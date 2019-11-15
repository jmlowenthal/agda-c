module Streams where

open import C
open C.C ⦃ ... ⦄

open import Data.Unit using (⊤)
open import Data.Integer using (ℤ) renaming (+_ to int)
open import Data.Nat using (ℕ) renaming (_<_ to _<ₙ_ ; _≤_ to _≤ₙ_ ; _∸_ to _-ₙ_)
open import Data.Product using (_×_ ; _,_)
open import Data.Vec using (Vec; _∷_; [])
open import Data.Nat.Properties

-- Stream Fusion, to Completeness ----------------------------------------

data CardT : Set where
  atMost1 : CardT
  many : CardT

-- ProducerT (element type) (internal state) ⦃ implementation ⦄
data ProducerT (α σ : Set) ⦃ _ : C ⦄ : Set where
  -- for : (state → index) × (state → index → continuation → void)
  for : (σ → Code Int) × (σ → Code Int → (α → Code Void) → Code Void) → ProducerT α σ
  -- unfolder : (state → terminated?) × cardinality × (state → continuation → void)
  unfolder : (σ → Code Bool) × CardT × (σ → (α → Code Void) → Code Void) → ProducerT α σ

-- Producer (element type) ⦃ implementation ⦄
data Producer (α : Set) ⦃ _ : C ⦄ : Set₁ where
  -- producer : ⦃ internal state ⦄ → (initialisation function) × producer
  producer : ∀ { σ } → (∀ { ω } → (σ → Code ω) → Code ω) × (ProducerT α σ) → Producer α

-- Stream (element type) ⦃ implementation ⦄
data SStream (α : Set) ⦃ _ : C ⦄ : Set₁ where
  -- linear : producer of code elements
  linear : Producer α → SStream α
  -- nested : ⦃ stream code ⦄ → (producer of stream code) × (stream code → stream)
  nested : ∀ { β } → Producer β × (β → SStream α) → SStream α

Stream : ∀ ⦃ _ : C ⦄ → c_type → Set₁
Stream α = SStream (Code α)

forUnfold : ∀ ⦃ _ : C ⦄ → ∀ { α } → Producer α → Producer α
forUnfold { α } (producer { σ = σ } (init , for (bound , index))) =
  let init' : ∀ { ω } → ((Ref Int × σ) → Code ω) → Code ω
      init' k = init (λ s0 → decl Int λ i → i ≔ ⟨ int 0 ⟩ ； k (i , s0))
      term : (Ref Int × σ) → Code Bool
      term pair = (let i , s0 = pair in (★ i) <= bound s0)
      step : (Ref Int × σ) →  (α → Code Void) → Code Void
      step pair k =
        let i , s0 = pair in
          index s0 (★ i) (λ a → i ≔ (★ i) + ⟨ int 1 ⟩ ； k a)
  in
    producer (init' , unfolder (term , many , step))
forUnfold (producer (init , unfolder x)) =
  producer (init , unfolder x)

ofArrRaw : ∀ ⦃ _ : C ⦄ → ∀ { α n m } → {m≤n : m ≤ₙ n} → Ref (Array α n) → Vec (Code α) m → Code Void
ofArrRaw _ Vec.[] = nop
ofArrRaw {n = n} {m≤n = 1≤n} x (h ∷ []) =
  x [ ⟨ int (n -ₙ 1) ⟩ ] ≔ h
ofArrRaw {n = n} {m = ℕ.suc (ℕ.suc m)} {m≤n = m+2≤n} x (h₁ ∷ h₂ ∷ t) =
  x [ ⟨ int (n -ₙ (ℕ.suc m)) ⟩ ] ≔ h₁ ；
  ofArrRaw {m≤n = ≤-trans (n≤1+n (ℕ.suc m)) m+2≤n} x (h₂ ∷ t)

ofArr : ∀ ⦃ _ : C ⦄ → ∀ { α n } → Vec (Code α) n → Stream α
ofArr { α } { n } vec =
  let init : ∀ { ω } → (Ref (Array α n) → Code ω) → Code ω
      init k = decl (Array α n) λ x → ofArrRaw {m≤n = ≤-refl} x vec ； k x
      upb : ∀ { m } → Ref (Array α m) → Code Int
      upb { m } _ = ⟨ int m ⟩
      index : ∀ { m } → Ref (Array α m) → Code Int → (Code α → Code Void) → Code Void
      index arr i k = decl α λ el → el ≔ ★ (arr [ i ]) ； k (★ el) -- TODO: requires i ∈ n
  in
    linear (producer (init , for (upb , index)))

-- TODO: C optionals / limited C structs
unfold : ∀ ⦃ _ : C ⦄ → ∀ { α ζ }
  → (Code ζ → Code Bool × Code α × Code ζ) → Code ζ → Stream α
unfold { α } { ζ } f x =
  let init : ∀ { ω } → (Code Bool × Code α × Code ζ → Code ω) → Code ω
      init k = k (f x)
      term : Code Bool × Code α × Code ζ → Code Bool
      term tuple = (let b , _ = tuple in b)
      step : Code Bool × Code α × Code ζ → (Code α → Code Void) → Code Void
      step s body = 
        let b , a , z = s in
        let b' , a' , z' = f z in
          if b then
            body a'
          else nop
  in
    linear (
      producer ((init , unfolder (term , many , step)))
    )

{-# TERMINATING #-} -- TODO: coinduction
foldRaw : ∀ ⦃ _ : C ⦄ → ∀ { α } → (α → Code Void) → SStream α → Code Void
foldRaw consumer (linear (producer (init , for (bound , index)))) = 
  init (λ sp → for ⟨ int 0 ⟩ to bound sp then λ i → index sp (★ i) consumer)
foldRaw consumer (linear (producer (init , unfolder (term , atMost1 , step)))) =
  init λ sp → if term sp then step sp consumer ； nop  else nop
foldRaw consumer (linear (producer (init , unfolder (term , many , step)))) =
  init λ sp → while term sp then step sp consumer
foldRaw consumer (nested (prod , f)) =
  foldRaw (λ e → foldRaw consumer (f e)) (linear prod)

fold : ∀ ⦃ _ : C ⦄ → ∀ { α ζ } → (Code ζ → Code α → Code ζ) → Code ζ → Stream α → Code ζ
fold { ζ = ζ } f z s =
  decl ζ λ acc →
  acc ≔ z ；
  foldRaw (λ a → acc ≔ f (★ acc) a) s ；
  ★ acc

mapRaw : ∀ ⦃ _ : C ⦄ → ∀ { α β } → (α → (β → Code Void) → Code Void)
  → SStream α → SStream β
mapRaw tr (linear (producer (init , for (bound , index)))) =
  let index' s i k = index s i (λ e → tr e k) in
    linear (producer (init , for (bound , index')))
mapRaw tr (linear (producer (init , unfolder (term , card , step)))) =
  let step' s k = step s (λ e → tr e k) in
    linear (producer (init , unfolder (term , card , step')))
mapRaw tr (nested (p , f)) = nested (p , (λ a → mapRaw tr (f a)))

map : ∀ ⦃ _ : C ⦄ → ∀ { α β } → (Code α → Code β) → Stream α → Stream β
map { β = β } f =
  mapRaw (λ a k →
    decl β λ t →
    t ≔ f a ；
    k (★ t)
  )

flatmap : ∀ ⦃ _ : C ⦄ → ∀ { α β } → (α → SStream β) → SStream α → SStream β
flatmap {α = α} f (linear x) = nested (x , f)
flatmap f (nested (x , g)) = nested (x , λ a → flatmap f (g a))

filter : ∀ ⦃ _ : C ⦄ → ∀ { α : c_type } → (Code α → Code Bool) → Stream α → Stream α
filter { α = α } f = flatmap (
  λ x → linear (
    producer (
      (λ k → k x)
      , unfolder (f , atMost1 , λ a k → k a)
    )
  ))

{-# TERMINATING #-} -- TODO
addToProducer : ∀ ⦃ _ : C ⦄ → ∀ { α } → Code Bool → Producer α → Producer α
addToProducer new (producer (init , unfolder (term , many , step))) =
  producer ((init , unfolder ((λ s → new && term s) , many , step)))
addToProducer new (producer (init , unfolder (term , atMost1 , step))) =
  producer (init , unfolder (term , atMost1 , step))
addToProducer new (producer (init , for x)) =
  addToProducer new (forUnfold (producer (init , for x)))

moreTermination : ∀ ⦃ _ : C ⦄ → ∀ { α } → Code Bool → SStream α → SStream α
moreTermination new (linear p) = linear (addToProducer new p)
moreTermination new (nested (p , f)) =
  nested (addToProducer new p , λ a → moreTermination new (f a))

addNr : ∀ ⦃ _ : C ⦄ → ∀ { α } → Code Int → (p : Producer α) → Producer (Ref Int × α)
addNr n (producer { σ = σ } (init , unfolder (term , card , step))) =
  let init' : ∀ { ω } → (Ref Int × σ → Code ω) → Code ω
      init' k = init (λ s → decl Int λ nr → k (nr , s))
      term' : CardT → Ref Int × σ → Code Bool
      term' = λ { many (nr , s) → (★ nr) == ⟨ int 0 ⟩ && term s
                ; atMost1 (nr , s) → term s }
      step' nrs k =
        let nr , s = nrs in
          step s (λ el → k (nr , el))
  in
    producer (init' , unfolder (term' card , card , step'))
addNr _ (producer (_ , for _)) =
  producer ((λ k → k ⊤.tt) , for ((λ _ → ⟨ int 0 ⟩) , (λ _ _ _ → nop)))

take : ∀ ⦃ _ : C ⦄ → Code Int → ∀ { α } → SStream α → SStream α
take n (linear (producer (init , for (bound , index)))) =
  linear (producer (
    init , for ((λ s → if (n - ⟨ int 1 ⟩) < bound s then n - ⟨ int 1 ⟩ else bound s) , index))
  )
take n (linear (producer (init , unfolder x))) =
  mapRaw
    (λ nrel k → let nr , el = nrel in nr ≔ ★ nr - ⟨ int 1 ⟩ ； k el)
    (linear (addNr n (producer (init , unfolder x))))
take n (nested { β = α } (p , f)) =
  nested (
    addNr n (forUnfold p) ,
    λ nra →
      let nr , a = nra in
        mapRaw
          (λ el k → nr ≔ ★ nr - ⟨ int 1 ⟩ ； k el)
          (moreTermination ((★ nr) == ⟨ int 0 ⟩) (f a))
  )

-- TODO: drop
-- TODO: zip or zipWith?

iota : ∀ ⦃ _ : C ⦄ → ℕ → Stream Int
iota n = unfold (λ n → true , n , n + ⟨ int 1 ⟩) ⟨ int n ⟩

_▹_ : ∀ ⦃ _ : C ⦄ → ∀ { α } → ∀ { β : Set } → Stream α → (Stream α → β) → β
x ▹ f = f x 

