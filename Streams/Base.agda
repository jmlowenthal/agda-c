module Streams.Base where

open import C
open C.C ⦃ ... ⦄

open import Data.Unit using (⊤)
open import Data.Integer using (ℤ) renaming (+_ to int)
open import Data.Nat using (ℕ) renaming (_<_ to _<ₙ_ ; _≤_ to _≤ₙ_ ; _∸_ to _-ₙ_)
open import Data.Product using (_×_ ; _,_ ; ∃ ; proj₁ ; proj₂)
open import Data.Vec using (Vec; _∷_; [])
open import Data.Nat.Properties
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
import Induction.WellFounded as Wf
open import Function
import Level

-- Stream Fusion, to Completeness ----------------------------------------

data CardT : Set where
  atMost1 : CardT
  many : CardT

-- ProducerT (element type) (internal state) ⦃ implementation ⦄
data ProducerT (α σ : Set) ⦃ _ : C ⦄ : Set where
  -- for : (state → index) × (state → index → continuation → void)
  for : (σ → Ref Int → Statement) × (σ → Expr Int → (α → Statement) → Statement) → ProducerT α σ
  -- unfolder : (state → terminated?) × cardinality × (state → continuation → void)
  unfolder : (σ → Ref Bool → Statement) × CardT × (σ → (α → Statement) → Statement) → ProducerT α σ

-- Producer (element type) ⦃ implementation ⦄
data Producer (α : Set) ⦃ _ : C ⦄ : Set₁ where
  -- producer : ⦃ internal state ⦄ → (initialisation function) × producer
  producer : ∀ { σ } → ((σ → Statement) → Statement) × (ProducerT α σ) → Producer α

-- Stream (element type) ⦃ implementation ⦄
data SStream (α : Set) ⦃ _ : C ⦄ : Set₁ where
  -- linear : producer of code elements
  linear : Producer α → SStream α
  -- nested : ⦃ stream code ⦄ → (producer of stream code) × (stream code → stream)
  nested : ∀ { β } → Producer β × (β → SStream α) → SStream α

Stream : ∀ ⦃ _ : C ⦄ → c_type → Set₁
Stream α = SStream (Expr α)

forUnfold : ∀ ⦃ _ : C ⦄ → ∀ { α } → Producer α → Producer α
forUnfold { α } (producer { σ = σ } (init , for (bound , index))) =
  let init' : ((Ref Int × σ) → Statement) → Statement
      init' k = init (λ s0 → decl Int λ i → i ≔ ⟨ int 0 ⟩ ； k (i , s0))
      term : (Ref Int × σ) → Ref Bool → Statement
      term pair ref =
        (let i , s0 = pair in
          decl Int λ x →
          bound s0 x ；
          ref ≔ (★ i) <= (★ x))
      step : (Ref Int × σ) →  (α → Statement) → Statement
      step pair k =
        let i , s0 = pair in
          index s0 (★ i) (λ a → i ≔ (★ i) + ⟨ int 1 ⟩ ； k a)
  in
    producer (init' , unfolder (term , many , step))
forUnfold (producer (init , unfolder x)) =
  producer (init , unfolder x)

ofArrRaw : ∀ ⦃ _ : C ⦄ → ∀ { α n m } → {m≤n : m ≤ₙ n} → Ref (Array α n) → Vec (Expr α) m → Statement
ofArrRaw _ Vec.[] = nop
ofArrRaw {n = n} {m≤n = 1≤n} x (h ∷ []) =
  x [ ⟨ int (n -ₙ 1) ⟩ ] ≔ h
ofArrRaw {n = n} {m = ℕ.suc (ℕ.suc m)} {m≤n = m+2≤n} x (h₁ ∷ h₂ ∷ t) =
  x [ ⟨ int (n -ₙ (ℕ.suc m) -ₙ 1) ⟩ ] ≔ h₁ ；
  ofArrRaw {m≤n = ≤-trans (n≤1+n (ℕ.suc m)) m+2≤n} x (h₂ ∷ t)

ofArr : ∀ ⦃ _ : C ⦄ → ∀ { α n } → Vec (Expr α) n → Stream α
ofArr { α } { n } vec =
  let init : (Ref (Array α n) → Statement) → Statement
      init k = decl (Array α n) λ x → ofArrRaw {m≤n = ≤-refl} x vec ； k x
      upb : ∀ { m } → Ref (Array α m) → Ref Int → Statement
      upb { m } _ ref = ref ≔ ⟨ int (m -ₙ 1) ⟩
      index : ∀ { m } → Ref (Array α m) → Expr Int → (Expr α → Statement) → Statement
      index arr i k = decl α λ el → el ≔ ★ (arr [ i ]) ； k (★ el) -- TODO: requires i ∈ n
  in
    linear (producer (init , for (upb , index)))

-- TODO: C optionals / limited C structs
unfold : ∀ ⦃ _ : C ⦄ → ∀ { α ζ }
  → (Expr ζ → (Expr Bool × Expr α × Expr ζ)) → Expr ζ → Stream α
unfold { α } { ζ } f x =
  let init : (Ref Bool × Ref α × Ref ζ → Statement) → Statement
      init k =
        let b , a , z = f x in
          decl Bool λ u → u ≔ b ；
          decl α λ v → v ≔ a ；
          decl ζ λ w → w ≔ z ；
          k (u , v , w)
      term : Ref Bool × Ref α × Ref ζ → Ref Bool → Statement
      term tuple ref = (let b , _ = tuple in ref ≔ ★ b)
      step : Ref Bool × Ref α × Ref ζ → (Expr α → Statement) → Statement
      step s body = 
        let b , a , z = s in
        let b' , a' , z' = f (★ z) in
          body (★ a) ；
          b ≔ b' ；
          a ≔ a' ；
          z ≔ z'
  in
    linear (
      producer ((init , unfolder (term , many , step)))
    )

-- Show that the SStream is always getting 'smaller', for termination checking
∥_∥ₛ : ∀ ⦃ _ : C ⦄ { α } → SStream α → ℕ
∥ linear _ ∥ₛ = 0
∥ nested _ ∥ₛ = 1

foldRaw : ∀ ⦃ _ : C ⦄ { α } → (α → Statement) → (x : SStream α)
  → {n : ℕ} { _ : n ≡ ∥ x ∥ₛ } → Statement
foldRaw consumer (linear (producer (init , for (bound , index)))) = 
  init (λ sp →
    decl Int λ l →
    bound sp l ；
    for ⟨ int 0 ⟩ to ★ l then λ i → index sp (★ i) consumer)
foldRaw consumer (linear (producer (init , unfolder (term , atMost1 , step)))) =
  init λ sp →
    decl Bool λ cond →
    term sp cond ；
    if ★ cond then step sp consumer else nop
foldRaw consumer (linear (producer (init , unfolder (term , many , step)))) =
  init λ sp →
    decl Bool λ cond →
    term sp cond ；
    while ★ cond then
      step sp consumer ；
      term sp cond
foldRaw consumer (nested (prod , f)) {1} =
  foldRaw (λ e → foldRaw consumer (f e) {∥ f e ∥ₛ} {refl}) (linear prod) {0} {refl}

fold' : ∀ ⦃ _ : C ⦄ { α } → (α → Statement) → SStream α → Statement
fold' f s = foldRaw f s {∥ s ∥ₛ} {refl}

-- e.g. collectToList = fold (λ l a → a ∷ l) []
fold : ∀ ⦃ _ : C ⦄ → ∀ { α ζ } → (Expr ζ → Expr α → Expr ζ) → Expr ζ → Stream α → (Ref ζ → Statement)
fold { ζ = ζ } f z s acc =
  acc ≔ z ；
  fold' (λ a → acc ≔ f (★ acc) a) s

mapRaw : ∀ ⦃ _ : C ⦄ → ∀ { α β } → (α → (β → Statement) → Statement)
  → SStream α → SStream β
mapRaw tr (linear (producer (init , for (bound , index)))) =
  let index' s i k = index s i (λ e → tr e k) in
    linear (producer (init , for (bound , index')))
mapRaw tr (linear (producer (init , unfolder (term , card , step)))) =
  let step' s k = step s (λ e → tr e k) in
    linear (producer (init , unfolder (term , card , step')))
mapRaw tr (nested (p , f)) = nested (p , (λ a → mapRaw tr (f a)))

map : ∀ ⦃ _ : C ⦄ → ∀ { α β } → (Expr α → Expr β) → Stream α → Stream β
map { β = β } f =
  mapRaw (λ a k →
    decl β λ t →
    t ≔ f a ；
    k (★ t)
  )

flatmap : ∀ ⦃ _ : C ⦄ → ∀ { α β } → (α → SStream β) → SStream α → SStream β
flatmap {α = α} f (linear x) = nested (x , f)
flatmap f (nested (x , g)) = nested (x , λ a → flatmap f (g a))

filter : ∀ ⦃ _ : C ⦄ → ∀ { α : c_type } → (Expr α → Expr Bool) → Stream α → Stream α
filter { α = α } f = flatmap (
  λ x → linear (producer ((λ k → k x) , unfolder ((λ a r → r ≔ f a) , atMost1 , λ a k → k a))))

-- Show that the Producer is always getting 'smaller', for termination checking
∥_∥ₚ : ∀ ⦃ _ : C ⦄ { α } → Producer α → ℕ
∥ producer (_ , unfolder _) ∥ₚ = 0
∥ producer (_ , for _) ∥ₚ = 1

addToProducerRaw : ∀ ⦃ _ : C ⦄ { α } → (Ref Bool → Statement) → (p : Producer α)
  → { n : ℕ } { _ : n ≡ ∥ p ∥ₚ } → Producer α
addToProducerRaw new (producer (init , unfolder (term , many , step))) =
  producer ((init , unfolder (
    (λ s r →
      decl Bool λ a →
      new a ；
      decl Bool λ b →
      term s b ；
      r ≔ (★ a) && (★ b))
    , many , step)))
addToProducerRaw new (producer (init , unfolder (term , atMost1 , step))) =
  producer (init , unfolder (term , atMost1 , step))
addToProducerRaw new (producer (init , for x)) {1} =
  addToProducerRaw new (forUnfold (producer (init , for x))) {0} {refl}

addToProducer : ∀ ⦃ _ : C ⦄ → ∀ { α } → (Ref Bool → Statement) → Producer α → Producer α
addToProducer new p = addToProducerRaw new p {∥ p ∥ₚ} {refl}

moreTermination : ∀ ⦃ _ : C ⦄ → ∀ { α } → (Ref Bool → Statement) → SStream α → SStream α
moreTermination new (linear p) = linear (addToProducer new p)
moreTermination new (nested (p , f)) =
  nested (addToProducer new p , λ a → moreTermination new (f a))

addNr : ∀ ⦃ _ : C ⦄ → ∀ { α } → Expr Int → (p : Producer α) → Producer (Ref Int × α)
addNr n (producer { σ = σ } (init , unfolder (term , card , step))) =
  let init' : (Ref Int × σ → Statement) → Statement
      init' k = init (λ s → decl Int λ nr → k (nr , s))
      term' : CardT → Ref Int × σ → Ref Bool → Statement
      term' = λ { many (nr , s) → λ r → term s r ； r ≔ (★ r) && ((★ nr) == ⟨ int 0 ⟩)
                ; atMost1 (nr , s) → term s }
      step' nrs k =
        let nr , s = nrs in
          step s (λ el → k (nr , el))
  in
    producer (init' , unfolder (term' card , card , step'))
addNr _ (producer (_ , for _)) =
  producer ((λ k → k ⊤.tt) , for ((λ _ r → r ≔ ⟨ int 0 ⟩) , (λ _ _ _ → nop)))

take : ∀ ⦃ _ : C ⦄ → Expr Int → ∀ { α } → SStream α → SStream α
take n (linear (producer (init , for (bound , index)))) =
  linear (producer (
    init , for (
      (λ s r →
        decl Int λ b →
        bound s b ；
        if ((n - ⟨ int 1 ⟩) < (★ b)) then
          r ≔ n - ⟨ int 1 ⟩
        else
          r ≔ ★ b
      )
      , index)
    )
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
          (moreTermination (λ r → r ≔ (★ nr) == ⟨ int 0 ⟩) (f a))
  )

-- TODO: drop
-- TODO: zip or zipWith?

nil : ∀ ⦃ _ : C ⦄ → ∀ { α } → Stream α
nil = linear (producer { σ = ⊤ } ((λ x → x ⊤.tt) , for ((λ _ _ → nop) , λ _ _ _ → nop)))

-- iota n
-- The infinite stream of natural numbers starting at n
iota : ∀ ⦃ _ : C ⦄ → ℕ → Stream Int
iota n = unfold (λ n → (true , n , n + ⟨ int 1 ⟩)) ⟨ int n ⟩

-- nat n
-- The stream of natural numbers less than n
nat : ∀ ⦃ _ : C ⦄ → ℕ → Stream Int
nat n = unfold (λ x → (x < ⟨ int n ⟩ , x , x + ⟨ int 1 ⟩)) ⟨ int 0 ⟩

_▹_ : ∀ ⦃ _ : C ⦄ → ∀ { α n } → ∀ { β : Set n } → Stream α → (Stream α → β) → β
x ▹ f = f x 
infixl 0 _▹_
