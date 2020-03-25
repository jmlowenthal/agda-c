module Streams.Base where

open import C
open C.C ⦃ ... ⦄

open import Data.Unit using (⊤)
open import Data.Integer using (ℤ) renaming (+_ to int)
open import Data.Nat using (ℕ) renaming (_<_ to _<ₙ_ ; _≤_ to _≤ₙ_ ; _∸_ to _-ₙ_ ; _+_ to _+ₙ_)
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
  -- unfolder : (state → continue?) × cardinality × (state → continuation → void)
  unfolder : (σ → Ref Bool → Statement) × CardT × (σ → (α → Statement) → Statement) → ProducerT α σ

-- Producer (element type) ⦃ implementation ⦄
data Producer (α : Set) ⦃ _ : C ⦄ : Set₁ where
  -- producer : ⦃ internal state ⦄ → (initialisation function) × producer
  producer : ∀ { σ } → ((σ → Statement) → Statement) × (ProducerT α σ) → Producer α

-- Stream (element type) ⦃ implementation ⦄
data SStream ⦃ _ : C ⦄ : Set → Set₁ where
  -- linear : producer of code elements
  linear : ∀ { α } → Producer α → SStream α
  -- nested : (producer of stream code) × (stream code → stream)
  nested : ∀ { α β } → Producer β × (β → SStream α) → SStream α

Stream : ∀ ⦃ _ : C ⦄ → c_type → Set₁
Stream α = SStream (Expr α)

-- Show that the SStream is always getting 'smaller', for termination checking
∥_∥ₛ : ∀ ⦃ _ : C ⦄ { α } → SStream α → ℕ
∥ linear _ ∥ₛ = 0
∥ nested _ ∥ₛ = 1

-- Show that the Producer is always getting 'smaller', for termination checking
∥_∥ₚ : ∀ ⦃ _ : C ⦄ { α } → Producer α → ℕ
∥ producer (_ , unfolder _) ∥ₚ = 0
∥ producer (_ , for _) ∥ₚ = 1

forUnfold : ∀ ⦃ _ : C ⦄ { α } → Producer α → Producer α
forUnfold { α } (producer { σ = σ } (init , for (bound , index))) =
  producer (init' , unfolder (term , many , step))
  where
    init' : ((Ref Int × σ) → Statement) → Statement
    init' k =
      init (λ s0 →
        decl Int λ i →
        i ≔ ⟪ int 0 ⟫ ；
        k (i , s0))
    term : (Ref Int × σ) → Ref Bool → Statement
    term (i , s0) ref =
      decl Int λ x →
      x ← bound s0 ；
      ref ≔ (★ i) <= (★ x)
    step : (Ref Int × σ) →  (α → Statement) → Statement
    step (i , s0) k =
      index s0 (★ i) (λ a → i ≔ (★ i) + ⟪ int 1 ⟫ ； k a)
forUnfold (producer (init , unfolder x)) =
  producer (init , unfolder x)

forUnfold-size : ∀ ⦃ _ : C ⦄ { α } (p : Producer α) → ∥ forUnfold p ∥ₚ ≡ 0
forUnfold-size (producer (_ , for _)) = refl
forUnfold-size (producer (_ , unfolder _)) = refl

ofArrRaw : ∀ ⦃ _ : C ⦄ → ∀ { α n m } → {m≤n : m ≤ₙ n} → Ref (Array α n) → Vec (Expr α) m → Statement
ofArrRaw _ Vec.[] = nop
ofArrRaw {n = n} {m≤n = 1≤n} x (h ∷ []) =
  x [ ⟪ int (n -ₙ 1) ⟫ ] ≔ h
ofArrRaw {n = n} {m = ℕ.suc (ℕ.suc m)} {m≤n = m+2≤n} x (h₁ ∷ h₂ ∷ t) =
  x [ ⟪ int (n -ₙ (ℕ.suc m) -ₙ 1) ⟫ ] ≔ h₁ ；
  ofArrRaw {m≤n = ≤-trans (n≤1+n (ℕ.suc m)) m+2≤n} x (h₂ ∷ t)

ofArr : ∀ ⦃ _ : C ⦄ → ∀ { α n } → Vec (Expr α) n → Stream α
ofArr { α } { n } vec =
  let init : (Ref (Array α n) → Statement) → Statement
      init k =
        decl (Array α n) λ x →
        ofArrRaw {m≤n = ≤-refl} x vec ；
        k x
      upb : ∀ { m } → Ref (Array α m) → Ref Int → Statement
      upb { m } _ ref =
        ref ≔ ⟪ int (m -ₙ 1) ⟫
      index : ∀ { m } → Ref (Array α m) → Expr Int → (Expr α → Statement) → Statement
      index arr i k =
        decl α λ el →
        el ≔ ★ (arr [ i ]) ；
        k (★ el) -- TODO: requires i ∈ n
  in
    linear (producer (init , for (upb , index)))

-- unfold ≡ λ f z → Functor.fmap f (Applicative.pure z)
unfold : ∀ ⦃ _ : C ⦄ → ∀ { α ζ }
  → (Expr ζ → (Expr Bool × Expr α × Expr ζ)) → Expr ζ → Stream α
unfold { α } { ζ } f x =
  linear (producer ((init , unfolder (term , many , step))))
  where
    init : (Ref Bool × Ref α × Ref ζ → Statement) → Statement
    init k =
      let b , a , z = f x in
        decl Bool λ u → u ≔ b ；
        decl α λ v → v ≔ a ；
        decl ζ λ w → w ≔ z ；
        k (u , v , w)
    term : Ref Bool × Ref α × Ref ζ → Ref Bool → Statement
    term (b , _) r = r ≔ ★ b
    step : Ref Bool × Ref α × Ref ζ → (Expr α → Statement) → Statement
    step (b , a , z) body =
      let b' , a' , z' = f (★ z) in
        body (★ a) ；
        b ≔ b' ；
        a ≔ a' ；
        z ≔ z'

iterRaw : ∀ ⦃ _ : C ⦄ { α } → (α → Statement) → (x : SStream α)
  → {n : ℕ} { _ : n ≡ ∥ x ∥ₛ } → Statement
iterRaw consumer (linear (producer (init , for (bound , index)))) = 
  init (λ sp →
    decl Int λ l →
    l ← bound sp ；
    for ⟪ int 0 ⟫ to ★ l then λ i →
      index sp (★ i) consumer)
iterRaw consumer (linear (producer (init , unfolder (term , atMost1 , step)))) =
  init λ sp →
    decl Bool λ cond →
    cond ← term sp ；
    if ★ cond then step sp consumer else nop
iterRaw consumer (linear (producer (init , unfolder (term , many , step)))) =
  init λ sp →
    decl Bool λ cond →
    cond ← term sp ；
    while ★ cond then (
      step sp consumer ；
      cond ← term sp
    )
iterRaw consumer (nested (prod , f)) {1} =
  iterRaw (λ e → iterRaw consumer (f e) {∥ f e ∥ₛ} {refl}) (linear prod) {0} {refl}

iter : ∀ ⦃ _ : C ⦄ { α } → (α → Statement) → SStream α → Statement
iter f s = iterRaw f s {∥ s ∥ₛ} {refl}

fold : ∀ ⦃ _ : C ⦄ { α ζ } → (Expr ζ → α → Expr ζ) → Expr ζ → SStream α → (Ref ζ → Statement)
fold f z s acc =
  acc ≔ z ；
  iter (λ a → acc ≔ f (★ acc) a) s

mapRaw : ∀ ⦃ _ : C ⦄ → ∀ { α β } → (α → (β → Statement) → Statement)
  → SStream α → SStream β
mapRaw tr (linear (producer (init , for (bound , index)))) =
  let index' s i k = index s i (λ e → tr e k) in
    linear (producer (init , for (bound , index')))
mapRaw tr (linear (producer (init , unfolder (term , card , step)))) =
  let step' s k = step s (λ e → tr e k) in
    linear (producer (init , unfolder (term , card , step')))
mapRaw tr (nested (p , f)) = nested (p , (λ a → mapRaw tr (f a)))

-- map ≡ Functor.fmap
map : ∀ ⦃ _ : C ⦄ → ∀ { α β } → (α → Expr β) → SStream α → Stream β
map { β = β } f =
  mapRaw (λ a k →
    decl β λ t →
    t ≔ f a ；
    k (★ t)
  )

-- Inefficient, but more general and ≅-equivalent
map' : ∀ ⦃ _ : C ⦄ { α β } → (α → β) → SStream α → SStream β
map' f = mapRaw (λ a k → k (f a))

-- flatmap ≡ λ f x → x Monad.>>= f
flatmap : ∀ ⦃ _ : C ⦄ → ∀ { α β } → (α → SStream β) → SStream α → SStream β
flatmap {α = α} f (linear x) = nested (x , f) -- TODO: can we eliminate this case when α is Bool or other prim type
flatmap f (nested (x , g)) = nested (x , λ a → flatmap f (g a))

filter : ∀ ⦃ _ : C ⦄ { α } → (α → Expr Bool) → SStream α → SStream α
filter f = flatmap (
  λ x → linear (producer ((λ k → k x) , unfolder ((λ a r → r ≔ f a) , atMost1 , λ a k → k a))))

addToProducerRaw : ∀ ⦃ _ : C ⦄ { α } → (Ref Bool → Statement) → (p : Producer α)
  → { n : ℕ } { _ : n ≡ ∥ p ∥ₚ } → Producer α
addToProducerRaw new (producer (init , unfolder (term , many , step))) =
  producer (init , unfolder (term' , many , step))
  where
    term' : _ → Ref Bool → Statement
    term' s r =
      decl Bool λ a →
      a ← new ；
      decl Bool λ b →
      b ← term s ；
      r ≔ (★ a) && (★ b)
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
  producer (init' , unfolder (term' card , card , step'))
  where
    init' : (Ref Int × σ → Statement) → Statement
    init' k = init (λ s → decl Int λ nr → k (nr , s))
    term' : CardT → Ref Int × σ → Ref Bool → Statement
    term' many (nr , s) r =
      r ← term s ；
      r ≔ (★ r) && ((★ nr) == ⟪ int 0 ⟫)
    term' atMost1 (nr , s) = term s
    step' : Ref Int × σ → (Ref Int × _ → Statement) → Statement
    step' (nr , s) k = step s (λ el → k (nr , el))
addNr _ (producer (_ , for _)) =
  producer ((λ k → k ⊤.tt) , for ((λ _ r → r ≔ ⟪ int 0 ⟫) , (λ _ _ _ → nop)))

take : ∀ ⦃ _ : C ⦄ → Expr Int → ∀ { α } → SStream α → SStream α
take n (linear (producer (init , for (bound , index)))) =
  linear (producer (
    init , for (
      (λ s r →
        decl Int λ b →
        b ← bound s ；
        if ((n - ⟪ int 1 ⟫) < (★ b)) then
          r ≔ n - ⟪ int 1 ⟫
        else
          r ≔ ★ b
      )
      , index)
    )
  )
take n (linear (producer (init , unfolder x))) =
  mapRaw
    (λ nrel k → let nr , el = nrel in nr ≔ ★ nr - ⟪ int 1 ⟫ ； k el)
    (linear (addNr n (producer (init , unfolder x))))
take n (nested { β = α } (p , f)) =
  nested (
    addNr n (forUnfold p) ,
    λ nra →
      let nr , a = nra in
        mapRaw
          (λ el k → nr ≔ ★ nr - ⟪ int 1 ⟫ ； k el)
          (moreTermination (λ r → r ≔ (★ nr) == ⟪ int 0 ⟫) (f a))
  )

-- TODO: drop

zipProducer : ∀ ⦃ _ : C ⦄ { α β } → (a : Producer α) → (b : Producer β)
  → { n : ℕ } { _ : n ≡ ∥ a ∥ₚ } { m : ℕ } { _ : m ≡ ∥ b ∥ₚ }
  → Producer (α × β)
zipProducer {α} {β} (producer {σ₁} (i₁ , for (b₁ , x₁))) (producer {σ₂} (i₂ , for (b₂ , x₂))) =
  producer (i , for (b , x))
  where
    i : (σ₁ × σ₂ → Statement) → Statement
    i k = i₁ (λ a → i₂ (λ b → k (a , b)))
    b : σ₁ × σ₂ → Ref Int → Statement
    b (a , b) r =
      decl Int λ x →
      decl Int λ y →
      x ← b₁ a ；
      y ← b₂ b ；
      if (★ x) < (★ y) then
        r ≔ ★ x
      else
        r ≔ ★ y
    x : σ₁ × σ₂ → Expr Int → (α × β → Statement) → Statement
    x (a , b) i k = x₁ a i (λ n → x₂ b i (λ m → k (n , m)))
zipProducer {α} {β} (producer {σ₁} (i₁ , unfolder (t₁ , c₁ , s₁))) (producer {σ₂} (i₂ , unfolder (t₂ , c₂ , s₂))) =
  producer (i , unfolder (t , many , s))
  where
    i : (σ₁ × σ₂ → Statement) → Statement
    i k = i₁ (λ a → i₂ (λ b → k (a , b)))
    t : σ₁ × σ₂ → Ref Bool → Statement
    t (a , b) r =
      decl Bool λ x →
      decl Bool λ y →
      x ← t₁ a ；
      r ← t₂ b ；
      r ≔ (★ x) && (★ y)
    s : σ₁ × σ₂ → (α × β → Statement) → Statement
    s (a , b) k = s₁ a (λ x → s₂ b (λ y → k (x , y)))
zipProducer a@(producer (_ , for _)) b@(producer (_ , unfolder _)) {n = 1} {refl} {0} {refl} =
  zipProducer (forUnfold a) b {n = 0} {refl} {0} {refl}
zipProducer a@(producer (_ , unfolder _)) b@(producer (_ , for _)) {n = 0} {refl} {1} {refl} =
  zipProducer a (forUnfold b) {n = 0} {refl} {0} {refl}

pushLinear : ∀ ⦃ _ : C ⦄ { α β γ }
  → (p : Producer α) (q : Producer β) {_ : ∥ p ∥ₚ ≡ 0} {_ : ∥ q ∥ₚ ≡ 0}
  → (β → SStream γ) → SStream (α × γ)
pushLinear {α} {β} {γ} (producer {σ₁} (init₁ , unfolder (term₁ , _ , step₁))) (producer {σ₂} (init₂ , unfolder (term₂ , _ , step₂))) f =
  nested (producer (init , unfolder (term , many , step)) , g)
  where
    init : (Ref Bool × σ₁ × σ₂ → Statement) → Statement
    init k =
      init₁ (λ s₁ →
        init₂ (λ s₂ →
          decl Bool λ r →
          r ← term₁ s₁ ；
          k (r , s₁ , s₂)))
    term : Ref Bool × σ₁ × σ₂ → Ref Bool → Statement
    term (b , s₁ , s₂) r =
      r ← term₂ s₂ ；
      r ≔ (★ r) && (★ b)
    step : Ref Bool × σ₁ × σ₂ → (Ref Bool × σ₁ × β → Statement) → Statement
    step (r , s₁ , s₂) k = step₂ s₂ (λ b → k (r , s₁ , b))
    g : Ref Bool × σ₁ × β → SStream (α × γ)
    g (r , s₁ , b) =
      mapRaw
        (λ c k → step₁ s₁ (λ a → r ← term₁ s₁ ； k (a , c)))
        (moreTermination (λ x → x ≔ ★ r) (f b))

-- Prohibt zip of two nested streams
zip : ∀ ⦃ _ : C ⦄ { α β } (x : SStream α) (y : SStream β) { _ : ∥ x ∥ₛ +ₙ ∥ y ∥ₛ ≤ₙ 1 }
  → SStream (α × β)
zip (linear p) (linear q) {_≤ₙ_.z≤n} =
  linear (zipProducer p q {_} {refl} {_} {refl})
zip (linear p) (nested (q , f)) {_≤ₙ_.s≤s _≤ₙ_.z≤n} =
  pushLinear (forUnfold p) (forUnfold q) {forUnfold-size p} {forUnfold-size q} f
zip (nested (p , f)) (linear q) {_≤ₙ_.s≤s _≤ₙ_.z≤n} =
  mapRaw
    (λ { (y , x) k → k (x , y) })
    (pushLinear (forUnfold q) (forUnfold p) {forUnfold-size q} {forUnfold-size p} f)

zipWith : ∀ ⦃ _ : C ⦄ { α β γ } → (α → β → γ)
  → (x : SStream α) (y : SStream β) { _ : ∥ x ∥ₛ +ₙ ∥ y ∥ₛ ≤ₙ 1 } → SStream γ
zipWith f a b {p} = mapRaw (λ { (x , y) k → k (f x y) }) (zip a b {p})

nil : ∀ ⦃ _ : C ⦄ → ∀ { α } → SStream α
nil = linear (producer { σ = ⊤ } ((λ x → x ⊤.tt) , for ((λ _ _ → nop) , λ _ _ _ → nop)))

-- iota n
-- The infinite stream of natural numbers starting at n
iota : ∀ ⦃ _ : C ⦄ → ℕ → Stream Int
iota n = unfold (λ n → (true , n , n + ⟪ int 1 ⟫)) ⟪ int n ⟫

-- nat n
-- The stream of natural numbers less than n
nat : ∀ ⦃ _ : C ⦄ → ℕ → Stream Int
nat n = unfold (λ x → (x < ⟪ int n ⟫ , x , x + ⟪ int 1 ⟫)) ⟪ int 0 ⟫

_▹_ : ∀ ⦃ _ : C ⦄ → ∀ { α n } → ∀ { β : Set n } → Stream α → (Stream α → β) → β
x ▹ f = f x 
infixl 0 _▹_
