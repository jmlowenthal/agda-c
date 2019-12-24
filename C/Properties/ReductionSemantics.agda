-- Based in-part on "A formally verified compiler back-end" by Xavier Leroy

open import C.Base
open import Function
open import Relation.Binary
open import Level using (0ℓ)
open import Data.Product using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Algebra.FunctionProperties
open import Data.Unit
open import Data.Empty
open import Data.Sum
open import Data.Integer as ℤ using (ℤ ; +_)
import Data.Integer.Properties as ℤₚ
open import Relation.Nullary
open import Data.Bool as 𝔹 using () renaming (Bool to 𝔹)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Construct.Closure.Transitive
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Data.Vec

module C.Properties.ReductionSemantics ⦃ _ : C ⦄ where

open C.Base.C ⦃ ... ⦄

⟦_⟧ : c_type → Set
⟦ Int ⟧ = ℤ
⟦ Bool ⟧ = 𝔹
⟦ Array α n ⟧ = Vec ⟦ α ⟧ n

data Value : (α : c_type) → ⟦ α ⟧ → Set where
  val : ∀ { α } → (v : ⟦ α ⟧) → Value α v

data Env : Set where
  _↦_,_ : ∀ { α } → ∀ { v : ⟦ α ⟧ } → Ref α → Value α v → Env → Env
  _,_ : ∀ { α } → Ref α → Env → Env
  ε : Env

data _∈_ : ∀ { α } → Ref α → Env → Set where
  x∈x↦v,E : ∀ { α } { v : ⟦ α ⟧ } {x : Ref α} {E : Env}
    → x ∈ (x ↦ val v , E)
  x∈x,E : ∀ { α } { x : Ref α } { E : Env }
    → x ∈ (x , E)
  xα∈yβ↦w,E : ∀ { α β } { x : Ref α } { E : Env } { y : Ref β } { α≢β : α ≢ β } { w : ⟦ β ⟧ } { W : Value β w }
    → x ∈ E → x ∈ (y ↦ W , E)
  xα∈yβ,E : ∀ { α β } { x : Ref α } { E : Env } { y : Ref β } { α≢β : α ≢ β }
    → x ∈ E → x ∈ (y , E)
  xα∈yα↦w,E : ∀ { α } { x y : Ref α } { E : Env } { x≢y : x ≢ y } { w : ⟦ α ⟧ } { W : Value α w }
    → x ∈ E → x ∈ (y ↦ W , E)
  xα∈yα,E : ∀ { α } { x y : Ref α } { E : Env } { x≢y : x ≢ y }
    → x ∈ E → x ∈ (y , E)

data _↦_∈_ : ∀ { α } { v : ⟦ α ⟧ } → Ref α → Value α v → Env → Set where
  x↦v∈x↦v,E : ∀ { α } { v : ⟦ α ⟧ } {x : Ref α} {E : Env}
    → x ↦ val v ∈ (x ↦ val v , E)
  xα↦v∈yβ↦w,E :
    ∀ { α β } { x : Ref α } { E : Env } { y : Ref β } { α≢β : α ≢ β }
    { v : ⟦ α ⟧ } { w : ⟦ β ⟧ }
    → x ↦ val v ∈ E → x ↦ val v ∈ (y ↦ val w , E)
  xα↦v∈yβ,E : ∀ { α β } { x : Ref α } { E : Env } { y : Ref β } { α≢β : α ≢ β } { v : ⟦ α ⟧ }
    → x ↦ val v ∈ E → x ↦ val v ∈ (y , E)
  xα↦v∈yα↦w,E : ∀ { α } { x y : Ref α } { E : Env } { x≢y : x ≢ y } { w : ⟦ α ⟧ } { v : ⟦ α ⟧ }
    → x ↦ val v ∈ E → x ↦ val v ∈ (y ↦ val w , E)
  xα↦v∈yα,E : ∀ { α } { x y : Ref α } { E : Env } { x≢y : x ≢ y } { v : ⟦ α ⟧ }
    → x ↦ val v ∈ E → x ↦ val v ∈ (y , E)

-- _↦_∈_ : ∀ { α } { v : ⟦ α ⟧ } → (x : Ref α) → (V : Value α v) → (E : Env) → ∀ { _ : x ∈ E } → Set
-- (x ↦ val v ∈ _) {x∈x↦v,E {v = w}} = v ≡ w
-- (x ↦ val v ∈ _) {x∈x,E} = ⊥
-- (x ↦ val v ∈ (_ ↦ _ , E)) {xα∈yβ↦w,E x∈E} = (x ↦ val v ∈ E) {x∈E}
-- (x ↦ val v ∈ (_ , E)) {xα∈yβ,E x∈E} = (x ↦ val v ∈ E) {x∈E}
-- (x ↦ val v ∈ (_ ↦ _ , E)) {xα∈yα↦w,E x∈E} = (x ↦ val v ∈ E) {x∈E}
-- (x ↦ val v ∈ (_ , E)) {xα∈yα,E x∈E} = (x ↦ val v ∈ E) {x∈E}

_∉_ : ∀ { α } → Ref α → Env → Set
x ∉ E = ¬ (x ∈ E)

infixr 4 _⊕_
_⊕_ : Env → Env → Env
(x ↦ v , E₁) ⊕ E₂ = x ↦ v , (E₁ ⊕ E₂)
(x , E₁) ⊕ E₂ = x , (E₁ ⊕ E₂)
ε ⊕ E₂ = E₂

data Continuation : Set where
  stop : Continuation
  _then_ : Statement → Continuation → Continuation

data State : Set where
  𝒮 : Statement → Continuation → Env → State
  -- TODO: Side effects

Congruence : ∀ { a l } { A : Set a } → Rel A l → Set _
Congruence {A = A} _~_ = ∀ (f : A → A) x y → x ~ y → (f x) ~ (f y)

Clos : ∀ { n } → (Vec Set n) → Set → Set
Clos [] B = B
Clos (h ∷ t) B = h → Clos t B

lift : ∀ { n } { v : Vec Set n } { A : Set } { B : Set }
  → Clos v (A → B) → A → Clos v B
lift {v = []} clos = clos
lift {v = h ∷ t} clos a x = lift (clos x) a

Closure : ∀ { n } → (Vec Set n) → Set
Closure v = Clos v Statement

record Semantics : Set₁ where
  field
    _⊢_⇒_ : ∀ { α } → ∀ { v : ⟦ α ⟧ } → Env → Expr α → Value α v → Set
    ⊢-total : ∀ { α E } { e : Expr α } → ∃ λ v → (E ⊢ e ⇒ val v)
    ⊢-weakening : ∀ { E E' α β } { e : Expr α } { v : ⟦ α ⟧ } { x : Ref β } { w : ⟦ β ⟧ }
      → { _ : x ∉ E × x ∉ E' }
      → (E ⊕ E') ⊢ e ⇒ val v → (E ⊕ (x ↦ val w , ε) ⊕ E') ⊢ e ⇒ val v
    ⊢-exchange : ∀ { E E' α β γ } { x : Ref α } { y : Ref β }
      → { v : ⟦ α ⟧ } { w : ⟦ β ⟧ } { e : Expr γ } { ev : ⟦ γ ⟧ }
      → (E ⊕ (x ↦ val v , (y ↦ val w , ε)) ⊕ E') ⊢ e ⇒ val ev
      → (E ⊕ (y ↦ val w , (x ↦ val v , ε)) ⊕ E') ⊢ e ⇒ val ev
    -- TODO: variants on Env constructor
    nat : ∀ { E n } → E ⊢ ⟨ n ⟩ ⇒ val n
    deref : ∀ { E α } { x : Ref α } { v : ⟦ α ⟧ }
      → x ↦ val v ∈ E → (E ⊢ (★ x) ⇒ val v)
    +-eval : ∀ { E x y x' y' }
      → E ⊢ x ⇒ val x' → E ⊢ y ⇒ val y'
      → E ⊢ x + y ⇒ val (x' ℤ.+ y')
    *-eval : ∀ { E x y x' y' }
      → E ⊢ x ⇒ val x' → E ⊢ y ⇒ val y'
      → E ⊢ x * y ⇒ val (x' ℤ.* y')
    ∸-eval : ∀ { E x y x' y' }
      → E ⊢ x ⇒ val x' → E ⊢ y ⇒ val y'
      → E ⊢ x - y ⇒ val (x' ℤ.- y')
    -- /-eval : ∀ { E x y x' y' }
    --   → E ⊢ x ⇒ v-int x' → E ⊢ y ⇒ v-int y'
    --   → E ⊢ x / y ⇒ v-int (x' ℤ./ y')
    true-eval : ∀ { E } → E ⊢ true ⇒ val 𝔹.true
    false-eval : ∀ { E } → E ⊢ false ⇒ val 𝔹.false
    ||-eval : ∀ { E x y x' y' }
      → E ⊢ x ⇒ val x' → E ⊢ y ⇒ val y' → E ⊢ x || y ⇒ val (x' 𝔹.∨ y')
    &&-eval : ∀ { E x y x' y' }
      → E ⊢ x ⇒ val x' → E ⊢ y ⇒ val y' → E ⊢ x && y ⇒ val (x' 𝔹.∧ y')

    _↝_ : Rel State 0ℓ
    ↝-if-true : ∀ { E : Env } → ∀ { k : Continuation }
      → ∀ { cond : Expr Bool } → ∀ { s₁ s₂ : Statement }
      → E ⊢ cond ⇒ val 𝔹.true → 𝒮 (if cond then s₁ else s₂) k E ↝ 𝒮 s₁ k E
    ↝-if-false : ∀ { E : Env } → ∀ { k : Continuation }
      → ∀ { cond : Expr Bool } → ∀ { s₁ s₂ : Statement }
      → E ⊢ cond ⇒ val 𝔹.false → 𝒮 (if cond then s₁ else s₂) k E ↝ 𝒮 s₂ k E
    ↝-assignment : ∀ { E : Env } → ∀ { k : Continuation }
      → ∀ { α } → ∀ { id : Ref α } → ∀ { e : Expr α } → ∀ { e' : ⟦ α ⟧ } → ∀ { v : Value α e' }
      → E ⊢ e ⇒ v → 𝒮 (id ≔ e) k E ↝ 𝒮 nop k (id ↦ v , E)
    ↝-seq : ∀ { E : Env } → ∀ { k : Continuation }
      → ∀ { s₁ s₂ : Statement } → 𝒮 (s₁ ； s₂) k E ↝ 𝒮 s₁ (s₂ then k) E
    ↝-decl : ∀ { E : Env } → ∀ { k : Continuation }
      → ∀ { α } → ∀ { f : Ref α → Statement }
      → ∀ { x : Ref α } → ∀ { _ : ¬ (x ∈ E) }
      → 𝒮 (decl α f) k E ↝ 𝒮 (f x) k (x , E) 
    ↝-nop : ∀ { E : Env } → ∀ { k : Continuation } → ∀ { s : Statement }
      → 𝒮 nop (s then k) E ↝ 𝒮 s k E
    ↝-for : ∀ { E : Env } → ∀ { k : Continuation }
      → ∀ { l u : Expr Int } → ∀ { f : Ref Int → Statement }
      → 𝒮 (for l to u then f) k E
        ↝ 𝒮 (if (l < u) then (
                (decl Int λ i → i ≔ l ； f i) ；
                for (l + ⟨ + 1 ⟩) to u then f)
             else nop) k E
    ↝-while : ∀ { E : Env } → ∀ { k : Continuation }
      → ∀ { e : Expr Bool } → ∀ { s : Statement }
      → 𝒮 (while e then s) k E ↝ 𝒮 (if e then (s ； while e then s) else nop) k E
    ↝-det : ∀ { S S₁ S₂ } → S ↝ S₁ → S ↝ S₂ → S₁ ≡ S₂

  infix 0 _≅ₑ_
  _≅ₑ_ : ∀ { α } → Rel (Expr α) 0ℓ
  _≅ₑ_ { α } x y = ∀ { E : Env } → ∀ { v w : ⟦ α ⟧ }
    → (E ⊢ x ⇒ val v) → (E ⊢ y ⇒ val w) → (v ≡ w)

  _↝⁺_ : State → State → Set
  _↝⁺_ S₁ S₂ = S₁ ⟨ _↝_ ⟩⁺ S₂

  _↝*_ : State → State → Set
  _↝*_ = Star _↝_

  Stuck : State → Set
  Stuck S = ∀ S' → ¬ (S ↝ S')

  Terminating : State → Set
  Terminating S = ∃ λ S' → S ↝* S' × Stuck S'

  infix 0 _≅ₛ_
  _≅ₛ_ : Rel State 0ℓ
  X ≅ₛ Y = ∀ { S₁ S₂ : State }
    → (¬ Terminating X × ¬ Terminating Y)
      ⊎ (X ↝* S₁ → Y ↝* S₂ → Stuck S₁ → Stuck S₂ → S₁ ≡ S₂)

  field
    ≅ₑ-equiv : ∀ { α } → IsEquivalence (_≅ₑ_ { α })
    ≅ₛ-equiv : IsEquivalence _≅ₛ_
    ≅ₛ-subst : ∀ { α E₁ E₂ k } { v w : ⟦ α ⟧ } { f : Expr α → Statement } { e₁ e₂ : Expr α }
      → E₁ ⊢ e₁ ⇒ val v → E₂ ⊢ e₂ ⇒ val w → v ≡ w
      → 𝒮 (f e₁) k E₁ ≅ₛ 𝒮 (f e₂) k E₂
    ≅ₛ-cong : Congruence _≅ₛ_

open Semantics ⦃ ... ⦄

open ≡-Reasoning


-- VALUE JUDGEMENT LEMMAS

⊢-det : ∀ ⦃ _ : Semantics ⦄ { E α } { e : Expr α } { x y : ⟦ α ⟧ }
  → E ⊢ e ⇒ val x → E ⊢ e ⇒ val y → x ≡ y
⊢-det {E} {α} {e} {x} {y} ⇒x ⇒y = IsEquivalence.refl ≅ₑ-equiv {e} {E} {x} {y} ⇒x ⇒y

cong₃ : ∀ { a b c d : Level.Level } { A : Set a } { B : Set b } { C : Set c } { D : Set d }
  → ∀ (f : A → B → C → D) {x y u v a b}
  → x ≡ y → u ≡ v → a ≡ b → f x u a ≡ f y v b
cong₃ f refl refl refl = refl

⊢-cong : ∀ ⦃ _ : Semantics ⦄ { E₁ E₂ α } { e₁ e₂ : Expr α } { x : ⟦ α ⟧ } { v₁ v₂ : Value α x }
  → E₁ ≡ E₂ → e₁ ≡ e₂ → v₁ ≡ v₂ → E₁ ⊢ e₁ ⇒ v₁ ≡ E₂ ⊢ e₂ ⇒ v₂
⊢-cong = cong₃ _⊢_⇒_


-- EXPRESSION EQUIVALENCE

+-left-id : ∀ ⦃ _ : Semantics ⦄ → LeftIdentity _≅ₑ_ (⟨ + 0 ⟩) _+_
+-left-id e {E} {v} {w} 0+e⇒v e⇒w =
  let 0+e⇒0+w = +-eval (nat { n = + 0 }) e⇒w in
  let v≡0+w = ⊢-det 0+e⇒v 0+e⇒0+w in
  begin
    v
    ≡⟨ v≡0+w ⟩
    + 0 ℤ.+ w
    ≡⟨ ℤₚ.+-identityˡ w ⟩
    w
  ∎

+-right-id : ∀ ⦃ _ : Semantics ⦄ → RightIdentity _≅ₑ_ (⟨ + 0 ⟩) _+_
+-right-id e {E} {v} {w} e+0⇒v e⇒w =
  let e+0⇒w+0 = +-eval e⇒w (nat { n = + 0 }) in
  let v≡w+0 = ⊢-det e+0⇒v e+0⇒w+0 in
  begin
    v
    ≡⟨ v≡w+0 ⟩
    w ℤ.+ + 0
    ≡⟨ ℤₚ.+-identityʳ w ⟩
    w
  ∎

+-id : ∀ ⦃ _ : Semantics ⦄ → Identity _≅ₑ_ (⟨ + 0 ⟩) _+_
+-id = +-left-id , +-right-id

-- +-assoc : Associative _≅ₑ_ _+_
-- +-commute : Commutative _≅ₑ_ _+_
-- *-id : Identity _≅ₑ_ (⟨ + 1 ⟩) _*_
-- *-zero : Zero _≅ₑ_ (⟨ + 0 ⟩) _*_
-- *-assoc : Associative _≅ₑ_ _*_
-- *-commute : Commutative _≅ₑ_ _*_
-- ∸-id : Identity _≅ₑ_ (⟨ + 0 ⟩) _-_
-- /-id : Identity _≅ₑ_ (⟨ + 1 ⟩) _/_
-- -- TODO: algebra properties of _<_ _<=_ _>_ _>=_ _==_ using standard library algebra
-- <-trans : ∀ { x y z : Expr Int } → x < y ≅ₑ true → y < z ≅ₑ true → x < z ≅ₑ true
-- ||-id : Identity _≅ₑ_ false _||_
-- ||-zero : Zero _≅ₑ_ true _||_
-- ||-assoc : Associative _≅ₑ_ _||_
-- ||-commute : Commutative _≅ₑ_ _||_
-- &&-id : Identity _≅ₑ_ true _&&_
-- &&-zero : Zero _≅ₑ_ false _&&_
-- &&-assoc : Associative _≅ₑ_ _&&_
-- &&-commute : Commutative _≅ₑ_ _&&_ 


-- REDUCTION LEMMAS

↝*-trans : ∀ ⦃ _ : Semantics ⦄ → Transitive _↝*_
↝*-trans = _◅◅_

↝*-to-↝⁺ : ∀ ⦃ _ : Semantics ⦄ { A B C } → A ↝ B → B ↝* C → A ↝⁺ C
↝*-to-↝⁺ A↝B ε = Plus′.[ A↝B ]
↝*-to-↝⁺ A↝B (B↝X ◅ X↝*C) = A↝B ∷ (↝*-to-↝⁺ B↝X X↝*C)

↝⁺-to-↝* : ∀ ⦃ _ : Semantics ⦄ { A B } → A ↝⁺ B → A ↝* B
↝⁺-to-↝* Plus′.[ A↝B ] = A↝B ◅ ε
↝⁺-to-↝* (A↝X ∷ X↝⁺B) = A↝X ◅ (↝⁺-to-↝* X↝⁺B)

↝̸-transᵇ : ∀ ⦃ _ : Semantics ⦄ { S S' : State }
  → S ↝* S' → Terminating S' → Terminating S
↝̸-transᵇ {S} {S'} S↝*S' (X , S'↝*X , X↝̸) = X , (S↝*S' ◅◅ S'↝*X) , X↝̸

↝̸-transᶠ : ∀ ⦃ _ : Semantics ⦄ { S S' : State }
  → S ↝* S' → Terminating S → Terminating S'
↝̸-transᶠ ε S↝̸ = S↝̸
↝̸-transᶠ (S↝X ◅ X↝*S') (S , ε , S↝̸) = ⊥-elim (S↝̸ _ S↝X)
↝̸-transᶠ (S↝A ◅ A↝*S') (X , S↝Y ◅ Y↝*X , X↝̸)
  with ↝-det S↝A S↝Y
... | refl = ↝̸-transᶠ A↝*S' (X , Y↝*X , X↝̸)

↝ω-transᵇ : ∀ ⦃ _ : Semantics ⦄ { X Y : State }
  → X ↝* Y → ¬ Terminating Y → ¬ Terminating X
↝ω-transᵇ {X} {Y} X↝*Y Y↝ω X↝̸ = Y↝ω (↝̸-transᶠ X↝*Y X↝̸)

↝ω-transᶠ : ∀ ⦃ _ : Semantics ⦄ { X Y : State }
  → X ↝* Y → ¬ Terminating X → ¬ Terminating Y
↝ω-transᶠ {X} {Y} X↝*Y X↝ω Y↝̸ = X↝ω (↝̸-transᵇ X↝*Y Y↝̸)

↝*-det : ∀ ⦃ _ : Semantics ⦄ { S S₁ S₂ }
  → Stuck S₁ → Stuck S₂ → S ↝* S₁ → S ↝* S₂ → S₁ ≡ S₂
↝*-det S₁↝̸ S₂↝̸ ε ε = refl
↝*-det S↝̸ S₂↝̸ ε (_◅_ {j = X} S↝X X↝*S₂) = ⊥-elim (S↝̸ X S↝X)
↝*-det S₁↝̸ S↝̸ (_◅_ {j = X} S↝X X↝*S₂) ε = ⊥-elim (S↝̸ X S↝X)
↝*-det S₁↝̸ S₂↝̸ (S↝X ◅ X↝*S₁) (S↝Y ◅ Y↝*S₂)
  with ↝-det S↝X S↝Y
... | refl = ↝*-det S₁↝̸ S₂↝̸ X↝*S₁ Y↝*S₂

↝*-det' : ∀ ⦃ _ : Semantics ⦄ { S S₁ S₂ }
  → S ↝* S₁ → S ↝* S₂ → Stuck S₂ → S₁ ↝* S₂
↝*-det' ε S↝*S₂ _ = S↝*S₂
↝*-det' (S↝X ◅ X↝*S₁) ε S↝̸ = ⊥-elim (S↝̸ _ S↝X)
↝*-det' (S↝X ◅ X↝*S₁) (S↝Y ◅ Y↝*S₂) S₂↝̸
  with ↝-det S↝X S↝Y
... | refl = ↝*-det' X↝*S₁ Y↝*S₂ S₂↝̸


-- PROGRAM EQUIVALENCE

infix 0 _≅ₚ_
_≅ₚ_ : ∀ ⦃ _ : Semantics ⦄ { n } { v : Vec Set n } → Rel (Closure v) 0ℓ
_≅ₚ_ {v = []} x y = ∀ { k E } → 𝒮 x k E ≅ₛ 𝒮 y k E
_≅ₚ_ {v = h ∷ t} x y = {r : h} → _≅ₚ_ {v = t} (x r) (y r)

≅ₚ-refl : ∀ ⦃ _ : Semantics ⦄ { n } { v : Vec Set n } → Reflexive (_≅ₚ_ {v = v})
≅ₚ-refl {v = []} = IsEquivalence.refl ≅ₛ-equiv
≅ₚ-refl {v = x ∷ v} = ≅ₚ-refl {v = v}

≅ₚ-sym : ∀ ⦃ _ : Semantics ⦄ { n } { v : Vec Set n } → Symmetric (_≅ₚ_ {v = v})
≅ₚ-sym {v = []} i~j = IsEquivalence.sym ≅ₛ-equiv i~j
≅ₚ-sym {v = x ∷ v} i~j = ≅ₚ-sym {v = v} i~j

≅ₚ-trans : ∀ ⦃ _ : Semantics ⦄ { n } { v : Vec Set n } → Transitive (_≅ₚ_ {v = v})
≅ₚ-trans {v = []} i~j j~k = IsEquivalence.trans ≅ₛ-equiv i~j j~k
≅ₚ-trans {v = x ∷ v} i~j j~k = ≅ₚ-trans {v = v} i~j j~k

≅ₚ-equiv : ∀ ⦃ _ : Semantics ⦄ { n } { v : Vec Set n } → IsEquivalence (_≅ₚ_ {v = v})
≅ₚ-equiv = record { refl = ≅ₚ-refl ; sym = ≅ₚ-sym ; trans = ≅ₚ-trans }

postulate ≅ₚ-cong : ∀ ⦃ _ : Semantics ⦄ { n m } { v : Vec Set n } { w : Vec Set m } → ∀ ( f : Closure v → Closure w ) (x y : Closure v) → x ≅ₚ y → f x ≅ₚ f y

β-if-true' : ∀ ⦃ _ : Semantics ⦄ { x y : Statement } { k E S₁ S₂ }
  → 𝒮 (if true then x else y) k E ↝* S₁ → 𝒮 x k E ↝* S₂ → Stuck S₁ → Stuck S₂
  → S₁ ≡ S₂
β-if-true' {x} {_} {k} {E} ε _ S₁↝̸ _ = ⊥-elim (S₁↝̸ (𝒮 x k E) (↝-if-true true-eval))
β-if-true' {x} {y} {k} {E} (if↝R ◅ R↝*S₁) x↝*S₂ S₁↝̸ S₂↝̸
  with ↝-det if↝R (↝-if-true true-eval)
... | refl = ↝*-det S₁↝̸ S₂↝̸ R↝*S₁ x↝*S₂

β-if-true : ∀ ⦃ _ : Semantics ⦄ { x y : Statement }
  → (if true then x else y) ≅ₚ x
β-if-true = inj₂ β-if-true'

-- β-if-false : ⦃ _ : Equivalence ⦄ → ∀ { x y : Statement }
--   → if false then x else y ≡ y
-- β-if-false = {!!}

-- η-if : ⦃ _ : Equivalence ⦄ → ∀ { cond : Expr Bool } → ∀ { e : Statement }
--   → if cond then e else e ≡ e
-- η-if = {!!}

-- β-while : ⦃ _ : Equivalence ⦄ → ∀ { e₁ : Expr Bool } → ∀ { e₂ : Statement }
--   → while e₁ then e₂ ≡ if e₁ then (e₂ ； while e₁ then e₂) else nop

≔-subst : ∀ ⦃ _ : Semantics ⦄ { α } { x : Ref α } { e : Expr α } { f : Expr α → Statement }
  → (x ≔ e ； f (★ x)) ≅ₚ (f e)
≔-subst {α} {x} {e} {f} {k} {E} {S₁} {S₂}
  with ⊢-total {α} {E} {e}
... | v , E⊢e⇒v
    with ≅ₛ-subst {f = f} (deref {x ↦ val v , E} {α} {x} x↦v∈x↦v,E) E⊢e⇒v refl
...   | inj₁ (f[★x]↝ω , f[e]↝ω) =
        let reduction = ↝-seq ◅ ↝-assignment E⊢e⇒v ◅ ↝-nop ◅ ε in
          inj₁ (↝ω-transᵇ reduction f[★x]↝ω , f[e]↝ω)
...   | inj₂ t = inj₂ (λ x≔e/f[★x]↝*S₁ f[e]↝*S₂ S₁↝̸ S₂↝̸ →
        let reduction = ↝-seq ◅ ↝-assignment E⊢e⇒v ◅ ↝-nop ◅ ε in
          t (↝*-det' reduction x≔e/f[★x]↝*S₁ S₁↝̸) f[e]↝*S₂ S₁↝̸ S₂↝̸)
