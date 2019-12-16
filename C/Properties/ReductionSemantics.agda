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

_↦_∈_ : ∀ { α } { v : ⟦ α ⟧ } → (x : Ref α) → (V : Value α v) → (E : Env) → ∀ { _ : x ∈ E } → Set
(x ↦ val v ∈ _) {x∈x↦v,E {v = w}} = v ≡ w
(x ↦ val v ∈ _) {x∈x,E} = ⊥
(x ↦ val v ∈ (_ ↦ _ , E)) {xα∈yβ↦w,E x∈E} = (x ↦ val v ∈ E) {x∈E}
(x ↦ val v ∈ (_ , E)) {xα∈yβ,E x∈E} = (x ↦ val v ∈ E) {x∈E}
(x ↦ val v ∈ (_ ↦ _ , E)) {xα∈yα↦w,E x∈E} = (x ↦ val v ∈ E) {x∈E}
(x ↦ val v ∈ (_ , E)) {xα∈yα,E x∈E} = (x ↦ val v ∈ E) {x∈E}

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

record Semantics : Set₁ where
  field
    _⊢_⇒_ : ∀ { α } → ∀ { v : ⟦ α ⟧ } → Env → Expr α → Value α v → Set
    ⇒-determinacy : ∀ { E α } { x : Expr α } { v w : ⟦ α ⟧ }
      → E ⊢ x ⇒ val v → E ⊢ x ⇒ val w → v ≡ w
    ⇒-weakening : ∀ { E E' α β } { e : Expr α } { v : ⟦ α ⟧ } { x : Ref β } { w : ⟦ β ⟧ }
      → { _ : x ∉ E × x ∉ E' }
      → (E ⊕ E') ⊢ e ⇒ val v → (E ⊕ (x ↦ val w , ε) ⊕ E') ⊢ e ⇒ val v
    ⇒-exchange : ∀ { E E' α β γ } { x : Ref α } { y : Ref β }
      → { v : ⟦ α ⟧ } { w : ⟦ β ⟧ } { e : Expr γ } { ev : ⟦ γ ⟧ }
      → (E ⊕ (x ↦ val v , (y ↦ val w , ε)) ⊕ E') ⊢ e ⇒ val ev
      → (E ⊕ (y ↦ val w , (x ↦ val v , ε)) ⊕ E') ⊢ e ⇒ val ev
    -- TODO: variants on Env constructor
    -- NB: some of these would come for free with a data specification, rather than
    -- a tagless style
    nat : ∀ { E n } → E ⊢ ⟨ n ⟩ ⇒ val n
    deref : ∀ { E α } → ∀ { x : Ref α } → ∀ { e : ⟦ α ⟧ } → ∀ { v : Value α e }
      → ∀ { x∈E : x ∈ E } → ((x ↦ v ∈ E) {x∈E}) → (E ⊢ (★ x) ⇒ v)
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

  infix 0 _≅ₑ_
  _≅ₑ_ : ∀ { α } → Rel (Expr α) 0ℓ
  _≅ₑ_ { α } x y = ∀ { E : Env } → ∀ { v w : ⟦ α ⟧ }
    → (E ⊢ x ⇒ val v) → (E ⊢ y ⇒ val w) → (v ≡ w)

  _↝⁺_ : State → State → Set
  _↝⁺_ S₁ S₂ = S₁ ⟨ _↝_ ⟩⁺ S₂

  _↝*_ : State → State → Set
  _↝*_ = Star _↝_

  NonTerminating : State → Set
  NonTerminating S = ∀ { S' : State }
    → S ↝* S' → (∃ λ S'' → S' ↝ S'')

  NonTerminatingₛ : Statement → Set
  NonTerminatingₛ s = ∀ { k E } → NonTerminating (𝒮 s k E)

  Terminating : State → Set
  Terminating S = ¬ (NonTerminating S)

  Terminatingₛ : Statement → Set
  Terminatingₛ s = ∀ { k E } → Terminating (𝒮 s k E)

  _≅ₛ_ : Rel Statement 0ℓ
  _≅ₛ_ x y = ∀ { k : Continuation } → ∀ { E : Env } → ∀ { S₁ S₂ : State }
    → (NonTerminating (𝒮 x k E) × NonTerminating (𝒮 y k E))
      ⊎ (𝒮 x k E ↝* S₁ → 𝒮 y k E ↝* S₂
        → (∀ S' → ¬ (S₁ ↝ S')) → (∀ S' → ¬ (S₂ ↝ S'))
        → S₁ ≡ S₂)

  field
    ≅ₑ-equiv : ∀ { α } → IsEquivalence (_≅ₑ_ { α })
    ≅ₛ-equiv : IsEquivalence _≅ₛ_
    ↝-det : ∀ { S S₁ S₂ } → S ↝ S₁ → S ↝ S₂ → S₁ ≡ S₂

open Semantics ⦃ ... ⦄

open ≡-Reasoning

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

↝*-trans : ∀ ⦃ _ : Semantics ⦄ → Transitive _↝*_
↝*-trans = _◅◅_

↝*-to-↝⁺ : ∀ ⦃ _ : Semantics ⦄ { A B C } → A ↝ B → B ↝* C → A ↝⁺ C
↝*-to-↝⁺ A↝B ε = Plus′.[ A↝B ]
↝*-to-↝⁺ A↝B (B↝X ◅ X↝*C) = A↝B ∷ (↝*-to-↝⁺ B↝X X↝*C)

↝⁺-to-↝* : ∀ ⦃ _ : Semantics ⦄ { A B } → A ↝⁺ B → A ↝* B
↝⁺-to-↝* Plus′.[ A↝B ] = A↝B ◅ ε
↝⁺-to-↝* (A↝X ∷ X↝⁺B) = A↝X ◅ (↝⁺-to-↝* X↝⁺B)

↝ω-interchange : ∀ ⦃ _ : Semantics ⦄ { s k E }
  → NonTerminatingₛ s → NonTerminating (𝒮 s k E)
↝ω-interchange ↝ωₛ = ↝ωₛ

↝̸-interchange : ∀ ⦃ _ : Semantics ⦄ { s k E }
  → Terminatingₛ s → Terminating (𝒮 s k E)
↝̸-interchange ↝̸ₛ = ↝̸ₛ

↝ω-transᵇ : ∀ ⦃ _ : Semantics ⦄ { X Y : State }
  → X ↝ Y → NonTerminating Y → NonTerminating X
↝ω-transᵇ {X} {Y} X↝Y Y↝ω ε = Y , X↝Y
↝ω-transᵇ {X} {Y} X↝Y Y↝ω (X↝A ◅ A↝*Y)
  with ↝-det X↝Y X↝A
... | refl = Y↝ω A↝*Y

↝ω-transᶠ : ∀ ⦃ _ : Semantics ⦄ { S S' : State }
  → S ↝ S' → NonTerminating S → NonTerminating S'
↝ω-transᶠ {S} {S'} S↝S' S↝ω S'↝*S'' = S↝ω {!!}

↝̸-transᵇ : ∀ ⦃ _ : Semantics ⦄ { S S' : State }
  → S ↝ S' → Terminating S' → Terminating S

↝̸-transᶠ : ∀ ⦃ _ : Semantics ⦄ { S S' : State }
  → S ↝ S' → Terminating S → Terminating S'

↝⁺-contr : ∀ ⦃ _ : Semantics ⦄ { S S' } → (∀ S'' → ¬ (S ↝ S'')) → S ↝⁺ S' → ⊥
↝⁺-contr {S} {S'} S↝̸ Plus′.[ S↝S' ] = S↝̸ S' S↝S'
↝⁺-contr S↝̸ (_∷_ {y = y} S↝y y↝⁺S') = S↝̸ y S↝y

↝*-det : ∀ ⦃ _ : Semantics ⦄ { S S₁ S₂ }
  → Terminating S → (∀ S' → ¬ (S₁ ↝ S')) → (∀ S' → ¬ (S₂ ↝ S'))
  → S ↝* S₁ → S ↝* S₂ → S₁ ≡ S₂
↝*-det ↝̸ S₁↝̸ S₂↝̸ ε ε = refl
↝*-det ↝̸ S↝̸ S₂↝̸ ε (S↝X ◅ X↝*S₂) = ⊥-elim (↝⁺-contr S↝̸ (↝*-to-↝⁺ S↝X X↝*S₂))
↝*-det ↝̸ S₁↝̸ S↝̸ (S↝X ◅ X↝*S₂) ε = ⊥-elim (↝⁺-contr S↝̸ (↝*-to-↝⁺ S↝X X↝*S₂))
↝*-det ↝̸ S₁↝̸ S₂↝̸ (S↝X ◅ X↝*S₁) (S↝Y ◅ Y↝*S₂)
  with ↝-det S↝X S↝Y
... | refl = ↝*-det (↝̸-transᶠ S↝X ↝̸) S₁↝̸ S₂↝̸ X↝*S₁ Y↝*S₂

↝*-det-progress : ∀ ⦃ _ : Semantics ⦄ { S S' S'' }
  → S ↝ S' → S ↝⁺ S'' → S' ↝* S''
↝*-det-progress S↝S' Plus′.[ S↝S'' ]
  with ↝-det S↝S' S↝S''
... | refl = ε
↝*-det-progress S↝S' (S↝X ∷ X↝⁺S'') with ↝-det S↝S' S↝X
... | refl = ↝⁺-to-↝* X↝⁺S''

β-if-true : ∀ ⦃ _ : Semantics ⦄ → ∀ { x y : Statement }
  → ∀ { _ : Terminatingₛ x ⊎ NonTerminatingₛ x }
  → (if true then x else y) ≅ₛ x
β-if-true {x} {y} {inj₁ ↝̸} =
  let helper :
        ∀ { k E S₁ S₂ }
        → 𝒮 (if true then x else y) k E ↝* S₁
        → 𝒮 x k E ↝* S₂
        → (∀ S' → ¬ (S₁ ↝ S'))
        → (∀ S' → ¬ (S₂ ↝ S'))
        → S₁ ≡ S₂
      helper {k} {E} = λ {
        ε x↝*S₂ S₁↝̸ S₂↝̸ →
          ⊥-elim (S₁↝̸ (𝒮 x k E) (↝-if-true true-eval)) ;
        if↝⁺S₁@(_ ◅ _) x↝*S₂ S₁↝̸ S₂↝̸ →
          ↝*-det (↝̸-interchange ↝̸) S₁↝̸ S₂↝̸ (↝*-det-progress (↝-if-true true-eval) {!if↝⁺S₁!}) x↝*S₂ }
  in
    inj₂ helper
β-if-true {_} {_} {inj₂ →ω} =
  inj₁ (↝ω-transᵇ (↝-if-true true-eval) →ω , →ω)

-- β-if-false : ⦃ _ : Equivalence ⦄ → ∀ { x y : Statement }
--   → if false then x else y ≡ y
-- β-if-false = {!!}

-- η-if : ⦃ _ : Equivalence ⦄ → ∀ { cond : Expr Bool } → ∀ { e : Statement }
--   → if cond then e else e ≡ e
-- η-if = {!!}

-- β-while : ⦃ _ : Equivalence ⦄ → ∀ { e₁ : Expr Bool } → ∀ { e₂ : Statement }
--   → while e₁ then e₂ ≡ if e₁ then (e₂ ； while e₁ then e₂) else nop
