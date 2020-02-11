-- Based in-part on "A formally verified compiler back-end" by Xavier Leroy

open import C

open import Algebra.FunctionProperties
open import C.Properties.State
open import Data.Bool as 𝔹 using () renaming (Bool to 𝔹)
open import Data.Empty
open import Data.Integer as ℤ using (ℤ ; +_)
open import Data.Product using (Σ ; ∃ ; ∃-syntax ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum
open import Data.Unit
open import Data.Vec using (Vec ; [] ; _∷_)
open import Function
open import Level using (0ℓ)
open import Relation.Binary
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.Construct.Closure.Transitive hiding (_++_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable

import Data.Integer.DivMod as ℤ÷
import Data.Integer.Properties as ℤₚ
import Data.Nat as ℕ
import Data.Nat.Properties as ℕₚ

open C.C ⦃ ... ⦄
open ≡-Reasoning

module C.Properties.ReductionSemantics ⦃ _ : C ⦄ where

Congruence : ∀ { a l } { A : Set a } → Rel A l → Set _
Congruence {A = A} _~_ = ∀ (f : A → A) x y → x ~ y → (f x) ~ (f y)

record Semantics : Set₁ where
  field
    _⊢_⇒_ : ∀ { α } → ∀ { v : ⟦ α ⟧ } → Env → Expr α → Value α v → Set
    ⊢-total : ∀ { α E } { e : Expr α } → ∃ λ v → (E ⊢ e ⇒ val v)
    ⊢-det : ∀ { α E } { e : Expr α } { v w : ⟦ α ⟧ } → E ⊢ e ⇒ val v → E ⊢ e ⇒ val w → v ≡ w 
    ⊢-weakening : ∀ { E E' α β } { e : Expr α } { v : ⟦ α ⟧ } { x : Ref β } { w : ⟦ β ⟧ }
      → { _ : x ∉nv E × x ∉nv E' }
      → (E ⊕ E') ⊢ e ⇒ val v → (E ⊕ (x ↦ val w , ε) ⊕ E') ⊢ e ⇒ val v
    ⊢-exchange : ∀ { E E' α β γ } { x : Ref α } { y : Ref β }
      → { v : ⟦ α ⟧ } { w : ⟦ β ⟧ } { e : Expr γ } { ev : ⟦ γ ⟧ }
      → (E ⊕ (x ↦ val v , (y ↦ val w , ε)) ⊕ E') ⊢ e ⇒ val ev
      → (E ⊕ (y ↦ val w , (x ↦ val v , ε)) ⊕ E') ⊢ e ⇒ val ev
    -- TODO: variants on Env constructor
    nat : ∀ { E } n → E ⊢ ⟨ n ⟩ ⇒ val n
    deref : ∀ { E α } { x : Ref α } { v : ⟦ α ⟧ }
      → x ↦ val v ∈nv E → (E ⊢ (★ x) ⇒ val v)
    +-eval : ∀ { E x y x' y' }
      → E ⊢ x ⇒ val x' → E ⊢ y ⇒ val y'
      → E ⊢ x + y ⇒ val (x' ℤ.+ y')
    *-eval : ∀ { E x y x' y' }
      → E ⊢ x ⇒ val x' → E ⊢ y ⇒ val y'
      → E ⊢ x * y ⇒ val (x' ℤ.* y')
    ∸-eval : ∀ { E x y x' y' }
      → E ⊢ x ⇒ val x' → E ⊢ y ⇒ val y'
      → E ⊢ x - y ⇒ val (x' ℤ.- y')
    /-eval : ∀ { E x y x' y' }
      → E ⊢ x ⇒ val x' → E ⊢ y ⇒ val y' → (y≠0 : False (ℤ.∣ y' ∣ ℕ.≟ 0))
      → E ⊢ x / y ⇒ val ((x' ℤ÷.div y') {y≠0})
    true-eval : ∀ { E } → E ⊢ true ⇒ val 𝔹.true
    false-eval : ∀ { E } → E ⊢ false ⇒ val 𝔹.false
    ||-eval : ∀ { E x y x' y' }
      → E ⊢ x ⇒ val x' → E ⊢ y ⇒ val y' → E ⊢ x || y ⇒ val (x' 𝔹.∨ y')
    &&-eval : ∀ { E x y x' y' }
      → E ⊢ x ⇒ val x' → E ⊢ y ⇒ val y' → E ⊢ x && y ⇒ val (x' 𝔹.∧ y')

    _↝_ : Rel State 0ℓ
    ↝-if-true : ∀ { E k } { cond : Expr Bool } { s₁ s₂ : Statement }
      → E ⊢ cond ⇒ val 𝔹.true → 𝒮 (if cond then s₁ else s₂) k E ↝ 𝒮 s₁ k E
    ↝-if-false : ∀ { E k } { cond : Expr Bool } { s₁ s₂ : Statement }
      → E ⊢ cond ⇒ val 𝔹.false → 𝒮 (if cond then s₁ else s₂) k E ↝ 𝒮 s₂ k E
    ↝-assignment : ∀ { E k α } { id : Ref α } { e : Expr α } { v : ⟦ α ⟧ }
      → E ⊢ e ⇒ val v → 𝒮 (id ≔ e) k E ↝ 𝒮 nop k (id ↦ val v , E)
    ↝-seq : ∀ { E k } { s₁ s₂ : Statement }
      → 𝒮 (s₁ ； s₂) k E ↝ 𝒮 s₁ (s₂ then k) E
    ↝-decl : ∀ { E k α } { f : Ref α → Statement }
      → ∃ λ (x : Ref α) → (x ∉nv E) × (𝒮 (decl α f) k E ↝ 𝒮 (f x) k (x , E))
    ↝-nop : ∀ { E k } { s : Statement } → 𝒮 nop (s then k) E ↝ 𝒮 s k E
    ↝-for : ∀ { E k } { l u : Expr Int } { f : Ref Int → Statement } { x : Ref Int }
      → 𝒮 (for l to u then f) k E
        ↝ 𝒮 (if (l < u) then (
                (decl Int λ i → i ≔ l ； f i) ；
                for (l + ⟨ + 1 ⟩) to u then f)
             else nop) k E
    ↝-while : ∀ { E k } { e : Expr Bool } { s : Statement }
      → 𝒮 (while e then s) k E ↝ 𝒮 (if e then (s ； while e then s) else nop) k E
    ↝-det : ∀ { S S₁ S₂ } → S ↝ S₁ → S ↝ S₂ → S₁ ≡ S₂

  infix 0 _≅ₑ_
  _≅ₑ_ : ∀ { α } → Rel (Expr α) 0ℓ
  _≅ₑ_ { α } x y = ∀ { E : Env } { v w : ⟦ α ⟧ }
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
  X ≅ₛ Y =
    (∃[ A ] (X ↝* A × Y ↝* A)) ⊎ (¬ Terminating X × ¬ Terminating Y)

  field
    ≅ₛ-subst :
      ∀ { α E₁ E₂ k } { v w : ⟦ α ⟧ } { f : Expr α → Statement } { e₁ e₂ : Expr α }
      → E₁ ⊢ e₁ ⇒ val v → E₂ ⊢ e₂ ⇒ val w → v ≡ w
      → 𝒮 (f e₁) k E₁ ≅ₛ 𝒮 (f e₂) k E₂
    ≅ₛ-decl : ∀ { α f k E } → 𝒮 (decl α λ x → f) k E ≅ₛ 𝒮 f k E
    ≅ₛ-cong : Congruence _≅ₛ_


  -- EXPRESSION EQUIVALENCE

  ≅ₑ-refl : ∀ { α } → Reflexive (_≅ₑ_ {α})
  ≅ₑ-refl ⇒v ⇒w = ⊢-det ⇒v ⇒w

  ≅ₑ-sym : ∀ { α } → Symmetric (_≅ₑ_ {α})
  ≅ₑ-sym i≅j ⇒v ⇒w = sym (i≅j ⇒w ⇒v)

  ≅ₑ-trans : ∀ { α } → Transitive (_≅ₑ_ {α})
  ≅ₑ-trans i≅j j≅k ⇒v ⇒w =
    let _ , ⇒a = ⊢-total in
      trans (i≅j ⇒v ⇒a) (j≅k ⇒a ⇒w)

  ≅ₑ-equiv : ∀ { α } → IsEquivalence (_≅ₑ_ {α})
  ≅ₑ-equiv = record { refl = ≅ₑ-refl ; sym = ≅ₑ-sym ; trans = ≅ₑ-trans }


  -- REDUCTION LEMMAS

  ↝*-trans : Transitive _↝*_
  ↝*-trans = _◅◅_

  ↝*-to-↝⁺ : ∀ { A B C } → A ↝ B → B ↝* C → A ↝⁺ C
  ↝*-to-↝⁺ A↝B ε = Plus′.[ A↝B ]
  ↝*-to-↝⁺ A↝B (B↝X ◅ X↝*C) = A↝B ∷ (↝*-to-↝⁺ B↝X X↝*C)

  ↝⁺-to-↝* : ∀ { A B } → A ↝⁺ B → A ↝* B
  ↝⁺-to-↝* Plus′.[ A↝B ] = A↝B ◅ ε
  ↝⁺-to-↝* (A↝X ∷ X↝⁺B) = A↝X ◅ (↝⁺-to-↝* X↝⁺B)

  ↝̸-transᵇ : ∀ { S S' : State }
    → S ↝* S' → Terminating S' → Terminating S
  ↝̸-transᵇ {S} {S'} S↝*S' (X , S'↝*X , X↝̸) = X , (S↝*S' ◅◅ S'↝*X) , X↝̸

  ↝̸-transᶠ : ∀ { S S' : State }
    → S ↝* S' → Terminating S → Terminating S'
  ↝̸-transᶠ ε S↝̸ = S↝̸
  ↝̸-transᶠ (S↝X ◅ X↝*S') (S , ε , S↝̸) = ⊥-elim (S↝̸ _ S↝X)
  ↝̸-transᶠ (S↝A ◅ A↝*S') (X , S↝Y ◅ Y↝*X , X↝̸)
    with ↝-det S↝A S↝Y
  ... | refl = ↝̸-transᶠ A↝*S' (X , Y↝*X , X↝̸)

  ↝ω-transᵇ : ∀ { X Y : State }
    → X ↝* Y → ¬ Terminating Y → ¬ Terminating X
  ↝ω-transᵇ {X} {Y} X↝*Y Y↝ω X↝̸ = Y↝ω (↝̸-transᶠ X↝*Y X↝̸)

  ↝ω-transᶠ : ∀ { X Y : State }
    → X ↝* Y → ¬ Terminating X → ¬ Terminating Y
  ↝ω-transᶠ {X} {Y} X↝*Y X↝ω Y↝̸ = X↝ω (↝̸-transᵇ X↝*Y Y↝̸)

  ↝*-det : ∀ { S S₁ S₂ }
    → Stuck S₁ → Stuck S₂ → S ↝* S₁ → S ↝* S₂ → S₁ ≡ S₂
  ↝*-det S₁↝̸ S₂↝̸ ε ε = refl
  ↝*-det S↝̸ S₂↝̸ ε (_◅_ {j = X} S↝X X↝*S₂) = ⊥-elim (S↝̸ X S↝X)
  ↝*-det S₁↝̸ S↝̸ (_◅_ {j = X} S↝X X↝*S₂) ε = ⊥-elim (S↝̸ X S↝X)
  ↝*-det S₁↝̸ S₂↝̸ (S↝X ◅ X↝*S₁) (S↝Y ◅ Y↝*S₂)
    rewrite ↝-det S↝X S↝Y = ↝*-det S₁↝̸ S₂↝̸ X↝*S₁ Y↝*S₂

  ↝*-det' : ∀ { S S₁ S₂ }
    → S ↝* S₁ → S ↝* S₂ → S₁ ↝* S₂ ⊎ S₂ ↝* S₁
  ↝*-det' ε S↝*S₂ = inj₁ S↝*S₂
  ↝*-det' S↝*S₁@(S↝X ◅ X↝*S₁) ε = inj₂ S↝*S₁
  ↝*-det' (S↝X ◅ X↝*S₁) (S↝Y ◅ Y↝*S₂)
    rewrite ↝-det S↝X S↝Y = ↝*-det' X↝*S₁ Y↝*S₂

  ≅ₛ-refl : Reflexive _≅ₛ_
  ≅ₛ-refl {x} = inj₁ (x , ε , ε)

  ≅ₛ-sym : Symmetric _≅ₛ_
  ≅ₛ-sym (inj₁ (A , i↝*A , j↝*A)) = inj₁ (A , j↝*A , i↝*A)
  ≅ₛ-sym (inj₂ (i↝ω , j↝ω)) = inj₂ (j↝ω , i↝ω)

  ≅ₛ-trans : Transitive _≅ₛ_
  ≅ₛ-trans (inj₁ (A , i↝*A , j↝*A)) (inj₁ (B , j↝*B , k↝*B))
    with ↝*-det' j↝*A j↝*B
  ... | inj₁ A↝*B = inj₁ (B , i↝*A ◅◅ A↝*B , k↝*B)
  ... | inj₂ B↝*A = inj₁ (A , i↝*A , k↝*B ◅◅ B↝*A)
  ≅ₛ-trans (inj₁ (A , i↝*A , j↝*A)) (inj₂ (j↝ω , k↝ω)) =
    inj₂ (↝ω-transᵇ i↝*A (↝ω-transᶠ j↝*A j↝ω) , k↝ω)
  ≅ₛ-trans (inj₂ (i↝ω , j↝ω)) (inj₁ (A , j↝*A , k↝*A)) =
    inj₂ (i↝ω , (↝ω-transᵇ k↝*A (↝ω-transᶠ j↝*A j↝ω)))
  ≅ₛ-trans (inj₂ (i↝ω , j↝ω)) (inj₂ (j↝ω' , k↝ω)) = inj₂ (i↝ω , k↝ω)

  ≅ₛ-equiv : IsEquivalence _≅ₛ_
  ≅ₛ-equiv = record { refl = ≅ₛ-refl ; sym = ≅ₛ-sym ; trans = ≅ₛ-trans }

  ↝*⇒≅ₛ : ∀ { A B } → A ↝* B → A ≅ₛ B
  ↝*⇒≅ₛ A↝*B = inj₁ (_ , A↝*B , ε)

