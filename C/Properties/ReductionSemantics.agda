-- Based in-part on "A formally verified compiler back-end" by Xavier Leroy

open import C
open import Function
open import Relation.Binary
open import Relation.Nullary.Decidable
open import Level using (0ℓ)
open import Data.Product using (Σ ; ∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Algebra.FunctionProperties
open import Data.Unit
open import Data.Empty
open import Data.Sum
open import Data.Integer as ℤ using (ℤ ; +_)
import Data.Integer.DivMod as ℤ÷
import Data.Integer.Properties as ℤₚ
import Data.Nat as ℕ
import Data.Nat.Properties as ℕₚ
open import Relation.Nullary
open import Data.Bool as 𝔹 using () renaming (Bool to 𝔹)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Construct.Closure.Transitive
  hiding (_++_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Data.Vec using (Vec ; [] ; _∷_)
import C.Properties.FreeVariables as FV

open C.C ⦃ ... ⦄

open ≡-Reasoning

module C.Properties.ReductionSemantics
  ⦃ _ : C ⦄
  { _~_ : Rel (∃ λ β → Ref β) Level.zero }
  { isStrictTotalOrder : IsStrictTotalOrder _≡_ _~_ }
  ⦃ _ : FV.FreeVariables isStrictTotalOrder ⦄ where

open FV.FreeVariables ⦃ ... ⦄
open FV isStrictTotalOrder

open import C.Properties.State

Congruence : ∀ { a l } { A : Set a } → Rel A l → Set _
Congruence {A = A} _~_ = ∀ (f : A → A) x y → x ~ y → (f x) ~ (f y)

record Semantics : Set₁ where
  field
    _⊢_⇒_ : ∀ { α } → ∀ { v : ⟦ α ⟧ } → Env → Expr α → Value α v → Set
    ⊢-total : ∀ { α E } { e : Expr α } → ∃ λ v → (E ⊢ e ⇒ val v)
    ⊢-weakening : ∀ { E E' α β } { e : Expr α } { v : ⟦ α ⟧ } { x : Ref β } { w : ⟦ β ⟧ }
      → { _ : x ∉nv E × x ∉nv E' }
      → (E ⊕ E') ⊢ e ⇒ val v → (E ⊕ (x ↦ val w , ε) ⊕ E') ⊢ e ⇒ val v
    ⊢-exchange : ∀ { E E' α β γ } { x : Ref α } { y : Ref β }
      → { v : ⟦ α ⟧ } { w : ⟦ β ⟧ } { e : Expr γ } { ev : ⟦ γ ⟧ }
      → (E ⊕ (x ↦ val v , (y ↦ val w , ε)) ⊕ E') ⊢ e ⇒ val ev
      → (E ⊕ (y ↦ val w , (x ↦ val v , ε)) ⊕ E') ⊢ e ⇒ val ev
    -- TODO: variants on Env constructor
    nat : ∀ { E n } → E ⊢ ⟨ n ⟩ ⇒ val n
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
    ↝-if-true : ∀ { E k } { cond : Expr Bool } { s₁ s₂ : Statement } { wf }
      → E ⊢ cond ⇒ val 𝔹.true
      → 𝒮 (if cond then s₁ else s₂) k E wf ↝ 𝒮 s₁ k E (⊆-covers wf (⊆-cong fv-if₂ ⊆-refl))
    ↝-if-false : ∀ { E k } { cond : Expr Bool } { s₁ s₂ : Statement } { wf }
      → E ⊢ cond ⇒ val 𝔹.false
      → 𝒮 (if cond then s₁ else s₂) k E wf ↝ 𝒮 s₂ k E (⊆-covers wf (⊆-cong fv-if₃ ⊆-refl))
    ↝-assignment : ∀ { E k α } { id : Ref α } { e : Expr α } { v : ⟦ α ⟧ } { wf }
      → E ⊢ e ⇒ val v
      → 𝒮 (id ≔ e) k E wf ↝ 𝒮 nop k (id ↦ val v , E)
        (grow-env (⊆-covers wf (⊆-cong (fv-nop₁ {fvₛ (id ≔ e)}) ⊆-refl)))
    ↝-seq : ∀ { E k } { s₁ s₂ : Statement } { wf }
      → 𝒮 (s₁ ； s₂) k E wf ↝ 𝒮 s₁ (s₂ then k) E (⊆-covers wf fv-seq₁)
    ↝-decl : ∀ { E k α } { f : Ref α → Statement } { wf }
      → ∃ λ (x : Ref α) → (x ∉nv E) × (𝒮 (decl α f) k E wf ↝ 𝒮 (f x) k (x , E) {!wf!})
    ↝-nop : ∀ { E k } { s : Statement } { wf }
      → 𝒮 nop (s then k) E wf ↝ 𝒮 s k E (⊆-covers wf fv-nop₂)
    ↝-for : ∀ { E k } { l u : Expr Int } { f : Ref Int → Statement } { wf } { x : Ref Int }
      → 𝒮 (for l to u then f) k E wf
        ↝ 𝒮 (if (l < u) then (
                (decl Int λ i → i ≔ l ； f i) ；
                for (l + ⟨ + 1 ⟩) to u then f)
             else nop) k E
             (⊆-covers wf (⊆-cong (proj₂ (≡⇒⊆ (fv-for₁ {x = x}))) ⊆-refl))
    ↝-while : ∀ { E k } { e : Expr Bool } { s : Statement } { wf }
      → 𝒮 (while e then s) k E wf ↝ 𝒮 (if e then (s ； while e then s) else nop) k E
        (⊆-covers wf (⊆-cong (proj₂ (≡⇒⊆ fv-while₁)) ⊆-refl))
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
    ≅ₛ-subst :
      ∀ { α E₁ E₂ k } { v w : ⟦ α ⟧ } { f : Expr α → Statement } { e₁ e₂ : Expr α } { wf₁ wf₂ }
      → E₁ ⊢ e₁ ⇒ val v → E₂ ⊢ e₂ ⇒ val w → v ≡ w
      → 𝒮 (f e₁) k E₁ wf₁ ≅ₛ 𝒮 (f e₂) k E₂ wf₂
    ≅ₛ-cong : Congruence _≅ₛ_

