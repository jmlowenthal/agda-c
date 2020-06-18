open import C.Lang
open import C.Semantics.SmallStep.Model
open import C.Semantics.SmallStep.Properties.Equivalence
open import Codata.Musical.Notation
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality

import Data.Bool as 𝔹

module C.Semantics.SmallStep.Properties.Properties ⦃ _ : Lang ⦄ ⦃ _ : Semantics ⦄ where

open Lang ⦃ ... ⦄
open Semantics ⦃ ... ⦄
open [≈]-Reasoning

β-if-true : ∀ { x y : Statement }
  → (if true then x else y) ≅ₚ x
β-if-true = ↝⇒≅ₛ (↝-if-true true-eval)

β-if-false : ∀ { x y : Statement } → if false then x else y ≅ₚ y
β-if-false = ↝⇒≅ₛ (↝-if-false false-eval)

η-if : ∀ { cond : Expr Bool } { e : Statement } → if cond then e else e ≅ₚ e
η-if {cond}
  with ⊢-total {e = cond}
... | (𝔹.false , ⇒false) = ↝⇒≅ₛ (↝-if-false ⇒false)
... | (𝔹.true , ⇒true) = ↝⇒≅ₛ (↝-if-true ⇒true)

β-while : ∀ { e₁ : Expr Bool } { e₂ : Statement }
  → while e₁ then e₂ ≅ₚ if e₁ then (e₂ ； while e₁ then e₂) else nop
β-while = ↝⇒≅ₛ ↝-while

≔-subst : ∀ { α } { x : Ref α } { e : Expr α } { f : Expr α → Statement }
  → x ≔ e ； f (★ x) ≅ₚ f e
≔-subst {α} {x} {e} {f} {k} {E} =
  let v , ⇒v = ⊢-total {α} {E} {e} in
    begin
      labels (𝒮 (x ≔ e ； f (★ x)) k E)
      ≈⟨ ↝⇒≅ₛ ↝-seq ⟩
      labels (𝒮 (x ≔ e) ((f (★ x)) ∷ k) E)
      ≈⟨ [≈]-reflexive (reduce-det (reduce _) (↝-assignment ⇒v ∷ ♯ reduce _)) ⟩
      labels-of (↝-assignment ⇒v ∷ _) 
      ≈⟨ left ignore-↦ (♯ [≈]-refl) ⟩
      labels (𝒮 nop ((f (★ x)) ∷ k) (x Env.↦ v , E))
      ≈⟨ ↝⇒≅ₛ ↝-nop ⟩
      labels (𝒮 (f (★ x)) k (x Env.↦ v , E))
      ≈⟨ ≅ₛ-subst (deref x↦v∈x↦v,E) ⇒v refl ⟩
      labels (𝒮 (f e) k E)
    ∎

decl-elim : ∀ { α } { f : Statement } → (decl α λ x → f) ≅ₚ f
decl-elim {α} {f} = ≅ₛ-decl
