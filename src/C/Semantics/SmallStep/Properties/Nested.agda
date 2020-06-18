open import C.Lang
open import C.Semantics.SmallStep.Model
open import C.Semantics.SmallStep.Properties.Equivalence
open import Codata.Musical.Colist
open import Codata.Musical.Notation
open import Data.List
open import Data.Product

import Data.Bool as 𝔹

module C.Semantics.SmallStep.Properties.Nested ⦃ _ : Lang ⦄ ⦃ _ : Semantics ⦄ where

open Lang ⦃ ... ⦄
open Semantics ⦃ ... ⦄
open [≈]-Reasoning

nested-while-loop : ∀ { s : Statement }
  → while true then s ≅ₚ while true then (while true then s)
nested-while-loop {s} {k} {E} =
  begin
    labels (𝒮 (while true then s) k E)
  ≈⟨ ↝*⇒≅ₛ (↝-while ◅ ♯ (↝-if-true true-eval ◅ ♯ (↝-seq ◅ ♯ ε))) ⟩
    labels (𝒮 s ((while true then s) ∷ k) E)
  ≈˘⟨ ↝⇒≅ₛ ↝-nop ⟩
    labels (𝒮 nop (s ∷ (while true then s) ∷ k) E)
  ≈⟨
    cont-equiv
      (≅ₛ-refl {𝒮 nop (s ∷ []) E})
      (λ E' →
        cont-equiv
          (begin
            labels (𝒮 nop ((while true then s) ∷ []) E')
            ≈⟨ ↝⇒≅ₛ ↝-nop ⟩
            labels (𝒮 (while true then s) [] E')
            ≈⟨ ≅ₛ-while-true ⟩
            labels (𝒮 (while true then s) ((while true then (while true then s)) ∷ []) E')
            ≈˘⟨ ↝⇒≅ₛ ↝-nop ⟩
            labels (𝒮 nop ((while true then s) ∷ (while true then (while true then s)) ∷ []) E')
          ∎)
          (λ E'' → ≅ₛ-refl {𝒮 nop k E''}))
  ⟩
    labels (𝒮 nop (s ∷ (while true then s) ∷ (while true then (while true then s)) ∷ k) E)
  ≈⟨ ↝⇒≅ₛ ↝-nop ⟩
    labels (𝒮 s ((while true then s) ∷ (while true then (while true then s)) ∷ k) E)
  ≈˘⟨
    ↝*⇒≅ₛ
      (↝-while
        ◅ ♯ (↝-if-true true-eval
        ◅ ♯ (↝-seq
        ◅ ♯ (↝-while
        ◅ ♯ (↝-if-true true-eval
        ◅ ♯ (↝-seq
        ◅ ♯ ε)))))) ⟩
    labels (𝒮 (while true then (while true then s)) k E)
  ∎

nested-if : ∀ { e e' : Expr Bool } { s : Statement } { k E }
  → 𝒮 (if e then (if e' then s else nop) else nop) k E ≅ₛ 𝒮 (if (e && e') then s else nop) k E
nested-if {e} {e'} {s} {k} {E}
  with ⊢-total {Bool} {E} {e} | ⊢-total {Bool} {E} {e'}
... | 𝔹.false , ⇒v | _ , ⇒w =
  begin
    labels (𝒮 (if e then (if e' then s else nop) else nop) k E)
    ≈⟨ ↝⇒≅ₛ (↝-if-false ⇒v) ⟩
    labels (𝒮 nop k E)
    ≈˘⟨ ↝⇒≅ₛ (↝-if-false (&&-eval ⇒v ⇒w)) ⟩
    labels (𝒮 (if (e && e') then s else nop) k E)
  ∎
... | 𝔹.true , ⇒v | 𝔹.false , ⇒w =
  begin
    labels (𝒮 (if e then (if e' then s else nop) else nop) k E)
    ≈⟨ ↝⇒≅ₛ (↝-if-true ⇒v) ⟩
    labels (𝒮 (if e' then s else nop) k E)
    ≈⟨ ↝⇒≅ₛ (↝-if-false ⇒w) ⟩
    labels (𝒮 nop k E)
    ≈˘⟨ ↝⇒≅ₛ (↝-if-false (&&-eval ⇒v ⇒w)) ⟩
    labels (𝒮 (if (e && e') then s else nop) k E)
  ∎
... | 𝔹.true , ⇒v | 𝔹.true , ⇒w =
  begin
    labels (𝒮 (if e then (if e' then s else nop) else nop) k E)
    ≈⟨ ↝⇒≅ₛ (↝-if-true ⇒v) ⟩
    labels (𝒮 (if e' then s else nop) k E)
    ≈⟨ ↝⇒≅ₛ (↝-if-true ⇒w) ⟩
    labels (𝒮 s k E)
    ≈˘⟨ ↝⇒≅ₛ (↝-if-true (&&-eval ⇒v ⇒w)) ⟩
    labels (𝒮 (if (e && e') then s else nop) k E)
  ∎
