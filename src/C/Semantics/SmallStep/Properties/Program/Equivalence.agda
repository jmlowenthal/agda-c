open import C.Lang
open import C.Semantics.SmallStep.Model
open import C.Semantics.SmallStep.Properties.Program.Reduction
open import Codata.Musical.Colist as Colist hiding ([_])
open import Codata.Musical.Notation
open import Data.Empty
open import Data.List as L hiding ([_] ; _++_)
open import Data.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

import Data.Nat as ℕ
import Level

open Lang ⦃ ... ⦄
open Semantics ⦃ ... ⦄

module C.Semantics.SmallStep.Properties.Program.Equivalence ⦃ _ : Lang ⦄ ⦃ _ : Semantics ⦄ where

≅ₛ-refl : Reflexive _≅ₛ_
≅ₛ-refl = [≈]-refl

≅ₛ-sym : Symmetric _≅ₛ_
≅ₛ-sym = [≈]-sym

≅ₛ-trans : Transitive _≅ₛ_
≅ₛ-trans = [≈]-trans

≅ₛ-equiv : IsEquivalence _≅ₛ_
≅ₛ-equiv = record { refl = ≅ₛ-refl ; sym = ≅ₛ-sym ; trans = ≅ₛ-trans }

↝⇒≅ₛ : ∀ { A B } → A ~[ τ ]↝ B → A ≅ₛ B
↝⇒≅ₛ {A} {B} A↝B with reduce A
... | [] = ⊥-elim (↝-Ω A↝B)
... | A↝C ∷ C↝
  with ↝-det A↝B A↝C
... | refl , refl = left ignore-τ (♯ [≈]-reflexive (reduce-det (♭ C↝) (reduce B)))

↝*⇒≅ₛ : ∀ { A B n } → A ~[ fromList (L.replicate n τ) ]↝* B → A ≅ₛ B
↝*⇒≅ₛ {n = ℕ.zero} ε = ≅ₛ-refl
↝*⇒≅ₛ {n = ℕ.suc n} (A↝Y ◅ Y↝*B) = ≅ₛ-trans (↝⇒≅ₛ A↝Y) (↝*⇒≅ₛ {n = n} (♭ Y↝*B))

postulate cont-equiv : ∀ { a b c d E } → labels (𝒮 nop a E) [≈] labels (𝒮 nop c E) → (∀ E' → labels (𝒮 nop b E') [≈] labels (𝒮 nop d E')) → labels (𝒮 nop (a L.++ b) E) [≈] labels (𝒮 nop (c L.++ d) E)

postulate ↝*-irr-cont : ∀ { x y : Statement } { k k' E e } → 𝒮 x k E ~[ e ]↝* 𝒮 y k E → 𝒮 x k' E ~[ e ]↝* 𝒮 y k' E
postulate cont-comb : ∀ { s : Statement } { E E' e f k X } → 𝒮 s [] E ~[ e ]↝* 𝒮 nop [] E' → 𝒮 nop k E' ~[ f ]↝* X → 𝒮 s k E ~[ e ++ f ]↝* X
postulate ≅ₛ-while-true : ∀ { s : Statement } { k k' E } → 𝒮 (while true then s) k E ≅ₛ 𝒮 (while true then s) k' E

infix 0 _≅ₚ_
_≅ₚ_ : Rel Statement Level.zero
_≅ₚ_ x y = ∀ { k E } → 𝒮 x k E ≅ₛ 𝒮 y k E

≅ₚ-refl : Reflexive _≅ₚ_
≅ₚ-refl = ≅ₛ-refl

≅ₚ-sym : Symmetric _≅ₚ_
≅ₚ-sym i~j = ≅ₛ-sym i~j

≅ₚ-trans : Transitive _≅ₚ_
≅ₚ-trans i~j j~k = ≅ₛ-trans i~j j~k

≅ₚ-equiv : IsEquivalence _≅ₚ_
≅ₚ-equiv = record { refl = ≅ₚ-refl ; sym = ≅ₚ-sym ; trans = ≅ₚ-trans }

≅ₚ-setoid : Setoid _ _
≅ₚ-setoid = record {
  Carrier = Statement ;
  _≈_ = _≅ₚ_ ;
  isEquivalence = ≅ₚ-equiv }

import Relation.Binary.Reasoning.Setoid as Reasoning
module ≅-Reasoning = Reasoning ≅ₚ-setoid
  renaming (_≈⟨_⟩_ to _≅⟨_⟩_ ; _≈˘⟨_⟩_ to _≅˘⟨_⟩_)

module [≈]-Reasoning = Reasoning [≈]-setoid
