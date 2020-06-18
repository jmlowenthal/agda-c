open import C.Lang
open import C.Semantics.SmallStep.Model
open import Data.Product using (∃ ; _,_ ; ∃-syntax ; proj₁ ; proj₂)
open import Relation.Binary
open import Codata.Musical.Notation

import Data.Nat as ℕ
import Level

module C.Semantics.SmallStep.Properties.Equivalence ⦃ _ : Lang ⦄ ⦃ _ : Semantics ⦄ where

open Lang ⦃ ... ⦄
open Semantics ⦃ ... ⦄

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
