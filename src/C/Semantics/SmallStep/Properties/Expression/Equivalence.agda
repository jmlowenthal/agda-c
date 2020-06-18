open import C.Lang
open import C.Semantics.SmallStep.Model
open import Data.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

import Level

open Lang ⦃ ... ⦄
open Semantics ⦃ ... ⦄

module C.Semantics.SmallStep.Properties.Expression.Equivalence ⦃ _ : Lang ⦄ ⦃ _ : Semantics ⦄ where

infix 0 _≅ₑ_
_≅ₑ_ : ∀ { α } → Rel (Expr α) Level.zero
_≅ₑ_ { α } x y = ∀ { E : Env } { v w : ⟦ α ⟧ }
  → (E ⊢ x ⇒ v) → (E ⊢ y ⇒ w) → (v ≡ w)

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
