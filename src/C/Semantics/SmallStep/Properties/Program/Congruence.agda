open import C.Lang
open import C.Semantics.SmallStep.Model
open import C.Semantics.SmallStep.Properties.Program.Equivalence

open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Data.List
open import Relation.Nullary
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Codata.Musical.Notation
open import Codata.Musical.Colist
open import Data.Nat
open import Data.Nat.Properties
open import Data.Integer using (+_)

module C.Semantics.SmallStep.Properties.Program.Congruence where

open Lang ⦃ ... ⦄
open Semantics ⦃ ... ⦄

Statement* = ∀ ⦃ ℒ : Lang ⦄ → Statement

_≅ₚ*_ : Statement* → Statement* → Set₁
x ≅ₚ* y = ∀ ⦃ ℒ : Lang ⦄ ⦃ ℳ : Semantics ⦄ → x ≅ₚ y

≅ₚ-cong : ∀ (f : Statement* → Statement*) (x y : Statement*) → x ≅ₚ* y → f x ≅ₚ* f y
≅ₚ-cong f x y x~y = {!!}

open ≅-Reasoning

_ : ∀ ⦃ _ : Lang ⦄ ⦃ _ : Semantics ⦄ →
  while true then nop ≅ₚ while true then (nop ； nop)
_ =
  begin
    (while true then nop)
    ≅˘⟨
      ≅ₚ-cong
        (λ ● → while true then ●)
        (nop ； nop)
        nop
        (↝*⇒≅ₛ (↝-seq ◅ ♯ (↝-nop ◅ ♯ ε)))
    ⟩
    (while true then (nop ； nop))
  ∎
