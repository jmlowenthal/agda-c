open import C.Lang
open import C.Semantics.SmallStep.Model
open import C.Semantics.SmallStep.Properties.Program.Equivalence
open import Data.Product.Nary.NonDependent
open import Function.Nary.NonDependent
open import Data.Product.Nary.NonDependent
open import Relation.Binary
open import Relation.Binary.Indexed.Heterogeneous.Construct.Trivial as Trivial
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality

import Level

module C.Semantics.SmallStep.Properties.Program.Congruence where

open Lang ⦃ ... ⦄
open Semantics ⦃ ... ⦄

Statement* = ∀ ⦃ ℒ : Lang ⦄ → Statement

_≅ₚ*_ : Statement* → Statement* → Set₁
x ≅ₚ* y = ∀ ⦃ ℒ : Lang ⦄ ⦃ ℳ : Semantics ⦄ → x ≅ₚ y

apply : ∀ { n L } { V : Sets n L } → (V ⇉ Statement*) → (Product _ V → Statement*)
apply {zero} f _ = f
apply {suc zero} f x = f x
apply {suc (suc n)} {V = H , T} f (h , t) = apply {V = T} (f h) t

L0 : ∀ { n } → Levels n
L0 {zero} = _
L0 {suc n} = Level.zero , L0

lemma : ∀ { n } → ⨆ n L0 ≡ Level.zero
lemma {zero} = refl
lemma {suc n} rewrite lemma {n} = refl

≅ₚ-cong :
  ∀ (V : Set) (f : ∀ ⦃ ℐ : Lang ⦄ → (V → Statement) → Statement)
    (x y : ∀ ⦃ ℐ : Lang ⦄ → V → Statement) →
  (∀ v → x v ≅ₚ* y v) → f x ≅ₚ* f y
≅ₚ-cong V f x y p {k} {E} = ≅ₛ-cong V f x y (λ v _ _ → p v) k E
