module Print.Eval where

open import C
open import Data.Bool renaming (Bool to 𝔹 ; if_then_else_ to If_Then_Else_)
open import Data.Integer as ℤ using (ℤ)
open import Data.Maybe
open import Data.Product
open import Data.Unit
open import Data.Vec
open import Print.AST
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable

import Data.Integer.Properties as ℤₚ
import Data.Integer.DivMod as ℤ÷
import Data.Nat as ℕ
import Level

divide : ℤ → ℤ → ℤ
divide x (ℤ.pos 0) = ℤ.+ 0 -- Implementation defined
divide x y@(ℤ.+[1+ n ]) = (x ℤ÷.div y) {tt}
divide x y@(ℤ.negsuc n) = (x ℤ÷.div y) {tt}

open import C.Properties.State ⦃ AST-C ⦄
open import C.Properties.Musical ⦃ AST-C ⦄

judge : ∀ { α } → Env → C.Expr AST-C α → ⟦ α ⟧
judge E (lit x) = x
judge E (add x y) = (judge E x) ℤ.+ (judge E y)
judge E (mul x y) = (judge E x) ℤ.* (judge E y)
judge E (sub x y) = (judge E x) ℤ.- (judge E y)
judge E (div x y) = divide (judge E x) (judge E y)
judge E (lt x y) = ⌊ (judge E x) ℤ.<? (judge E y) ⌋
judge E (lte x y) = ⌊ (judge E x) ℤ.≤? (judge E y) ⌋
judge E (gt x y) = ⌊ (judge E y) ℤ.<? (judge E x) ⌋
judge E (gte x y) = ⌊ (judge E y) ℤ.≤? (judge E x) ⌋
judge E (eq x y) = ⌊ (judge E x) ℤ.≟ (judge E y) ⌋
judge E true = true
judge E false = false
judge E (or x y) = (judge E x) ∨ (judge E y)
judge E (and x y) = (judge E x) ∧ (judge E y)
judge E (IExpr.not e) = Data.Bool.not (judge E e)
judge E (tenary c x y) with judge E c
... | true = judge E x
... | false = judge E y
judge (y , E) (deref x) = judge E (deref x)
judge (y Env.↦ v , E) (deref x) = {!!}

-- This shouldn't be hit provided we have closed expressions (TODO: prove it)
judge ε (deref x) = default
  where
    default : ∀ { α } → ⟦ α ⟧
    default {Int} = ℤ.+ 0
    default {Bool} = false
    default {Array α ℕ.zero} = []
    default {Array α (ℕ.suc n)} = default ∷ default

step : State → Maybe (Label × State)
step s = {!!}

AST-Semantics : Semantics
Semantics._⊢_⇒_ AST-Semantics E e v = judge E e ≡ v
Semantics._~[_]↝_ AST-Semantics S₁ e S₂ = step S₁ ≡ just (e , S₂)
Semantics.reduce AST-Semantics S = {!!}
Semantics.⊢-total AST-Semantics {_} {E} {e} = judge E e , refl
Semantics.⊢-det AST-Semantics refl refl = refl
Semantics.⊢-weakening AST-Semantics refl = {!!}
Semantics.⊢-exchange AST-Semantics x = {!!}
Semantics.nat AST-Semantics n = {!!}
Semantics.deref AST-Semantics x = {!!}
Semantics.+-eval AST-Semantics x x₁ = {!!}
Semantics.*-eval AST-Semantics x x₁ = {!!}
Semantics.∸-eval AST-Semantics x x₁ = {!!}
Semantics./-eval AST-Semantics x x₁ y≠0 = {!!}
Semantics.true-eval AST-Semantics = {!!}
Semantics.false-eval AST-Semantics = {!!}
Semantics.||-eval AST-Semantics x x₁ = {!!}
Semantics.&&-eval AST-Semantics x x₁ = {!!}
Semantics.⁇-eval-t AST-Semantics x x₁ = {!!}
Semantics.⁇-eval-f AST-Semantics x x₁ = {!!}
Semantics.↝-if-true AST-Semantics x = {!!}
Semantics.↝-if-false AST-Semantics x = {!!}
Semantics.↝-assignment AST-Semantics x = {!!}
Semantics.↝-seq AST-Semantics = {!!}
Semantics.↝-decl AST-Semantics = {!!}
Semantics.↝-nop AST-Semantics = {!!}
Semantics.↝-stuck AST-Semantics = {!!}
Semantics.↝-Ω AST-Semantics x = {!!}
Semantics.↝-for AST-Semantics = {!!}
Semantics.↝-while AST-Semantics = {!!}
Semantics.↝-putchar AST-Semantics x = {!!}
Semantics.↝-det AST-Semantics x x₁ = {!!}
Semantics.↝-progress AST-Semantics x k E = {!!}
Semantics.↝-irr-cont AST-Semantics x = {!!}
Semantics.≅ₛ-subst AST-Semantics x x₁ x₂ = {!!}
Semantics.≅ₛ-decl AST-Semantics = {!!}
Semantics.≅ₛ-cong AST-Semantics f x y x₁ = {!!}

eval-statement : ∀ { α } → (C.Ref AST-C α → C.Statement AST-C) → ⟦ α ⟧
eval-statement s = {!Semantics._~[_]↝_ AST-Semantics!}

eval : ∀ { α } → (∀ ⦃ ℐ : C ⦄ → C.Ref ℐ α → C.Statement ℐ) → ⟦ α ⟧
eval s = eval-statement (s ⦃ AST-C ⦄)
