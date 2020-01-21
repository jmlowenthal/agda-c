module Print.Eval where

open import C
open import Print.AST
open import Data.Integer as ℤ using (ℤ)
open import Data.Bool renaming (Bool to 𝔹 ; if_then_else_ to If_Then_Else_)
open import Data.Product
open import Data.Vec
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Unit

import Data.Integer.Properties as ℤₚ
import Data.Integer.DivMod as ℤ÷
import Level

open import C.Properties.FreeVariables ⦃ AST-C ⦄

divide : ℤ → ℤ → ℤ
divide x (ℤ.pos 0) = ℤ.+ 0 -- Implementation defined
divide x y@(ℤ.+[1+ n ]) = (x ℤ÷.div y) {tt}
divide x y@(ℤ.negsuc n) = (x ℤ÷.div y) {tt}

data _<<_ : Rel (∃ λ β → IRef β) Level.zero where
  lit<<lit : ∀ { x y } → x ℤ.< y → (Int , lit x) << (Int , lit y)

isStrictTotalOrder : IsStrictTotalOrder _≡_ _<<_

AST-FV : FreeVariables isStrictTotalOrder

open import C.Properties.State ⦃ AST-C ⦄ ⦃ AST-FV ⦄
open import C.Properties.ReductionSemantics ⦃ AST-C ⦄ ⦃ AST-FV ⦄

judge : ∀ { α } { v : ⟦ α ⟧ } → Env → IExpr α → Value α v

step : State → State
step s = {!!}

AST-Semantics : Semantics
Semantics._↝_ AST-Semantics S₁ S₂ = step S₁ ≡ S₂

eval-statement : ∀ { α } → (IRef α → IStatement) → ⟦ α ⟧
eval-statement s = {!Semantics._↝_ AST-Semantics!}

eval : ∀ { α } → (∀ ⦃ ℐ : C ⦄ → C.Ref ℐ α → C.Statement ℐ) → ⟦ α ⟧
eval s = eval-statement (s ⦃ AST-C ⦄)
