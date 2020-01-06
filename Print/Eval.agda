module Print.Eval where

open import C
open import Print.AST
open import Data.Integer
open import Data.Bool renaming (Bool to 𝔹 ; if_then_else_ to If_Then_Else_)
open import Data.Vec
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
import Level

open import C.Properties.ReductionSemantics ⦃ AST-C ⦄

judge : ∀ { α } { v : ⟦ α ⟧ } → Env → Expr α → Value α v

step : State → State
step s = {!!}

AST-Semantics : Semantics
Semantics._↝_ AST-Semantics S₁ S₂ = step S₁ ≡ S₂

eval-statement : ∀ { α } → (IRef α → IStatement) → ⟦ α ⟧
eval-statement s = {!Semantics._↝_ AST-Semantics!}

eval : ∀ { α } → (∀ ⦃ ℐ : C ⦄ → C.Ref ℐ α → C.Statement ℐ) → ⟦ α ⟧
eval s = eval-statement (s ⦃ AST-C ⦄)
