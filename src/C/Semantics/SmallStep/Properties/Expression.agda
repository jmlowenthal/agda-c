open import Algebra.FunctionProperties
open import C.Lang
open import C.Semantics.SmallStep.Model
open import Data.Integer as ℤ using (ℤ ; +_)
open import Data.Product
open import Relation.Binary.PropositionalEquality

import Data.Integer.Properties as ℤₚ

module C.Semantics.SmallStep.Properties.Expression ⦃ _ : Lang ⦄ ⦃ _ : Semantics ⦄ where

open Lang ⦃ ... ⦄
open Semantics ⦃ ... ⦄
open ≡-Reasoning

+-left-id : ∀ (x : Expr Int) → ⟪ + 0 ⟫ + x ≅ₑ x
+-left-id e {E} {v} {w} 0+e⇒v e⇒w =
  let 0+e⇒0+w = +-eval (nat (+ 0)) e⇒w
      v≡0+w = ⊢-det 0+e⇒v 0+e⇒0+w in
  begin
    v
    ≡⟨ v≡0+w ⟩
    + 0 ℤ.+ w
    ≡⟨ ℤₚ.+-identityˡ w ⟩
    w
  ∎

+-right-id : RightIdentity _≅ₑ_ (⟪ + 0 ⟫) _+_
+-right-id e {E} {v} {w} e+0⇒v e⇒w =
  let e+0⇒w+0 = +-eval e⇒w (nat (+ 0)) in
  let v≡w+0 = ⊢-det e+0⇒v e+0⇒w+0 in
  begin
    v
    ≡⟨ v≡w+0 ⟩
    w ℤ.+ + 0
    ≡⟨ ℤₚ.+-identityʳ w ⟩
    w
  ∎

+-id : Identity _≅ₑ_ (⟪ + 0 ⟫) _+_
+-id = +-left-id , +-right-id

+-assoc : Associative _≅ₑ_ _+_
+-assoc x y z {E} {v} {w} [x+y]+z⇒v x+[y+z]⇒w =
  let x' , ⇒x' = ⊢-total {e = x} in
  let y' , ⇒y' = ⊢-total {e = y} in
  let z' , ⇒z' = ⊢-total {e = z} in
  begin
    v
    ≡⟨ ⊢-det [x+y]+z⇒v (+-eval (+-eval ⇒x' ⇒y') ⇒z') ⟩
    (x' ℤ.+ y') ℤ.+ z'
    ≡⟨ ℤₚ.+-assoc x' y' z' ⟩
    x' ℤ.+ (y' ℤ.+ z')
    ≡⟨ ⊢-det (+-eval ⇒x' (+-eval ⇒y' ⇒z')) x+[y+z]⇒w ⟩
    w
  ∎

+-comm : Commutative _≅ₑ_ _+_
+-comm x y {E} {v} {w} x+y⇒v y+x⇒w =
  let x' , ⇒x' = ⊢-total {e = x} in
  let y' , ⇒y' = ⊢-total {e = y} in
  begin
    v
    ≡⟨ ⊢-det x+y⇒v (+-eval ⇒x' ⇒y') ⟩
    x' ℤ.+ y'
    ≡⟨ ℤₚ.+-comm x' y' ⟩
    y' ℤ.+ x'
    ≡⟨ ⊢-det (+-eval ⇒y' ⇒x') y+x⇒w ⟩
    w
  ∎

-- *-id : Identity _≅ₑ_ (⟨ + 1 ⟩) _*_
-- *-zero : Zero _≅ₑ_ (⟨ + 0 ⟩) _*_
-- *-assoc : Associative _≅ₑ_ _*_
-- *-commute : Commutative _≅ₑ_ _*_
-- ∸-id : Identity _≅ₑ_ (⟨ + 0 ⟩) _-_
-- /-id : Identity _≅ₑ_ (⟨ + 1 ⟩) _/_
-- -- TODO: algebra properties of _<_ _<=_ _>_ _>=_ _==_ using standard library algebra
-- <-trans : ∀ { x y z : Expr Int } → x < y ≅ₑ true → y < z ≅ₑ true → x < z ≅ₑ true
-- ||-id : Identity _≅ₑ_ false _||_
-- ||-zero : Zero _≅ₑ_ true _||_
-- ||-assoc : Associative _≅ₑ_ _||_
-- ||-commute : Commutative _≅ₑ_ _||_
-- &&-id : Identity _≅ₑ_ true _&&_
-- &&-zero : Zero _≅ₑ_ false _&&_
-- &&-assoc : Associative _≅ₑ_ _&&_
-- &&-commute : Commutative _≅ₑ_ _&&_ 
