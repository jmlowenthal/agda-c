{-# OPTIONS --safe --exact-split --without-K #-}

module C.Lang.Lang where

import Data.Nat as ℕ
open import Data.Product

open import Data.Integer as ℤ using (ℤ)
open import Relation.Binary using (Rel ; IsPartialOrder)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Nullary.Decidable
open import Relation.Nullary.Product

data c_type : Set where
  Int Bool : c_type -- TODO: Float type
  Array : c_type → (n : ℕ.ℕ) → c_type

Array-inj : ∀ {m n x y} → Array m x ≡ Array n y → m ≡ n × x ≡ y
Array-inj refl = refl , refl

_≟_ : ∀ (x y : c_type) → Dec (x ≡ y)
Int       ≟ Int       = yes refl
Int       ≟ Bool      = no λ ()
Int       ≟ Array _ _ = no λ ()
Bool      ≟ Int       = no λ ()
Bool      ≟ Bool      = yes refl
Bool      ≟ Array _ _ = no λ ()
Array _ _ ≟ Int       = no λ ()
Array _ _ ≟ Bool      = no λ ()
Array x m ≟ Array y n = map′ (uncurry (cong₂ Array)) Array-inj (x ≟ y ×-dec m ℕ.≟ n)

record Lang : Set₁ where
  field
    Expr : c_type → Set
    Statement : Set
    Ref : c_type → Set
    ⟪_⟫ : ℤ → Expr Int
    _+_ _*_ _-_ _/_ : Expr Int → Expr Int → Expr Int
    _<_ _<=_ _>_ _>=_ _==_ : Expr Int → Expr Int → Expr Bool
    true false : Expr Bool
    _||_ _&&_ : Expr Bool → Expr Bool → Expr Bool
    !_ : Expr Bool → Expr Bool
    _⁇_∷_ : ∀ { α } → Expr Bool → Expr α → Expr α → Expr α
    if_then_else_ : Expr Bool → Statement → Statement → Statement
    _[_] : ∀ { α n } → Ref (Array α n) → (i : Expr Int) → Ref α
    ★_ : ∀ { α } → Ref α → Expr α
    _≔_ : ∀ { α } → Ref α → Expr α → Statement
    _；_ : Statement → Statement → Statement
    decl : (α : c_type) → (Ref α → Statement) → Statement
    nop : Statement
    for_to_then_ : Expr Int → Expr Int → (Ref Int → Statement) → Statement
    while_then_ : Expr Bool → Statement → Statement
    putchar : Expr Int → Statement

  _←_ : ∀ { α } → Ref α → (Ref α → Statement) → Statement
  x ← e = e x

  infixr 1 _；_
  infix 2 if_then_else_
  infix 3 _≔_
  infix 4 _⁇_∷_
  infix 5 _/_
  infix 6 _*_
  infix 7 _+_
  infix 8 _-_
  infix 9 ★_ _||_ _&&_ _[_]
