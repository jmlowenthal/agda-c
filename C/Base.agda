module C.Base where

open import Data.Nat using (ℕ ; _≟_)
open import Data.Integer using (ℤ)
open import Relation.Binary using (Rel ; IsPartialOrder)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (Dec ; yes ; no)

data c_type : Set where
  Int Bool : c_type -- TODO: Float type
  Array : c_type → (n : ℕ) → c_type

≟-ctype : ∀ (x y : c_type) → Dec (x ≡ y)
≟-ctype Int Int = yes refl
≟-ctype Int Bool = no λ ()
≟-ctype Int (Array _ _) = no λ ()
≟-ctype Bool Int = no λ ()
≟-ctype Bool Bool = yes refl
≟-ctype Bool (Array _ -) = no λ ()
≟-ctype (Array _ _) Int = no λ ()
≟-ctype (Array _ _) Bool = no λ ()
≟-ctype (Array α n) (Array β m)
  with n ≟ m | ≟-ctype α β
... | no ¬p | _ = no (λ { refl → ¬p refl })
... | yes refl | no ¬p = no (λ { refl → ¬p refl })
... | yes refl | yes refl = yes refl

record C : Set₁ where
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

  infixr 0 _；_
  infix 1 if_then_else_
  infix 2 _≔_
  infix 3 _⁇_∷_
  infix 4 _/_
  infix 5 _*_
  infix 6 _+_
  infix 7 _-_
  infix 8 ★_ _||_ _&&_
  infix 9 _[_]
