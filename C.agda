module C where

open import Data.Nat using (ℕ)
open import Data.Integer using (ℤ)

data c_type : Set where
  Void Char Int Bool : c_type
  Array : c_type → (n : ℕ) → c_type

record C : Set₁ where
  field
    Code : c_type → Set
    Ref : c_type → Set
    --_≃_ : ∀ { α β } → Code α → Code β → Set
    --_≤_ : Code Int → Code Int → Set
    ⟨_⟩ : ℤ → Code Int
    _+_ _*_ _-_ _/_ : Code Int → Code Int → Code Int
    _<_ _<=_ _>_ _>=_ _==_ : Code Int → Code Int → Code Bool
    true false : Code Bool
    _||_ _&&_ : Code Bool → Code Bool → Code Bool
    if_then_else_ : ∀ { α } → Code Bool → Code α → Code α → Code α
    _[_] : ∀ { α n } → Ref (Array α n) → (i : Code Int) → Ref α
    ★_ : ∀ { α } → Ref α → Code α
    _≔_ : ∀ { α } → Ref α → Code α → Code Void
    _；_ : ∀ { α β } → Code α → Code β → Code β
    decl : (α : c_type) → ∀ { β } → (Ref α → Code β) → Code β
    nop : Code Void
    for_to_then_ : (l : Code Int) → (u : Code Int) → (Ref Int → Code Void) → Code Void
    while_then_ : Code Bool → Code Void → Code Void

  infixr 0 _；_
  infix 1 if_then_else_
  infix 2 _≔_
  infix 4 _/_
  infix 5 _*_
  infix 6 _+_
  infix 7 _-_
  infix 8 ★_ _||_ _&&_
  infix 9 _[_]
