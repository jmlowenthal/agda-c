open import C.Base
open import Data.Char as Char using (Char ; toℕ ; fromℕ)
open import Data.Integer as ℤ using (+_)
open import Data.List as List using (List ; [] ; _∷_)
open import Data.Nat as ℕ using (ℕ)
open import Data.String as String using (String ; toList ; fromList ; _++_)

import Data.Nat.Show as ℕs

module C.Extras ⦃ _ : C ⦄ where

open C ⦃ ... ⦄

_%_ : Expr Int → Expr Int → Expr Int
x % y = x - ((x / y) * y)

putnl : Statement
putnl = putchar ⟪ + (toℕ '\n') ⟫

putstr : String → Statement
putstr s = putcharlist (toList s)
  where
    putcharlist : List Char → Statement
    putcharlist [] = nop
    putcharlist (h ∷ []) = putchar ⟪ + (toℕ h) ⟫
    putcharlist (h ∷ t@(_ ∷ _)) = putchar ⟪ + (toℕ h) ⟫ ； putcharlist t

putstr-coloured : String → ℕ → Statement
putstr-coloured s n = 
  putchar ⟪ + 27 ⟫ ；
  putstr "[;" ；
  putstr (ℕs.show n) ；
  putstr "m " ；
  putstr s ；
  putchar ⟪ + 27 ⟫ ；
  putstr "[0m\n"
