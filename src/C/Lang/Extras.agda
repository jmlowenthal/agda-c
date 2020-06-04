open import C.Lang
open import Data.Char as Char using (Char ; toℕ ; fromℕ)
open import Data.Integer as ℤ using (+_)
open import Data.List as List using (List ; [] ; _∷_)
open import Data.Nat as ℕ using (ℕ)
open import Data.String as String using (String ; toList ; fromList ; _++_)

import Data.Nat.Show as ℕs

module C.Lang.Extras ⦃ _ : Lang ⦄ where

open Lang ⦃ ... ⦄

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

show : ∀ { α } → Expr α → Statement
show {Int} e =
  decl Int λ i →
  decl Int λ j →
  decl Bool λ cond →
  cond ≔ true ；
  i ≔ e ；
  if (★ i) < ⟪ + 0 ⟫ then (
    putstr "-" ；
    i ≔ ⟪ + 0 ⟫ - (★ i))
  else
    nop ；
  while (★ cond) then (
    j ≔ (★ i) / ⟪ + 10 ⟫ ；
    putchar ((★ i) - ((★ j) * ⟪ + 10 ⟫) + ⟪ + 48 ⟫) ；
    i ≔ ★ j ；
    cond ≔ ! ((★ i) == ⟪ + 0 ⟫))
show {Bool} e = if e then putstr "true" else putstr "false"
show {Array α n} e = nop
