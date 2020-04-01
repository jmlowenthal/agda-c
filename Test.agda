open import C
open import Data.Char as Char using (Char ; toℕ ; fromℕ)
open import Data.Integer as ℤ using (+_)
open import Data.List as List using (List ; [] ; _∷_)
open import Data.String as String using (String ; toList ; fromList ; _++_)
open import IO
open import Print.Print
open import Streams.Base
open import Streams.Claims

module Test where

open C.C ⦃ ... ⦄

putnl : ∀ ⦃ _ : C ⦄ → Statement
putnl = putchar ⟪ + (toℕ '\n') ⟫

putstr : ∀ ⦃ _ : C ⦄ → String → Statement
putstr s = putcharlist (toList s)
  where
    putcharlist : List Char → Statement
    putcharlist [] = nop
    putcharlist (h ∷ []) = putchar ⟪ + (toℕ h) ⟫
    putcharlist (h ∷ t@(_ ∷ _)) = putchar ⟪ + (toℕ h) ⟫ ； putcharlist t

if-equal : ∀ ⦃ _ : C ⦄ { α } → Ref α → Ref α → Statement → Statement → Statement
if-equal {Int} x y t f = if (★ x) == (★ y) then t else f
if-equal {Bool} x y t f = if ((★ x) && (★ y)) || ((! (★ x)) && (! (★ y))) then t else f
if-equal {Array α n} x y t f =
  decl Bool λ eq →
  eq ≔ true ；
  decl Int λ i →
  i ≔ ⟪ + 0 ⟫ ；
  while ((★ eq) && ((★ i) < ⟪ + n ⟫)) then (
    if-equal {α} (x [ ★ i ]) (y [ ★ i ]) nop (eq ≔ false) ；
    i ≔ ★ i + ⟪ + 1 ⟫
  ) ；
  if ★ eq then t else f

generate-test : ∀ ⦃ _ : C ⦄ { α } → Claim (Expr α) → Statement
generate-test {α} (s ≈ t) =
  let n = 10 in
    putstr ("Validating that the first " ++ fromList (fromℕ n ∷ []) ++ " elements are equal") ；
    decl (Array α n) λ S →
    decl Int λ i →
    i ≔ ⟪ + 0 ⟫ ；
    iter (λ e → S [ (★ i) ] ≔ e ； i ≔ (★ i) + ⟪ + 1 ⟫) (take ⟪ + n ⟫ s) ；
    decl (Array α n) λ T →
    i ≔ ⟪ + 0 ⟫ ；
    iter (λ e → T [ ★ i ] ≔ e ； i ≔ (★ i) + ⟪ + 1 ⟫) (take ⟪ + n ⟫ t) ；
    if-equal S T
      (putstr "[PASSED]\n")
    -- else
      (putstr "[FAILED]\n")

main =
  run (IO.putStr ex)
  where
    ex : String
    ex = print-main (
      generate-test (map'≅map (λ e → e) (iota 0)))
