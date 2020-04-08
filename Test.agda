open import C.Base
open import C.Extras
open import Data.Nat as ℕ using (ℕ)
open import Data.Integer as ℤ using (+_)
open import Data.String as String using (String ; _++_)
open import IO
open import Print.Print
open import Streams.Base
open import Streams.Claims

import Data.Nat.Show as ℕs

module Test where

open C ⦃ ... ⦄

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

_←⁺_ : ∀ ⦃ _ : C ⦄ { α n } → Ref (Array α n) → Stream α → Statement
_←⁺_ {α} {n} arr s =
  decl Int λ i →
  i ≔ ⟪ + 0 ⟫ ；
  iter
    (λ e →
       arr [ ★ i ] ≔ e ；
       i ≔ (★ i) + ⟪ + 1 ⟫)
    (take ⟪ + n ⟫ s)

generate-test : ∀ ⦃ _ : C ⦄ { α } → String → Claim (Expr α) → Ref Int → Statement
generate-test {α} name (s ≈ t) r =
  let n = 10 in
    putstr name ；
    decl (Array α n) λ S →
    S ←⁺ s ；
    decl (Array α n) λ T →
    T ←⁺ t ；
    if-equal S T
      (putstr-coloured " [PASSED]" 32)
    -- else
      (putstr-coloured " [FAILED]" 31 ； r ≔ ★ r - ⟪ + 1 ⟫)

main =
  run (IO.putStr ex)
  where
    ex : String
    ex = print-main-return (λ r →
      r ≔ ⟪ + 0 ⟫ ；
      putstr "Running tests:\n" ；
      generate-test "map'=map" (map'≅map (λ e → e) (iota 0)) r ；
      generate-test "map-map" (map-map (iota 0) (λ e → e * ⟪ + 2 ⟫) (λ e → e + ⟪ + 2 ⟫)) r ；
      generate-test "map-id" (map-id (iota 0)) r ；
      generate-test "filter-filter" (filter-filter (iota 0) (λ e → (e % ⟪ + 2 ⟫) == ⟪ + 0 ⟫) λ e → (e % ⟪ + 5 ⟫) == ⟪ + 0 ⟫) r)
