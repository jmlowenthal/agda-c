open import CMinor.Lang.Lang
open import Data.Vec

open import Data.Nat.Binary using (4ᵇ ; 1ᵇ)
import Level

module CMinor.Example {a b c d e f g} (L : Lang a b c d e f g) where

-- Example from Leroy et al
-- ```
-- // C:
-- double average(int arr[], int sz) {
--   double s; int i;
--   for (i = 0, s = 0; i < sz; i++)
--     s += arr[i];
--   return s / sz;
-- }
-- // CMinor:
-- "average"(arr, sz) : int, int -> float {
-- vars s, i; stacksize 0;
-- s = 0.0; i = 0;
-- block { loop {
--   if (i >= sz) exit(0);
--   s = s +. floatofint(int32[arr + i * 4]);
--   i = i + 1;
-- } }
-- return s /. floatofint(sz)
-- ```
open Lang L

-- The syntax of our CMinor impl is very cumbersome (for now)
average : (Int ∷ Int ∷ []) ⇒ Float
average = define-function _ _ (Float ∷ Int ∷ []) 0
  (λ arr sz →
    (λ s i →
      Level.lift (
        (block (loop (
          sequence
            (if-else (cmp->= (id i) (id sz)) (exit 0) skip)
            (sequence
              (assignment s (addf (id s) (floatofint (mem-read Int (add (id arr) (mul (id i) (cst (cst-int 4ᵇ))))))))
              (assignment i (add (id i) (cst (cst-int 1ᵇ))))))))
      )
    )
  )
