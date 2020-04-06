open import C.Base
open import C.Extras
open import Data.Integer as ℤ using (+_)
open import Data.List as List using (List ; _∷_ ; [])
open import Data.Nat as ℕ using (ℕ)
open import Data.Product as Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.String as String using (String ; _++_)
open import Data.Vec as Vec using (Vec ; _∷_ ; [])
open import IO
open import Print.Print
open import Streams

import Data.Nat.Show as ℕs
import Data.Fin as Fin
import Data.Nat.DivMod as ℕ÷

module Benchmark where

open C ⦃ ... ⦄

-- Kiselyov et al., Section §7:
--
-- - sum: the simplest of_arr arr ▹ sum pipeline, summing the elements of an array;
-- - sumOfSquares: our running example from §4.2 on;
-- - sumOfSquaresEven: the sumOfSquares benchmark with added filter, summing the squares of only the even array elements;
-- - cart: ∑ xᵢ yⱼ, using flat_map to build the outer-product stream;
-- - maps: consecutive map operations with integer multiplication;
-- - filters: consecutive filter operations using integer comparison;
-- - dotProduct: compute dot product of two arrays using zip_with;
-- - flatMapafterzipWith: compute ∑ (xᵢ+xᵢ) yⱼ, like cart above, doubling the x array via zip_with (+) with itself;
-- - zipWithafterflatMap: zip_with of two streams one of whichis the result of flat_map;
-- - flatmaptake: flat_map followed by take"
--
-- Input: All tests were run with the same input set. For the sum, sumOfSquares, sumOfSquaresEven, maps, filters we used an array of N = 100,000,000 small integers: xᵢ = i mod 10. The cart test iterates over two arrays. An outer one of 10,000,000 integers and an inner one of 10. For the dotProduct we used 10,000,000 integers, for the flatMap_after_zipWith 10,000, for the zipWith_after_flatMap 10,000,000 and for the flatmap_take N numbers sub-sized by 20% of N."

module Tests ⦃ _ : C ⦄ where

  sum : ∀ { n } → Vec (Expr Int) n → Statement
  sum arr =
    decl Int λ r →
    r ← fold _+_ ⟪ + 0 ⟫ (ofArr arr)

  sumOfSquares : ∀ { n } → Vec (Expr Int) n → Statement
  sumOfSquares arr =
    decl Int λ r →
    r ← fold _+_ ⟪ + 0 ⟫
      (ofArr arr
        ▹ map (λ a → a * a))

  sumOfSquaresEven : ∀ { n } → Vec (Expr Int) n → Statement
  sumOfSquaresEven arr =
    decl Int λ r →
    r ← fold _+_ ⟪ + 0 ⟫
      (ofArr arr
        ▹ filter (λ e → (e % ⟪ + 2 ⟫) == ⟪ + 0 ⟫)
        ▹ map (λ a → a * a))

  -- Sum over Cartesian-/outer-product
  cart : ∀ { n m } → Vec (Expr Int) n → Vec (Expr Int) m → Statement
  cart x y =
    decl Int λ r →
    r ← fold _+_ ⟪ + 0 ⟫
      (ofArr x
        ▹ flatmap (λ i → ofArr y ▹ map (λ j → i * j)))

  maps : ∀ { n } → Vec (Expr Int) n → Statement
  maps arr =
    iter (λ _ → nop)
      (ofArr arr
        ▹ map (λ e → e * ⟪ + 2 ⟫)
        ▹ map (λ e → e * ⟪ + 3 ⟫))

  filters : ∀ { n } → Vec (Expr Int) n → Statement
  filters arr =
    iter (λ _ → nop)
      (ofArr arr
        ▹ filter (λ e → ! (e == ⟪ + 5 ⟫))
        ▹ filter (λ e → ! (e == ⟪ + 10 ⟫)))

  dotProduct : ∀ { n } → Vec (Expr Int) n → Vec (Expr Int) n → Statement
  dotProduct x y =
    decl Int λ r →
    r ← fold _+_ ⟪ + 0 ⟫
      (zipWith (λ i j → i * j) (ofArr x) (ofArr y) {ℕ.z≤n})

  flatmap-after-zipWith : ∀ { n m } → Vec (Expr Int) n → Vec (Expr Int) m → Statement
  flatmap-after-zipWith x y =
    iter (λ _ → nop)
      (zipWith _+_ (ofArr x) (ofArr x) {ℕ.z≤n}
        ▹ flatmap (λ i → ofArr y ▹ map (λ j → i * j)))

  zipWith-after-flatmap : ∀ { n } → Vec (Expr Int) (n ℕ.* n) → Vec (Expr Int) n → Statement
  zipWith-after-flatmap x y =
    iter (λ _ → nop)
      (zipWith _+_
        (ofArr x)
        (flatmap (λ e → ofArr y ▹ map (λ a → a + e)) (ofArr y))
        {ℕ.s≤s ℕ.z≤n})

  flatmap-take : ∀ { n m } → Vec (Expr Int) n → Vec (Expr Int) m → ℕ → Statement
  flatmap-take x y n =
    iter (λ _ → nop)
      (ofArr x
        ▹ flatmap (λ a → ofArr y ▹ map (λ b → a + b))
        ▹ take ⟪ + n ⟫)

benchmark-function : String → (∀ ⦃ _ : C ⦄ → Statement) → String
benchmark-function name body = 
  "/* BENCHMARK(" ++ name ++ ") */\n"
  ++ print-func _ name [] body 

main =
  run (IO.putStr ex)
  where
    gen : ∀ ⦃ _ : C ⦄ n → Vec (Expr Int) n
    gen _ = Vec.tabulate (λ n → ⟪ + ((Fin.toℕ n) ℕ÷.% 10) ⟫)
    ex : String
    ex =
      "#include <stdio.h>\n"
      ++ 
        -- void "sum" []
        --   (Tests.sum (gen 100000000)) ∷
        -- void "sumOfSquares" []
        --   (Tests.sumOfSquares (gen 100000000)) ∷
        -- void "sumOfSquaresEven" []
        --   (Tests.sumOfSquaresEven (gen 100000000)) ∷
        -- void "cart" []
        --   (Tests.cart (gen 10000000) (gen 10)) ∷
        -- void "maps" []
        --   (Tests.maps (gen 100000000)) ∷
        -- void "filters" []
        --   (Tests.filters (gen 100000000)) ∷
        -- void "dotProduct" []
        --   (Tests.dotProduct (gen 10000000) (gen 10000000)) ∷
        -- void "flatmap_after_zipWith" []
        --   (Tests.flatmap-after-zipWith (gen 10000) (gen 10000)) ∷
        -- void "zipWith_after_flatmap" []
        --   (Tests.zipWith-after-flatmap (gen _) (gen 10000)) ∷
        -- void "flatmap_take" []
        --   (Tests.flatmap-take (gen 10000) (gen 10000) ((10000 ℕ.* 10000) ℕ÷./ 5)) ∷ []
        benchmark-function "flatmap_take"
          (Tests.flatmap-take (gen 10000) (gen 10000) ((10000 ℕ.* 10000) ℕ÷./ 5))
