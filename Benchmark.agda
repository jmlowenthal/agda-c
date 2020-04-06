open import C.Base
open import C.Extras
open import Data.Integer as ℤ using (+_)
open import Data.List as List using (List ; _∷_ ; [])
open import Data.Maybe as Maybe using (Maybe ; just ; nothing)
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

  gen : ∀ n → (Ref (Array Int n) → Statement) → Statement
  gen n k =
    decl (Array Int n) λ arr →
    for ⟪ + 0 ⟫ to ⟪ + n ℤ.- + 1 ⟫ then λ i → (
      arr [ ★ i ] ≔ (★ i) % ⟪ + 10 ⟫
    ) ；
    k arr

  sum : ℕ → Statement
  sum n =
    gen n λ arr →
      decl Int λ r →
      r ← fold _+_ ⟪ + 0 ⟫ (ofArr arr)

  sumOfSquares : ℕ → Statement
  sumOfSquares n =
    gen n λ arr →
      decl Int λ r →
      r ← fold _+_ ⟪ + 0 ⟫
        (ofArr arr
          ▹ map (λ a → a * a))

  sumOfSquaresEven : ℕ → Statement
  sumOfSquaresEven n =
    gen n λ arr →
      decl Int λ r →
      r ← fold _+_ ⟪ + 0 ⟫
        (ofArr arr
          ▹ filter (λ e → (e % ⟪ + 2 ⟫) == ⟪ + 0 ⟫)
          ▹ map (λ a → a * a))

  -- Sum over Cartesian-/outer-product
  cart : ℕ → ℕ → Statement
  cart n m =
    gen n λ x →
      gen m λ y →
        decl Int λ r →
        r ← fold _+_ ⟪ + 0 ⟫
        (ofArr x
          ▹ flatmap (λ i → ofArr y ▹ map (λ j → i * j)))

  maps : ℕ → Statement
  maps n =
    gen n λ arr →
      iter (λ _ → nop)
        (ofArr arr
          ▹ map (λ e → e * ⟪ + 2 ⟫)
          ▹ map (λ e → e * ⟪ + 3 ⟫))

  filters : ℕ → Statement
  filters n =
    gen n λ arr →
      iter (λ _ → nop)
        (ofArr arr
          ▹ filter (λ e → ! (e == ⟪ + 5 ⟫))
          ▹ filter (λ e → ! (e == ⟪ + 10 ⟫)))

  dotProduct : ℕ → ℕ → Statement
  dotProduct n m =
    gen n λ x →
      gen n λ y →
        decl Int λ r →
        r ← fold _+_ ⟪ + 0 ⟫
          (zipWith (λ i j → i * j) (ofArr x) (ofArr y) {ℕ.z≤n})

  flatmap-after-zipWith : ℕ → ℕ → Statement
  flatmap-after-zipWith n m =
    gen n λ x →
      gen n λ y →
        iter (λ _ → nop)
          (zipWith _+_ (ofArr x) (ofArr x) {ℕ.z≤n}
            ▹ flatmap (λ i → ofArr y ▹ map (λ j → i * j)))

  zipWith-after-flatmap : ℕ → Statement
  zipWith-after-flatmap n =
    gen (n ℕ.* n) λ x →
      gen n λ y →
        iter (λ _ → nop)
          (zipWith _+_
          (ofArr x)
          (flatmap (λ e → ofArr y ▹ map (λ a → a + e)) (ofArr y))
          {ℕ.s≤s ℕ.z≤n})

  flatmap-take : ℕ → ℕ → ℕ → Statement
  flatmap-take n m i =
    gen n λ x →
      gen m λ y →
        iter (λ _ → nop)
          (ofArr x
            ▹ flatmap (λ a → ofArr y ▹ map (λ b → a + b))
            ▹ take ⟪ + i ⟫)

benchmark-function : String → (∀ ⦃ _ : C ⦄ → Statement) → String
benchmark-function name body = 
  "#if BENCHMARK_" ++ name ++ "\n"
  ++ print-func (just Int) "main" [] (λ r → body ； r ≔ ⟪ + 0 ⟫)
  ++ "#endif\n\n"

main =
  run (IO.putStr ex)
  where
    gen : ∀ ⦃ _ : C ⦄ n → Vec (Expr Int) n
    gen _ = Vec.tabulate (λ n → ⟪ + ((Fin.toℕ n) ℕ÷.% 10) ⟫)
    gen100M : ∀ ⦃ _ : C ⦄ → Vec _ 10000
    gen100M = gen _
    gen10M : ∀ ⦃ _ : C ⦄ → Vec _ 1000
    gen10M = gen _
    gen10K : ∀ ⦃ _ : C ⦄ → Vec _ 100
    gen10K = gen _
    100M = 100000000
    10M =   10000000
    10K =      10000
    ex : String
    ex =
      "#include <stdio.h>\n"
      ++
        (benchmark-function "sum"
          (Tests.sum 100M))
      ++
        (benchmark-function "sumOfSquares"
          (Tests.sumOfSquares 100M))
      ++
        (benchmark-function "sumOfSquaresEven"
          (Tests.sumOfSquaresEven 100M))
      ++
        (benchmark-function "cart"
          (Tests.cart 10M 10))
      ++
        (benchmark-function "maps"
          (Tests.maps 100M))
      ++
        (benchmark-function "filters"
          (Tests.filters 100M))
      ++
        (benchmark-function "dotProduct"
          (Tests.dotProduct 10M 10M))
      ++
        (benchmark-function "flatmap_after_zipWith"
          (Tests.flatmap-after-zipWith 10K 10K))
      ++
        (benchmark-function "zipWith_after_flatmap"
          (Tests.zipWith-after-flatmap 10K))
      ++
        (benchmark-function "flatmap_take"
          (Tests.flatmap-take 10K 10K ((10K ℕ.* 10K) ℕ÷./ 5)))
