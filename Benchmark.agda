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
open import Print.AST using (AST-C)
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

  sum : ∀ { n } → Ref Int → Ref (Array Int n) → Statement
  sum r arr =
    r ← fold _+_ ⟪ + 0 ⟫ (ofArr arr)

  sumOfSquares : ∀ { n } → Ref Int → Ref (Array Int n) → Statement
  sumOfSquares r arr =
    r ← fold _+_ ⟪ + 0 ⟫
      (ofArr arr
        ▹ map (λ a → a * a))

  sumOfSquaresEven : ∀ { n } → Ref Int → Ref (Array Int n) → Statement
  sumOfSquaresEven r arr =
    r ← fold _+_ ⟪ + 0 ⟫
      (ofArr arr
        ▹ filter (λ e → (e % ⟪ + 2 ⟫) == ⟪ + 0 ⟫)
        ▹ map (λ a → a * a))

  -- Sum over Cartesian-/outer-product
  cart : ∀ { n m } → Ref Int → Ref (Array Int n) → Ref (Array Int m) → Statement
  cart r x y =
    r ← fold _+_ ⟪ + 0 ⟫
    (ofArr x
      ▹ flatmap (λ i → ofArr y ▹ map (λ j → i * j)))

  maps : ∀ { n } → Ref Int → Ref (Array Int n) → Statement
  maps r arr =
    iter (λ e → r ≔ e)
      (ofArr arr
        ▹ map (λ e → e * ⟪ + 2 ⟫)
        ▹ map (λ e → e * ⟪ + 3 ⟫))

  filters : ∀ { n } → Ref Int → Ref (Array Int n) → Statement
  filters r arr =
    iter (λ e → r ≔ e)
      (ofArr arr
        ▹ filter (λ e → ! (e == ⟪ + 5 ⟫))
        ▹ filter (λ e → ! (e == ⟪ + 10 ⟫)))

  dotProduct : ∀ { n m } → Ref Int → Ref (Array Int n) → Ref (Array Int m) → Statement
  dotProduct r x y =
    r ← fold _+_ ⟪ + 0 ⟫
      (zipWith (λ i j → i * j) (ofArr x) (ofArr y) {ℕ.z≤n})

  flatmap-after-zipWith : ∀ { n m } → Ref Int → Ref (Array Int n) → Ref (Array Int m) → Statement
  flatmap-after-zipWith r x y =
    iter (λ e → r ≔ e)
      (zipWith _+_ (ofArr x) (ofArr x) {ℕ.z≤n}
        ▹ flatmap (λ i → ofArr y ▹ map (λ j → i * j)))

  zipWith-after-flatmap : ∀ { n } → Ref Int → Ref (Array Int (n ℕ.* n)) → Ref (Array Int n) → Statement
  zipWith-after-flatmap r x y =
    iter (λ e → r ≔ e)
      (zipWith _+_
      (ofArr x)
      (flatmap (λ e → ofArr y ▹ map (λ a → a + e)) (ofArr y))
      {ℕ.s≤s ℕ.z≤n})

  flatmap-take : ∀ { n m } → ℕ → Ref Int → Ref (Array Int n) → Ref (Array Int m) → Statement
  flatmap-take i r x y =
    iter (λ e → r ≔ e)
      (ofArr x
        ▹ flatmap (λ a → ofArr y ▹ map (λ b → a + b))
        ▹ take ⟪ + i ⟫)

IntArraysFunc : ∀ ⦃ _ : C ⦄ → List ℕ → Set
IntArraysFunc [] = Statement
IntArraysFunc (h ∷ t) = Ref (Array Int h) → IntArraysFunc t

benchmark-function : String → ∀ l → (∀ ⦃ _ : C ⦄ → Ref Int → IntArraysFunc l) → String
benchmark-function name l body =
  "#if BENCHMARK_" ++ name ++ "\n"
  ++ "int main(void){\n"
    ++ "volatile int " ++ print-ref {Int} (0 , []) ++ ";\n"
    ++ decl-int-arrays l (body ⦃ AST-C ⦄ (0 , [])) 1
    ++ "return 0;\n"
  ++ "}\n"
  ++ "#endif\n\n"
  where
    init : ∀ ⦃ _ : C ⦄ n → Ref (Array Int n) → Statement
    init n ref =
      for ⟪ + 0 ⟫ to ⟪ + n ℤ.- + 1 ⟫ then λ i → (
        ref [ ★ i ] ≔ (★ i) % ⟪ + 10 ⟫
      )
    decl-int-arrays : ∀ l → IntArraysFunc ⦃ AST-C ⦄ l → ℕ → String
    decl-int-arrays [] k n = print-statement (proj₂ (k n))
    decl-int-arrays (h ∷ t) k n =
      let m , initialiser = init ⦃ AST-C ⦄ h (n , []) (ℕ.suc n) in
        "/* INT[" ++ ℕs.show h ++ "] */ int* " ++ print-ref {Int} (n , [])
          ++ " = malloc(" ++ ℕs.show h ++ " * sizeof(int));\n"
        ++ print-statement initialiser
        ++ decl-int-arrays t (k (n , [])) m

main =
  run (IO.putStr ex)
  where
    100M = 100000000
    10M =   10000000
    10K =      10000
    ex : String
    ex =
      "#include <stdio.h>\n"
      ++ "#include <stdlib.h>\n"
      ++ (benchmark-function "sum" (100M ∷ []) Tests.sum)
      ++ (benchmark-function "sumOfSquares" (100M ∷ []) Tests.sumOfSquares)
      ++ (benchmark-function "sumOfSquaresEven" (100M ∷ []) Tests.sumOfSquaresEven)
      ++ (benchmark-function "cart" (10M ∷ 10 ∷ []) Tests.cart)
      ++ (benchmark-function "maps" (100M ∷ []) Tests.maps)
      ++ (benchmark-function "filters" (100M ∷ []) Tests.filters)
      ++ (benchmark-function "dotProduct" (10M ∷ 10M ∷ []) Tests.dotProduct)
      ++ (benchmark-function "flatmap_after_zipWith" (10K ∷ 10K ∷ [])
            Tests.flatmap-after-zipWith)
      ++ (benchmark-function "zipWith_after_flatmap" (_ ∷ 10K ∷ [])
            Tests.zipWith-after-flatmap)
      ++ (benchmark-function "flatmap_take" (10K ∷ 10K ∷ [])
            (Tests.flatmap-take ((10K ℕ.* 10K) ℕ÷./ 5)))
