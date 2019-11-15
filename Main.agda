open import Streams
import C
open import Print
open import Data.String
open import IO
open import Data.Integer using (+_)
open import Data.Vec

module Main where

open C.C ⦃ ... ⦄

main =
  let ex = print (ofArr (⟨ + 1 ⟩ ∷ []) ▹ fold (λ x y → x + y) ⟨ + 0 ⟩) in
     run (IO.putStr ex)
