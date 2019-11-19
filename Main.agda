open import Streams
import C
open import Print
open import Data.String
open import IO
open import Data.Integer using (+_)
open import Data.Vec using (_∷_ ; [] ; [_])

module Main where

open C.C ⦃ ... ⦄

sum : ∀ ⦃ _ : C.C ⦄ → Stream C.Int → Code C.Int
sum = fold (λ x y → x + y) ⟨ + 0 ⟩

main =
  let ex = print (ofArr (⟨ + 1 ⟩ ∷ ⟨ + 2 ⟩ ∷ ⟨ + 3 ⟩ ∷ []) ▹ sum) in
     run (IO.putStr ex)
