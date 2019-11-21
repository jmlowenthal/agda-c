open import Streams
import C
open import Print
open import Data.String using (String ; _++_)
open import IO hiding (return)
open import Data.Integer using (+_)
open import Data.Vec using (Vec ; _∷_ ; [] ; [_])

module Main where

open C.C ⦃ ... ⦄

square : ∀ ⦃ _ : C.C ⦄ → Stream C.Int → Stream C.Int
square = map (λ x → x * x)

sum : ∀ ⦃ _ : C.C ⦄ → Stream C.Int → Ref C.Int → Statement
sum = fold (λ x y → x + y) ⟨ + 0 ⟩

main =
  let ex = print (filter (λ x → (x / ⟨ + 2 ⟩) == ⟨ + 0 ⟩) (iota 0) ▹ sum) in
     run (IO.putStr ex)
