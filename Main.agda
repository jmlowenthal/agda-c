open import Streams
open import C
open import Print
open import Data.String using (String ; _++_)
open import IO hiding (return)
open import Data.Nat using (ℕ)
open import Data.Integer using (+_)
open import Data.Vec using (Vec ; _∷_ ; [] ; [_])

module Main where

open C.C ⦃ ... ⦄

spower : ∀ ⦃ _ : C ⦄ → Expr Int → ℕ → Expr Int
spower x ℕ.zero = ⟨ + 1 ⟩
spower x (ℕ.suc y) = x * (spower x y)

gibb : ∀ ⦃ _ : C ⦄ → ℕ → Expr Int → Expr Int → Expr Int
gibb ℕ.zero x y = x
gibb (ℕ.suc ℕ.zero) x y = y
gibb (ℕ.suc (ℕ.suc m)) x y = gibb (ℕ.suc m) x y + gibb m x y

-- This naive unrolling fails to terminate, since the function is not primitive-recursive
ackermann : ∀ ⦃ _ : C ⦄ → ℕ → Expr Int → (Ref Int → Statement)
ackermann ℕ.zero n x = x ≔ n + ⟨ + 1 ⟩
ackermann (ℕ.suc m) n x =
  if n == ⟨ + 0 ⟩ then
    x ← ackermann m ⟨ + 1 ⟩
  else
    decl Int λ y →
    y ← ackermann (ℕ.suc m) (n - ⟨ + 1 ⟩) ；
    x ← ackermann m (★ y)

-- TODO: show C-embedding is not Turing-complete by showing that we can solve the Halting Problem for the subset given (NB: no dynamic allocation or recursion means the language is not Turing-complete).

square : ∀ ⦃ _ : C ⦄ → Stream C.Int → Stream C.Int
square = map (λ x → x * x)

sum : ∀ ⦃ _ : C ⦄ → Stream Int → Ref Int → Statement
sum = fold (λ x y → x + y) ⟨ + 0 ⟩

main =
  let ex = print ((iota 0) ▹ filter (λ x → (x / ⟨ + 2 ⟩) == ⟨ + 0 ⟩) ▹ sum) in
     run (IO.putStr ex)
