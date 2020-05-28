module Print.Eval where

open import C
open import C.Properties.State
open import Data.Bool renaming (Bool to 𝔹 ; if_then_else_ to If_Then_Else_)
open import Data.Integer as ℤ using (ℤ)
open import Data.Maybe
open import Data.Product
open import Data.Unit
open import Data.Vec
open import Data.Nat as ℕ using (ℕ)
open import Data.String
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Function

import Data.Integer.Properties as ℤₚ
import Data.Integer.DivMod as ℤ÷
import Data.Nat as ℕ
import Data.Char as Char
import Level

divide : ℤ → ℤ → ℤ
divide x (ℤ.pos 0) = ℤ.+ 0 -- Implementation defined
divide x y@(ℤ.+[1+ n ]) = (x ℤ÷.div y) {tt}
divide x y@(ℤ.negsuc n) = (x ℤ÷.div y) {tt}

data Refer (α : c_type) : Set where
  var : ℕ → Refer α
  index : ∀ { n } → Refer (Array α n) → ℤ → Refer α

depth : ∀ { α } → Refer α → ℕ
depth (var _) = 0
depth (index x _) = ℕ.suc (depth x)

{-# TERMINATING #-}
≟-Refer : ∀ (x : ∃[ α ] Refer α) (y : ∃[ α ] Refer α) → Dec (x ≡ y)
≟-Refer (α , x) (β , y) with ≟-ctype α β
≟-Refer _ _ | no ¬p = no λ { refl → ¬p refl }
≟-Refer (_ , var a) (_ , var b) | yes refl  with a ℕ.≟ b
≟-Refer (_ , var a) (_ , var b) | yes refl | yes refl = yes refl
≟-Refer (_ , var a) (_ , var b) | yes refl | no ¬p = no λ { refl → ¬p refl }
≟-Refer (_ , var _) (_ , index _ _) | yes refl = no λ ()
≟-Refer (_ , index _ _) (_ , var _) | yes refl = no λ ()
≟-Refer (α , index x i) (α , index y j) | yes refl with ≟-Refer (_ , x) (_ , y) | i ℤ.≟ j
≟-Refer (_ , index _ _) (_ , index _ _) | yes refl | yes refl | yes refl = yes refl
≟-Refer (_ , index _ _) (_ , index _ _) | yes refl | yes refl | no ¬p = no λ { refl → ¬p refl }
≟-Refer (_ , index _ _) (_ , index _ _) | yes refl | no ¬p | _ = no λ { refl → ¬p refl }

Envir : Set
Envir = ∀ { α } → Refer α → ⟦ α ⟧

-- Default base environment
E0 : Envir
E0 {Int} _ = ℤ.+ 0
E0 {Bool} _ = 𝔹.false
E0 {Array α ℕ.zero} _ = []
E0 {Array α (ℕ.suc n)} _ = E0 {α} (var 0) ∷ E0 (var 0)

Eval-C : C
C.Ref Eval-C α = Envir → Refer α
C.Expr Eval-C α = Envir → ⟦ α ⟧
C.Statement Eval-C = (String × ℕ × Envir) → (String × ℕ × Envir)
C.⟪_⟫ Eval-C x _ = x
C._+_ Eval-C x y E = x E ℤ.+ y E
C._*_ Eval-C x y E = x E ℤ.* y E
C._-_ Eval-C x y E = x E ℤ.- y E
C._/_ Eval-C x y E = divide (x E) (y E)
C._<_ Eval-C x y E = ⌊ x E ℤ.<? y E ⌋
C._<=_ Eval-C x y E = ⌊ x E ℤ.≤? y E ⌋
C._>_ Eval-C x y E = ⌊ y E ℤ.<? x E ⌋
C._>=_ Eval-C x y E = ⌊ y E ℤ.≤? x E ⌋
C._==_ Eval-C x y E = ⌊ x E ℤ.≟ y E ⌋
C.true Eval-C E = 𝔹.true
C.false Eval-C E = 𝔹.false
C._||_ Eval-C x y E = x E ∨ y E
C._&&_ Eval-C x y E = x E ∧ y E
C.!_ Eval-C x E = not (x E)
C._[_] Eval-C r i E = index (r E) (i E)
C.★_ Eval-C x E = E (x E)
C._⁇_∷_ Eval-C c x y E with c E
... | true = x E
... | false = y E
C._≔_ Eval-C x y (s , n , E) = s , n , env
  where
    env : Envir
    env r with ≟-Refer (_ , r) (_ , x E)
    ... | yes refl = y E
    ... | no _ = E r
C.if_then_else_ Eval-C e x y (s , n , E) with e E
... | true = x (s , n , E)
... | false = y (s , n , E)
C._；_ Eval-C x y (s , n , E) = y (x (s , n , E))
C.decl Eval-C α f (s , n , E) = f (λ _ → var n) (s , ℕ.suc n , E)
C.nop Eval-C = id
C.for_to_then_ Eval-C l u f (s , n , E) = iter (u E) (u E ℤ.- l E) (s , ℕ.suc n , E)
  where
    env : ℤ → Envir → Envir
    env _ E r@(index _ _) = E r
    env x E {Bool} r@(var _) = E r
    env x E {Array _ _} r@(var _) = E r
    env x E {Int} r@(var i) with i ℕ.≟ n
    ... | yes refl = x
    ... | no _ = E r
    iter : ℤ → ℤ → String × ℕ × Envir → String × ℕ × Envir
    iter base (ℤ.negsuc _) = id
    iter base (ℤ.pos ℕ.zero) = id
    iter base j@(ℤ.pos (ℕ.suc i)) (s , m , E) =
      iter base (ℤ.pos i) (f (λ _ → var n) (s , m , env (base ℤ.- j) E))
C.while_then_ Eval-C e f = ?
C.putchar Eval-C x (s , n , E) =
  s Data.String.++ fromChar (Char.fromℕ ℤ.∣ (x E) ℤ.⊔ (ℤ.+ 0) ∣) , n , E
