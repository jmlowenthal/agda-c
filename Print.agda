open import C
open import Data.String renaming (_==_ to _==ₛ_)
import Data.Integer
open import Data.Nat
import Data.Nat.Show
open import Data.Bool using () renaming (if_then_else_ to If_Then_Else_)
open import Data.Product

module Print where

open C.C ⦃ ... ⦄

showOp : String → (ℕ → ℕ × String) → (ℕ → ℕ × String) → (ℕ → ℕ × String)
showOp op x y n =
  let n , x = x n in
  let n , y = y n in
    n , "(" ++ x ++ " " ++ op ++ " " ++ y ++ ")"

showType : c_type → String
showType Void = "void"
showType Char = "char"
showType Int = "int"
showType Bool = "bool"
showType (Array α n) = "(" ++ (showType α) ++ ")[" ++ (Data.Nat.Show.show n) ++ "]"

impl : C
C.Code impl _ = ℕ → ℕ × String -- Variable index start → code
C.Ref impl _ = ℕ → String
C.⟨ impl ⟩ x n = n , Data.Integer.show x
C._+_ impl = showOp "+"
C._*_ impl = showOp "*"
C._-_ impl = showOp "-"
C._/_ impl = showOp "/"
C._<_ impl = showOp "<"
C._<=_ impl = showOp "<="
C._>_ impl = showOp ">"
C._>=_ impl = showOp ">="
C._==_ impl = showOp "=="
C.true impl n = n , "true"
C.false impl n = n , "false"
C._||_ impl = showOp "||"
C._&&_ impl = showOp "&&"
C.if_then_else_ impl cond t f n =
  let n , cond = cond n in
  let n , t = t n in
  let n , f = f n in
    n , "if (" ++ cond ++ ") { " ++ t ++ " } else { " ++ f ++ " }"
C.[] impl n = n , "{}"
C._∷_ impl x y n =
  let n , x = x n in
  let n , y = y n in
    n , (If (y ==ₛ "{}") Then x Else (x ++ ", " ++ y))
C._[_] impl arr i n =
  let n , i = i n in
  let arr = arr n in
    "(" ++ arr ++ "[" ++ i ++ "])"
C.★_ impl x n = let x = x n in n , x
C._≔_ impl x y n =
  let n , y = y n in
  let x = x n in
    n , x ++ " = " ++ y
C._；_ impl x y n =
  let n , x = x n in
  let n , y = y n in
    n , x ++ ";\n" ++ y
C.decl impl α k n =
  let var = "x" ++ (Data.Nat.Show.show n) in
  let n , k = k (λ _ → var) (suc n) in
    n , (showType α) ++ " " ++ var ++ ";\n" ++ k
C.nop impl n = n , ""
C.for_to_then_ impl l u body n =
  let n , l = l n in
  let n , u = u n in
  let n , body = body (λ _ → "x" ++ (Data.Nat.Show.show n)) (suc n) in
    n , "for (int i = " ++ l ++ "; i <= " ++ u ++ "; ++i) {\n" ++ body ++ "\n}"
C.while_then_ impl cond body n =
  let n , cond = cond n in
  let n , body = body n in
    n , "while (" ++ cond ++ ") {\n" ++ body ++ "\n}"

print : ∀ { α } → (∀ ⦃ _ : C ⦄ → Code α) → String
print e = let _ , s = e ⦃ impl ⦄ 0 in s
