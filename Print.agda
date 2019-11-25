open import C
open import Data.String renaming (_==_ to _==ₛ_)
import Data.Integer
open import Data.Nat
import Data.Nat.Show
open import Data.Bool using () renaming (if_then_else_ to If_Then_Else_ ; Bool to 𝔹)
open import Data.Product
open import Data.Unit

module Print where

open C.C ⦃ ... ⦄

showReturn : String → 𝔹 → String
showReturn s b = If b Then ("return " ++ s) Else s

showOp : String → String → String → String
showOp op x y = "(" ++ x ++ " " ++ op ++ " " ++ y ++ ")"

showType : c_type → String
showType Char = "char"
showType Int = "int"
showType Bool = "int"
showType (Array α n) = "(" ++ (showType α) ++ ")[" ++ (Data.Nat.Show.show n) ++ "]"

showBasicDecl : c_type → (String → (ℕ → ℕ × String)) → (ℕ → ℕ × String)
showBasicDecl α k n =
  let var = "x" ++ (Data.Nat.Show.show n) in
  let n , k = k var (suc n) in
    n , (showType α) ++ " " ++ var ++ ";\n" ++ k

impl : C
C.Expr impl _ = String -- Variable index start → code
C.Statement impl = ℕ → ℕ × String
C.Ref impl _ = String
C._≤_ impl x y = ⊤
C.⟨ impl ⟩ x = Data.Integer.show x
C._+_ impl = showOp "+"
C._*_ impl = showOp "*"
C._-_ impl = showOp "-"
C._/_ impl = showOp "/"
C._<_ impl = showOp "<"
C._<=_ impl = showOp "<="
C._>_ impl = showOp ">"
C._>=_ impl = showOp ">="
C._==_ impl = showOp "=="
C.true impl = "1"
C.false impl = "0"
C._||_ impl = showOp "||"
C._&&_ impl = showOp "&&"
C.if_then_else_ impl cond t f n =
  let n , t = t n in
  let n , f = f n in
    n , "if (" ++ cond ++ ") {\n" ++ t ++ ";\n}\nelse {\n" ++ f ++ ";\n}"
C._[_] impl arr i =
    "(" ++ arr ++ "[" ++ i ++ "])"
C.★_ impl x = x
C._≔_ impl x y n = n , x ++ " = " ++ y
C._；_ impl x y n =
  let n , x = x n in
  let n , y = y n in
    n , x ++ ";\n" ++ y
C.decl impl Char = showBasicDecl Char
C.decl impl Int = showBasicDecl Int
C.decl impl Bool = showBasicDecl Bool
C.decl impl (Array α len) k n =
  let var = "x" ++ (Data.Nat.Show.show n) in
  let n , k = k var (suc n) in
    n , (showType α) ++ " " ++ var ++ "[" ++ (Data.Nat.Show.show len) ++ "];\n" ++ k
C.nop impl n = n , ""
C.for_to_then_ impl l u body n =
  let var = "x" ++ (Data.Nat.Show.show n) in
  let n , body = body var (suc n) in
    n ,
    "for (int " ++ var ++ " = " ++ l ++ "; "
        ++ var ++ " <= " ++ u ++ "; "
        ++ "++" ++ var ++ ") {\n"
      ++ body
    ++ ";\n}"
C.while_then_ impl cond body n =
  let n , body = body n in
    n , "while (" ++ cond ++ ") {\n" ++ body ++ ";\n}"

print : ∀ { α } → (∀ ⦃ _ : C ⦄ → Ref α → Statement) → String
print { α } e =
  let _ , x = (C.decl impl α λ x → e ⦃ impl ⦄ x) 0 in
    "int main(void) {\n" ++ x ++ ";\nreturn x0;\n}\n"
