open import C
open import Data.String renaming (_==_ to _==ₛ_)
import Data.Integer
open import Data.Nat
import Data.Nat.Show
open import Data.Bool using () renaming (if_then_else_ to If_Then_Else_ ; Bool to 𝔹)
open import Data.Product

module Print where

open C.C ⦃ ... ⦄

showReturn : String → 𝔹 → String
showReturn s b = If b Then ("return " ++ s) Else s

showOp : String → (ℕ → ℕ × (𝔹 → String)) → (ℕ → ℕ × (𝔹 → String)) → (ℕ → ℕ × (𝔹 → String))
showOp op x y n =
  let n , x = x n in
  let x = x 𝔹.false in
  let n , y = y n in
  let y = y 𝔹.false in
    n , showReturn ("(" ++ x ++ " " ++ op ++ " " ++ y ++ ")")

showType : c_type → String
showType Void = "void"
showType Char = "char"
showType Int = "int"
showType Bool = "bool"
showType (Array α n) = "(" ++ (showType α) ++ ")[" ++ (Data.Nat.Show.show n) ++ "]"

showBasicDecl : c_type → ((ℕ → String) → (ℕ → ℕ × (𝔹 → String))) → (ℕ → ℕ × (𝔹 → String))
showBasicDecl α k n =
  let var = "x" ++ (Data.Nat.Show.show n) in
  let n , k = k (λ _ → var) (suc n) in
    n , λ b → (showType α) ++ " " ++ var ++ ";\n" ++ (k b)

impl : C
C.Code impl _ = ℕ → ℕ × (Data.Bool.Bool → String) -- Variable index start → Is return? → code
C.Ref impl _ = ℕ → String
C.⟨ impl ⟩ x n = n , showReturn (Data.Integer.show x)
C._+_ impl = showOp "+"
C._*_ impl = showOp "*"
C._-_ impl = showOp "-"
C._/_ impl = showOp "/"
C._<_ impl = showOp "<"
C._<=_ impl = showOp "<="
C._>_ impl = showOp ">"
C._>=_ impl = showOp ">="
C._==_ impl = showOp "=="
C.true impl n = n , showReturn "true"
C.false impl n = n , showReturn "false"
C._||_ impl = showOp "||"
C._&&_ impl = showOp "&&"
C.if_then_else_ impl cond t f n =
  let n , cond = cond n in
  let cond = cond 𝔹.false in
  let n , t = t n in
  let t = t 𝔹.false in
  let n , f = f n in
  let f = f 𝔹.false in
    n , showReturn ("if (" ++ cond ++ ") { " ++ t ++ " } else { " ++ f ++ " }")
C._[_] impl arr i n =
  let n , i = i n in
  let i = i 𝔹.false in
  let arr = arr n in
    "(" ++ arr ++ "[" ++ i ++ "])"
C.★_ impl x n = let x = x n in n , showReturn x
C._≔_ impl x y n =
  let x = x n in
  let n , y = y n in
  let y = y 𝔹.false in
    n , showReturn (x ++ " = " ++ y)
C._；_ impl x y n =
  let n , x = x n in
  let x = x 𝔹.false in
  let n , y = y n in
    n , λ b → x ++ ";\n" ++ (y b)
C.decl impl Void = showBasicDecl Void
C.decl impl Char = showBasicDecl Char
C.decl impl Int = showBasicDecl Int
C.decl impl Bool = showBasicDecl Bool
C.decl impl (Array α len) k n =
  let var = "x" ++ (Data.Nat.Show.show n) in
  let n , k = k (λ _ → var) (suc n) in
    n , λ b → (showType α) ++ " " ++ var ++ "[" ++ (Data.Nat.Show.show len) ++ "];\n" ++ (k b)
C.nop impl n = n , showReturn "0"
C.for_to_then_ impl l u body n =
  let n , l = l n in
  let l = l 𝔹.false in
  let n , u = u n in
  let u = u 𝔹.false in
  let var = "x" ++ (Data.Nat.Show.show n) in
  let n , body = body (λ _ → var) (suc n) in
    n ,
    λ b → "for (int " ++ var ++ " = " ++ l ++ "; "
        ++ var ++ " <= " ++ u ++ "; "
        ++ "++" ++ var ++ ") {\n"
      ++ body b
    ++ ";\n}"
C.while_then_ impl cond body n =
  let n , cond = cond n in
  let cond = cond 𝔹.false in
  let n , body = body n in
    n , λ b → "while (" ++ cond ++ ") {\n" ++ body b ++ "\n}"

print : ∀ { α } → (∀ ⦃ _ : C ⦄ → Code α) → String
print e = let _ , s = e ⦃ impl ⦄ 0 in "int main(void) {\n" ++ (s 𝔹.true) ++ ";\n}\n"
