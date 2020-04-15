module Print.Print where

open import C.Base
open import Data.List as List using (List ; [] ; _∷_)
open import Data.Maybe
open import Data.Nat as ℕ using (ℕ ; suc)
open import Data.Product
open import Data.String
open import Function using (_∘_)
open import Print.AST
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

import Data.Integer as ℤ
import Data.Nat.Show as ℕs
import Data.Char as Char

open C ⦃ ... ⦄

print-ctype : c_type → String
print-ctype Int = "int"
print-ctype Bool = "int"
print-ctype (Array α n) = "(" ++ (print-ctype α) ++ ")[" ++ (ℕs.show n) ++ "]" 

Print-C : C
C.Ref Print-C _ = String
C.Expr Print-C _ = String
C.Statement Print-C = ℕ → ℕ × String
C.⟪_⟫ Print-C x = ℤ.show x
C._+_ Print-C x y = "(" ++ x ++ ") + (" ++ y ++ ")"
C._*_ Print-C x y = "(" ++ x ++ ") * (" ++ y ++ ")"
C._-_ Print-C x y = "(" ++ x ++ ") - (" ++ y ++ ")"
C._/_ Print-C x y = "(" ++ x ++ ") / (" ++ y ++ ")"
C._<_ Print-C x y = "(" ++ x ++ ") < (" ++ y ++ ")"
C._<=_ Print-C x y = "(" ++ x ++ ") <= (" ++ y ++ ")"
C._>_ Print-C x y = "(" ++ x ++ ") > (" ++ y ++ ")"
C._>=_ Print-C x y = "(" ++ x ++ ") >= (" ++ y ++ ")"
C._==_ Print-C x y = "(" ++ x ++ ") == (" ++ y ++ ")"
C.true Print-C = "true"
C.false Print-C = "false"
C._||_ Print-C x y = "(" ++ x ++ ") || (" ++ y ++ ")"
C._&&_ Print-C x y = "(" ++ x ++ ") && (" ++ y ++ ")"
C.!_ Print-C x = "!(" ++ x ++ ")"
C._[_] Print-C r i = r ++ "[" ++ i ++ "]"
C.★_ Print-C x = x
C._⁇_∷_ Print-C c x y = "(" ++ c ++ ") " ++ fromChar (Char.fromℕ 63) -- Question mark = 63
    ++ " (" ++ x ++ ") : (" ++ y ++ ")"
C._≔_ Print-C x y n = n , x ++ " = " ++ y ++ ";\n"
C.if_then_else_ Print-C e x y n =
  let n , x = x n in
  let n , y = y n in
    n , "if (" ++ e ++ ") {\n" ++ x ++ "}\nelse\n{" ++ y ++ "}\n"
C._；_ Print-C x y n =
  let n , x = x n in
  let n , y = y n in
    n , x ++ y
C.decl Print-C α f n =
  let ref = "x" ++ ℕs.show n in
  let n , f = f ref (ℕ.suc n) in
    n , builder α ref ++ ";\n" ++ f
  where
    builder : c_type → String → String
    builder Int acc = "int " ++ acc
    builder Bool acc = "/* BOOL */ int " ++ acc
    builder (Array α n) acc = builder α (acc ++ "[" ++ ℕs.show n ++ "]")
C.nop Print-C n = n , ""
C.for_to_then_ Print-C l u f n =
  let i = "x" ++ ℕs.show n in
  let n , f = f i (ℕ.suc n) in
    n ,
    "for (int " ++ i ++ " = " ++ l ++ "; "
      ++ i ++ " <= " ++ u ++ "; "
      ++ "++" ++ i ++ ") {\n"
      ++ f
    ++ "}\n"
C.while_then_ Print-C e f n =
  let n , f = f n in
    n , "while (" ++ e ++ "){\n" ++ f ++ "}\n"
C.putchar Print-C x n = n , "putchar(" ++ x ++ ");\n"

print : (∀ ⦃ _ : C ⦄ → Statement) → String
print s = proj₂ (s ⦃ Print-C ⦄ 0)

print-main : (∀ ⦃ _ : C ⦄ → Statement) → String
print-main s =
  "#include <stdio.h>\n"
  ++ "int main(void) {\n"
    ++ print s
    ++ "return 0;\n"
 ++ "}\n"
