module Print.Print where

open import C
open import Print.AST
open import Data.String
open import Data.List using (List ; [] ; _∷_)
open import Data.Product
open import Function using (_∘_)
import Data.Integer as ℤ
import Data.Nat.Show as ℕ

print-ctype : c_type → String
print-ctype Int = "int"
print-ctype Bool = "int"
print-ctype (Array α n) = "(" ++ (print-ctype α) ++ ")[" ++ (ℕ.show n) ++ "]" 

print-expr : ∀ { α } → IExpr α → String

print-ref : ∀ { α } → IRef α → String
print-ref (r , []) = "x" ++ (ℕ.show r)
print-ref {α} (r , h ∷ t) = (print-ref {α} (r , t)) ++ "[" ++ (print-expr h) ++ "]"

print-expr (lit x) = ℤ.show x
print-expr (add x y) = "(" ++ (print-expr x) ++ " + " ++ (print-expr y) ++ ")"
print-expr (mul x y) = "(" ++ (print-expr x) ++ " * " ++ (print-expr y) ++ ")"
print-expr (sub x y) = "(" ++ (print-expr x) ++ " - " ++ (print-expr y) ++ ")"
print-expr (div x y) = "(" ++ (print-expr x) ++ " / " ++ (print-expr y) ++ ")"
print-expr (lt x y) = "(" ++ (print-expr x) ++ " < " ++ (print-expr y) ++ ")"
print-expr (lte x y) = "(" ++ (print-expr x) ++ " <= " ++ (print-expr y) ++ ")"
print-expr (gt x y) = "(" ++ (print-expr x) ++ " > " ++ (print-expr y) ++ ")"
print-expr (gte x y) = "(" ++ (print-expr x) ++ " >= " ++ (print-expr y) ++ ")"
print-expr (eq x y) = "(" ++ (print-expr x) ++ " == " ++ (print-expr y) ++ ")"
print-expr true = "1"
print-expr false = "0"
print-expr (or x y) = "(" ++ (print-expr x) ++ " || " ++ (print-expr y) ++ ")"
print-expr (and x y) = "(" ++ (print-expr x) ++ " && " ++ (print-expr y) ++ ")"
print-expr (not x) = "(!" ++ (print-expr x) ++ ")"
print-expr (deref {α} x) = print-ref {α} x

print-statement : IStatement → String
print-statement (ifthenelse e t f) =
  "if (" ++ (print-expr e) ++ ") {\n"
    ++ (print-statement t)
  ++ "}\nelse\n{"
    ++ (print-statement f)
  ++ "}\n"
print-statement (assignment {α} x e) = (print-ref {α} x) ++ " = " ++ (print-expr e) ++ ";\n"
print-statement (sequence a b) = (print-statement a) ++ (print-statement b)
print-statement (declaration α ref f) =
  (print-ctype α) ++ " " ++ (print-ref {α} ref) ++ ";\n" ++ (print-statement f)
print-statement (for ref l u f) =
  let i = print-ref {Int} ref in
    "for ("
      ++ (print-ctype Int) ++ i ++ " = " ++ (print-expr l) ++ "; "
      ++ i ++ " < " ++ (print-expr u) ++ "; "
      ++ "++" ++ i ++ ") {\n"
      ++ (print-statement f)
    ++ "}\n"
print-statement (while e f) =
  "while (" ++ (print-expr e) ++ "){\n"
    ++ (print-statement f)
  ++ "}\n"
print-statement nop = ""

print : (∀ ⦃ ℐ : C ⦄ → C.Statement ℐ) → String
print = print-statement ∘ toAST

print-main : ∀ { α } → (∀ ⦃ ℐ ⦄ → C.Ref ℐ α → C.Statement ℐ) → String
print-main {α} s =
  let ref = (0 , []) in
  let s = declaration α ref (proj₂ (s ⦃ AST-C ⦄ ref 1)) in
    "int main(void) {\n" ++ print-statement s ++ "return " ++ print-ref {α} ref ++ ";\n}"
