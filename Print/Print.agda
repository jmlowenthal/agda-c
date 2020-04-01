module Print.Print where

open import C
open import Print.AST
open import Data.String
open import Data.List using (List ; [] ; _∷_)
open import Data.Product
open import Function using (_∘_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

import Data.Integer as ℤ
import Data.Nat as ℕ
import Data.Nat.Show as ℕs
import Data.Char as Char

print-ctype : c_type → String
print-ctype Int = "int"
print-ctype Bool = "int"
print-ctype (Array α n) = "(" ++ (print-ctype α) ++ ")[" ++ (ℕs.show n) ++ "]" 

print-expr : ∀ { α } → IExpr α → String

print-ref : ∀ { α } → IRef α → String
print-ref (r , []) = "x" ++ (ℕs.show r)
print-ref {α} (r , h ∷ t) = (print-ref {α} (r , t)) ++ "[" ++ (print-expr h) ++ "]"

print-decl : c_type → ℕ.ℕ → String
print-decl Int r = "int " ++ print-ref {Int} (r , [])
print-decl Bool r = "int " ++ print-ref {Bool} (r , [])
print-decl (Array α n) r = builder (Array α n) ""
  where
    builder : c_type → String → String
    builder Int acc = print-ref {Int} (r , []) ++ acc
    builder Bool acc = print-ref {Bool} (r , []) ++ acc
    builder (Array α n) acc = builder α (acc ++ "[" ++ ℕs.show n ++ "]")

print-expr (lit x) = ℤ.show x
print-expr (add x y) = "(" ++ (print-expr x) ++ ") + (" ++ (print-expr y) ++ ")"
print-expr (mul x y) = "(" ++ (print-expr x) ++ ") * (" ++ (print-expr y) ++ ")"
print-expr (sub x y) = "(" ++ (print-expr x) ++ ") - (" ++ (print-expr y) ++ ")"
print-expr (div x y) = "(" ++ (print-expr x) ++ ") / (" ++ (print-expr y) ++ ")"
print-expr (lt x y) = "(" ++ (print-expr x) ++ ") < (" ++ (print-expr y) ++ ")"
print-expr (lte x y) = "(" ++ (print-expr x) ++ ") <= (" ++ (print-expr y) ++ ")"
print-expr (gt x y) = "(" ++ (print-expr x) ++ ") > (" ++ (print-expr y) ++ ")"
print-expr (gte x y) = "(" ++ (print-expr x) ++ ") >= (" ++ (print-expr y) ++ ")"
print-expr (eq x y) = "(" ++ (print-expr x) ++ ") == (" ++ (print-expr y) ++ ")"
print-expr true = "1"
print-expr false = "0"
print-expr (or x y) = "(" ++ (print-expr x) ++ ") || (" ++ (print-expr y) ++ ")"
print-expr (and x y) = "(" ++ (print-expr x) ++ ") && (" ++ (print-expr y) ++ ")"
print-expr (not x) = "!(" ++ (print-expr x) ++ ")"
print-expr (deref {α} x) = print-ref {α} x
print-expr (tenary c x y) =
  "(" ++ print-expr c ++ ") " ++ fromChar (Char.fromℕ 63) -- Question mark = 63
    ++ " (" ++ print-expr x ++ ") : (" ++ print-expr y ++ ")"

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
  (print-decl α ref) ++ ";\n" ++ (print-statement f)
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
print-statement (putchar i) = "putchar(" ++ print-expr i ++ ");\n"

print : (∀ ⦃ ℐ : C ⦄ → C.Statement ℐ) → String
print = print-statement ∘ toAST

wrap-main : String → String
wrap-main body = "#include <stdio.h>\nint main(void) {\n" ++ body ++ ";\n}"

print-main : (∀ ⦃ ℐ ⦄ → C.Statement ℐ) → String
print-main s =
  wrap-main (print-statement (proj₂ (s ⦃ AST-C ⦄ 0)) ++ "return 0")

print-main-return : ∀ { α } → (∀ ⦃ ℐ ⦄ → C.Ref ℐ α → C.Statement ℐ) → String
print-main-return {α} s =
  let s = declaration α 0 (proj₂ (s ⦃ AST-C ⦄ (0 , []) 1)) in
    wrap-main (print-statement s ++ "return " ++ print-ref {α} (0 , []))
