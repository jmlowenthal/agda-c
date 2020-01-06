module Print.Print where

open import C
open import Print.AST
open import Data.String
import Data.Integer as ℤ
import Data.Nat.Show as ℕ

print-ctype : c_type → String
print-ctype Int = "int"
print-ctype Bool = "int"
print-ctype (Array α n) = "(" ++ (print-ctype α) ++ ")[" ++ (ℕ.show n) ++ "]" 

print-ref : ∀ { α } → IRef α → String
print-expr : ∀ { α } → IExpr α → String

print-ref (index arr i) = "(" ++ (print-ref arr) ++ "[" ++ (print-expr i) ++ "])"
print-ref (var x) = x

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
print-expr (deref x) = print-ref x

print-statement : IStatement → String
print-statement (ifthenelse e t f) =
  "if (" ++ (print-expr e) ++ ") {\n"
    ++ (print-statement t)
  ++ "}\nelse\n{"
    ++ (print-statement f)
  ++ "}\n"
print-statement (assignment x e) = (print-ref x) ++ " = " ++ (print-expr e) ++ ";\n"
print-statement (sequence a b) = (print-statement a) ++ (print-statement b)
print-statement (declaration α f) = (print-ctype α) ++ (print-statement (f {!!}))
print-statement (for l u f) =
  "for (int i = " ++ (print-expr l) ++ "; i < " ++ (print-expr u) ++ "; ++i) {\n"
    ++ (print-statement (f {!!}))
  ++ "}\n"
print-statement (while e f) =
  "while (" ++ (print-expr e) ++ "){\n"
    ++ (print-statement f)
  ++ "}\n"
print-statement nop = ""

print : ∀ { α } → (∀ ⦃ ℐ : C ⦄ → C.Ref ℐ α → C.Statement ℐ) → String
print {α} s = print-statement (declaration α (s ⦃ AST-C ⦄))
