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

print-expr : ∀ { α } → IExpr α → String

print-ref : ∀ { α } → IRef α → String
print-ref (r , []) = "x" ++ (ℕs.show r)
print-ref {α} (r , h ∷ t) = (print-ref {α} (r , t)) ++ "[" ++ (print-expr h) ++ "]"

print-decl : c_type → ℕ.ℕ → String
print-decl Int r = "int " ++ print-ref {Int} (r , [])
print-decl Bool r = "/* BOOL */ int " ++ print-ref {Bool} (r , [])
print-decl (Array α n) r = builder (Array α n) ""
  where
    builder : c_type → String → String
    builder Int acc = print-decl Int r ++ acc
    builder Bool acc = print-decl Bool r ++ acc
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

print : (∀ ⦃ _ : C ⦄ → Statement) → String
print = print-statement ∘ toAST

wrap-main : String → String
wrap-main body = "#include <stdio.h>\nint main(void) {\n" ++ body ++ ";\n}"

Func : ∀ ⦃ _ : C ⦄ → List c_type → Maybe c_type → Set
Func [] nothing = Statement
Func [] (just α) = Ref α → Statement
Func (α ∷ t) β = Ref α → Func t β

data C-Function : Set₁ where
  void : String → ∀ (sig : List c_type) → (∀ ⦃ _ : C ⦄ → Func sig nothing) → C-Function
  int : String → ∀ (sig : List c_type) → (∀ ⦃ _ : C ⦄ → Func sig (just Int)) → C-Function

Program = List String × List C-Function

print-program : Program → String
print-program (i , f) = print-includes i ++ print-funcs f
  where
    print-includes : List String → String
    print-includes [] = ""
    print-includes (h ∷ t) = "#include <" ++ h ++ ">\n" ++ print-includes t
    print-return-type : Maybe c_type → String
    print-return-type nothing = "void"
    print-return-type (just α) = print-ctype α
    print-arguments : List c_type → ℕ.ℕ → String
    print-arguments [] _ = "void"
    print-arguments (h ∷ []) n = print-decl h n
    print-arguments (h ∷ t@(_ ∷ _)) n =
      print-decl h n ++ ", " ++ print-arguments t (ℕ.suc n)
    print-body : ∀ { α } sig → (Func ⦃ AST-C ⦄ sig α) → ℕ.ℕ → String
    print-body {nothing} [] body n = print-statement (proj₂ (body n))
    print-body {just α} [] body n =
      print-statement (declaration α n (proj₂ (body (n , []) (suc n)))) ++ "return " ++ print-ref {α} (n , []) ++ ";\n"
    print-body {_} (α ∷ t) body n = print-body t (body (n , [])) (ℕ.suc n)
    print-func : ∀ α → String → ∀ sig → (∀ ⦃ _ : C ⦄ → Func sig α) → String
    print-func α name sig body =
      print-return-type α ++ " " ++ name ++ "(" ++ print-arguments sig 0 ++ ") {\n"
        ++ print-body sig (body ⦃ AST-C ⦄) 0
      ++ "}\n"
    print-funcs : List C-Function → String
    print-funcs [] = ""
    print-funcs (void name sig f ∷ l) = (print-func nothing name sig f) ++ print-funcs l
    print-funcs (int name sig f ∷ l) = (print-func (just Int) name sig f) ++ print-funcs l

print-main : (∀ ⦃ _ : C ⦄ → Statement) → String
print-main s =
  print-program (
    "stdio.h" ∷ [] ,
    (int "main" [] (λ i → s ； i ≔ ⟪ ℤ.+ 0 ⟫)) ∷ [])

print-main-return : (∀ ⦃ _ : C ⦄ → Ref Int → Statement) → String
print-main-return s =
  print-program (
    "stdio.h" ∷ [] ,
    (int "main" [] s) ∷ [])
