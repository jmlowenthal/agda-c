module Print.AST where

open import C
open import Data.Nat as ℕ using (ℕ)
open import Data.Integer as ℤ using (ℤ)
open import Data.String
open import Data.List using (List ; _∷_ ; [])
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

data IExpr : c_type → Set

IRef : c_type → Set
IRef _ = ℕ × List (IExpr Int)

data IExpr where
  lit : ℤ → IExpr Int
  add : IExpr Int → IExpr Int → IExpr Int
  mul : IExpr Int → IExpr Int → IExpr Int
  sub : IExpr Int → IExpr Int → IExpr Int
  div : IExpr Int → IExpr Int → IExpr Int
  lt : IExpr Int → IExpr Int → IExpr Bool
  lte : IExpr Int → IExpr Int → IExpr Bool
  gt : IExpr Int → IExpr Int → IExpr Bool
  gte : IExpr Int → IExpr Int → IExpr Bool
  eq : IExpr Int → IExpr Int → IExpr Bool
  true : IExpr Bool
  false : IExpr Bool
  or : IExpr Bool → IExpr Bool → IExpr Bool
  and : IExpr Bool → IExpr Bool → IExpr Bool
  not : IExpr Bool → IExpr Bool
  deref : ∀ { α } → IRef α → IExpr α

data IStatement : Set where
  ifthenelse : IExpr Bool → IStatement → IStatement → IStatement
  assignment : ∀ { α } → IRef α → IExpr α → IStatement
  sequence : IStatement → IStatement → IStatement
  declaration : (α : c_type) → IRef α → IStatement → IStatement
  for : IRef Int → IExpr Int → IExpr Int → IStatement → IStatement
  while : IExpr Bool → IStatement → IStatement
  nop : IStatement

AST-C : C
C.Expr AST-C α = IExpr α
C.Ref AST-C α = IRef α
C.Statement AST-C = ℕ → ℕ × IStatement
C.⟨_⟩ AST-C x = lit x
C._+_ AST-C x y = add x y
C._*_ AST-C x y = mul x y
C._-_ AST-C x y = sub x y
C._/_ AST-C x y = div x y
C._<_ AST-C x y = lt x y
C._<=_ AST-C x y = lte x y
C._>_ AST-C x y = gt x y
C._>=_ AST-C x y = gte x y
C._==_ AST-C x y = eq x y
C.true AST-C = true
C.false AST-C = false
C._||_ AST-C x y = or x y
C._&&_ AST-C x y = and x y
C.!_ AST-C x = not x
C._[_] AST-C (r , l) i = r , i ∷ l
C.★_ AST-C x = deref x
C._≔_ AST-C x y n = n , assignment x y
C.if_then_else_ AST-C e x y n =
  let n , x = x n in
  let n , y = y n in
    n , ifthenelse e x y
C._；_ AST-C x y n =
  let n , x = x n in
  let n , y = y n in
    n , sequence x y
C.decl AST-C α f n =
  let ref = (n , []) in
  let n , f = f ref (ℕ.suc n) in
    n , declaration α ref f
C.nop AST-C n = n , nop
C.for_to_then_ AST-C l u f n =
  let ref = (n , []) in
  let n , f = f ref (ℕ.suc n) in
    n , for ref l u f
C.while_then_ AST-C e f n =
  let n , f = f n in
    n , while e f

toAST : (∀ ⦃ ℐ ⦄ → C.Statement ℐ) → IStatement
toAST s = proj₂ ((s ⦃ AST-C ⦄) 0)
