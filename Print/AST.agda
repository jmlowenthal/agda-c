module Print.AST where

open import C
open import Data.Integer
open import Data.String

data IExpr : c_type → Set

data IRef : c_type → Set where
  index : ∀ { α n } → IRef (Array α n) → IExpr Int → IRef α
  var : ∀ { α } → String → IRef α

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
  declaration : (α : c_type) → (IRef α → IStatement) → IStatement
  for : IExpr Int → IExpr Int → (IRef Int → IStatement) → IStatement
  while : IExpr Bool → IStatement → IStatement
  nop : IStatement

AST-C : C
C.Expr AST-C α = IExpr α
C.Ref AST-C α = IRef α
C.Statement AST-C = IStatement
C.⟨_⟩ AST-C = lit
C._+_ AST-C = add
C._*_ AST-C = mul
C._-_ AST-C = sub
C._/_ AST-C = div
C._<_ AST-C = lt
C._<=_ AST-C = lte
C._>_ AST-C = gt
C._>=_ AST-C = gte
C._==_ AST-C = eq
C.true AST-C = true
C.false AST-C = false
C._||_ AST-C = or
C._&&_ AST-C = and
C.! AST-C = not
C._[_] AST-C = index
C.★ AST-C = deref
C._≔_ AST-C = assignment
C.if_then_else_ AST-C = ifthenelse
C._；_ AST-C = sequence
C.decl AST-C = declaration
C.nop AST-C = nop
C.for_to_then_ AST-C = for
C.while_then_ AST-C = while
