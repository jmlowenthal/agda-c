module Print.AST where

open import C
open import Data.Nat as ℕ using (ℕ)
open import Data.Integer as ℤ using (ℤ)
open import Data.String
open import Data.List using (List ; _∷_ ; [])
open import Data.Product
open import Relation.Nullary
open import Relation.Binary
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
  tenary : ∀ { α } → IExpr Bool → IExpr α → IExpr α → IExpr α

data IStatement : Set where
  ifthenelse : IExpr Bool → IStatement → IStatement → IStatement
  assignment : ∀ { α } → IRef α → IExpr α → IStatement
  sequence : IStatement → IStatement → IStatement
  declaration : (α : c_type) → IRef α → IStatement → IStatement
  for : IRef Int → IExpr Int → IExpr Int → IStatement → IStatement
  while : IExpr Bool → IStatement → IStatement
  nop : IStatement
  putchar : IExpr Int → IStatement

AST-C : C
C.Expr AST-C α = IExpr α
C.Ref AST-C α = IRef α
C.Statement AST-C = ℕ → ℕ × IStatement
C.⟪_⟫ AST-C x = lit x
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
C._⁇_∷_ AST-C c x y = tenary c x y
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
C.putchar AST-C x n = n , putchar x

toAST : (∀ ⦃ ℐ ⦄ → C.Statement ℐ) → IStatement
toAST s = proj₂ ((s ⦃ AST-C ⦄) 0)

≟-List : ∀ { a } { A : Set a }
  → Decidable (λ (a b : A) → a ≡ b) → Decidable (λ (a b : List A) → a ≡ b)
≟-List ≟-A [] [] = yes refl
≟-List ≟-A [] (x ∷ b) = no λ ()
≟-List ≟-A (x ∷ a) [] = no λ ()
≟-List ≟-A (x ∷ a) (y ∷ b) with ≟-A x y
... | no ¬p = no λ { refl → ¬p refl }
... | yes refl with ≟-List ≟-A a b
...   | no ¬p = no λ { refl → ¬p refl }
...   | yes refl = yes refl

≟-IExpr : ∀ { α } → Decidable (λ (a b : IExpr α) → a ≡ b)

≟-IRef : ∀ { α } → Decidable (λ ( a b : IRef α ) → a ≡ b)
≟-IRef (n , a) (m , b) with n ℕ.≟ m | ≟-List ≟-IExpr a b
... | yes refl | yes refl = yes refl
... | yes refl | no ¬q = no λ { refl → ¬q refl }
... | no ¬p | _ = no λ { refl → ¬p refl }

≟-IExpr (lit x) (lit y) with x ℤ.≟ y
... | yes refl = yes refl
... | no ¬p = no λ { refl → ¬p refl }
≟-IExpr (lit _) (add _ _) = no λ ()
≟-IExpr (lit _) (mul _ _) = no λ ()
≟-IExpr (lit _) (sub _ _) = no λ ()
≟-IExpr (lit _) (div _ _) = no λ ()
≟-IExpr (lit _) (deref x₁) = no λ ()
≟-IExpr (lit _) (tenary _ _ _) = no λ ()
≟-IExpr (add _ _) (lit _) = no λ ()
≟-IExpr (add a b) (add x y) with ≟-IExpr a x | ≟-IExpr b y
... | yes refl | yes refl = yes refl
... | yes refl | no ¬p = no λ { refl → ¬p refl }
... | no ¬p | _ = no λ { refl → ¬p refl }
≟-IExpr (add _ _) (mul _ _) = no λ ()
≟-IExpr (add _ _) (sub _ _) = no λ ()
≟-IExpr (add _ _) (div _ _) = no λ ()
≟-IExpr (add _ _) (deref _) = no λ ()
≟-IExpr (add _ _) (tenary _ _ _) = no λ ()
≟-IExpr (mul _ _) (lit _) = no λ ()
≟-IExpr (mul _ _) (add _ _) = no λ ()
≟-IExpr (mul a b) (mul x y)  with ≟-IExpr a x | ≟-IExpr b y
... | yes refl | yes refl = yes refl
... | yes refl | no ¬p = no λ { refl → ¬p refl }
... | no ¬p | _ = no λ { refl → ¬p refl }
≟-IExpr (mul _ _) (sub _ _) = no λ ()
≟-IExpr (mul _ _) (div _ _) = no λ ()
≟-IExpr (mul _ _) (deref _) = no λ ()
≟-IExpr (mul _ _) (tenary _ _ _) = no λ ()
≟-IExpr (sub _ _) (lit _) = no λ ()
≟-IExpr (sub _ _) (add _ _) = no λ ()
≟-IExpr (sub _ _) (mul _ _) = no λ ()
≟-IExpr (sub x y) (sub a b) with ≟-IExpr a x | ≟-IExpr b y
... | yes refl | yes refl = yes refl
... | yes refl | no ¬p = no λ { refl → ¬p refl }
... | no ¬p | _ = no λ { refl → ¬p refl }
≟-IExpr (sub _ _) (div _ _) = no λ ()
≟-IExpr (sub _ _) (deref _) = no λ ()
≟-IExpr (sub _ _) (tenary _ _ _) = no λ ()
≟-IExpr (div _ _) (lit _) = no λ ()
≟-IExpr (div _ _) (add _ _) = no λ ()
≟-IExpr (div _ _) (mul _ _) = no λ ()
≟-IExpr (div _ _) (sub _ _) = no λ ()
≟-IExpr (div a b) (div x y) with ≟-IExpr a x | ≟-IExpr b y
... | yes refl | yes refl = yes refl
... | yes refl | no ¬p = no λ { refl → ¬p refl }
... | no ¬p | _ = no λ { refl → ¬p refl }
≟-IExpr (div _ _) (deref _) = no λ ()
≟-IExpr (div _ _) (tenary _ _ _) = no λ ()
≟-IExpr (lt a b) (lt x y) with ≟-IExpr a x | ≟-IExpr b y
... | yes refl | yes refl = yes refl
... | yes refl | no ¬p = no λ { refl → ¬p refl }
... | no ¬p | _ = no λ { refl → ¬p refl }
≟-IExpr (lt _ _) (lte _ _) = no λ ()
≟-IExpr (lt _ _) (gt _ _) = no λ ()
≟-IExpr (lt _ _) (gte _ _) = no λ ()
≟-IExpr (lt _ _) (eq _ _) = no λ ()
≟-IExpr (lt _ _) true = no λ ()
≟-IExpr (lt _ _) false = no λ ()
≟-IExpr (lt _ _) (or _ _) = no λ ()
≟-IExpr (lt _ _) (and _ _) = no λ ()
≟-IExpr (lt _ _) (not _) = no λ ()
≟-IExpr (lt _ _) (deref _) = no λ ()
≟-IExpr (lt _ _) (tenary _ _ _) = no λ ()
≟-IExpr (lte _ _) (lt _ _) = no λ ()
≟-IExpr (lte a b) (lte x y) with ≟-IExpr a x | ≟-IExpr b y
... | yes refl | yes refl = yes refl
... | yes refl | no ¬p = no λ { refl → ¬p refl }
... | no ¬p | _ = no λ { refl → ¬p refl }
≟-IExpr (lte _ _) (gt _ _) = no λ ()
≟-IExpr (lte _ _) (gte _ _) = no λ ()
≟-IExpr (lte _ _) (eq _ _) = no λ ()
≟-IExpr (lte _ _) true = no λ ()
≟-IExpr (lte _ _) false = no λ ()
≟-IExpr (lte _ _) (or _ _) = no λ ()
≟-IExpr (lte _ _) (and _ _) = no λ ()
≟-IExpr (lte _ _) (not _) = no λ ()
≟-IExpr (lte _ _) (deref _) = no λ ()
≟-IExpr (lte _ _) (tenary _ _ _) = no λ ()
≟-IExpr (gt _ _) (lt _ _) = no λ ()
≟-IExpr (gt _ _) (lte _ _) = no λ ()
≟-IExpr (gt a b) (gt x y) with ≟-IExpr a x | ≟-IExpr b y
... | yes refl | yes refl = yes refl
... | yes refl | no ¬p = no λ { refl → ¬p refl }
... | no ¬p | _ = no λ { refl → ¬p refl }
≟-IExpr (gt _ _) (gte _ _) = no λ ()
≟-IExpr (gt _ _) (eq _ _) = no λ ()
≟-IExpr (gt _ _) true = no λ ()
≟-IExpr (gt _ _) false = no λ ()
≟-IExpr (gt _ _) (or _ _) = no λ ()
≟-IExpr (gt _ _) (and _ _) = no λ ()
≟-IExpr (gt _ _) (not _) = no λ ()
≟-IExpr (gt _ _) (deref _) = no λ ()
≟-IExpr (gt _ _) (tenary _ _ _) = no λ ()
≟-IExpr (gte _ _) (lt _ _) = no λ ()
≟-IExpr (gte _ _) (lte _ _) = no λ ()
≟-IExpr (gte _ _) (gt _ _) = no λ ()
≟-IExpr (gte a b) (gte x y) with ≟-IExpr a x | ≟-IExpr b y
... | yes refl | yes refl = yes refl
... | yes refl | no ¬p = no λ { refl → ¬p refl }
... | no ¬p | _ = no λ { refl → ¬p refl }
≟-IExpr (gte _ _) (eq _ _) = no λ ()
≟-IExpr (gte _ _) true = no λ ()
≟-IExpr (gte _ _) false = no λ ()
≟-IExpr (gte _ _) (or _ _) = no λ ()
≟-IExpr (gte _ _) (and _ _) = no λ ()
≟-IExpr (gte _ _) (not _) = no λ ()
≟-IExpr (gte _ _) (deref _) = no λ ()
≟-IExpr (gte _ _) (tenary _ _ _) = no λ ()
≟-IExpr (eq _ _) (lt _ _) = no λ ()
≟-IExpr (eq _ _) (lte _ _) = no λ ()
≟-IExpr (eq _ _) (gt _ _) = no λ ()
≟-IExpr (eq _ _) (gte _ _) = no (λ ())
≟-IExpr (eq a b) (eq x y) with ≟-IExpr a x | ≟-IExpr b y
... | yes refl | yes refl = yes refl
... | yes refl | no ¬p = no λ { refl → ¬p refl }
... | no ¬p | _ = no λ { refl → ¬p refl }
≟-IExpr (eq _ _) true = no (λ ())
≟-IExpr (eq _ _) false = no (λ ())
≟-IExpr (eq _ _) (or _ _) = no (λ ())
≟-IExpr (eq _ _) (and _ _) = no (λ ())
≟-IExpr (eq _ _) (not _) = no (λ ())
≟-IExpr (eq _ _) (deref _) = no (λ ())
≟-IExpr (eq _ _) (tenary _ _ _) = no (λ ())
≟-IExpr true (lt _ _) = no (λ ())
≟-IExpr true (lte _ _) = no (λ ())
≟-IExpr true (gt _ _) = no (λ ())
≟-IExpr true (gte _ _) = no (λ ())
≟-IExpr true (eq _ _) = no (λ ())
≟-IExpr true true = yes refl
≟-IExpr true false = no (λ ())
≟-IExpr true (or _ _) = no (λ ())
≟-IExpr true (and _ _) = no (λ ())
≟-IExpr true (not _) = no (λ ())
≟-IExpr true (deref _) = no (λ ())
≟-IExpr true (tenary _ _ _) = no (λ ())
≟-IExpr false (lt _ _) = no (λ ())
≟-IExpr false (lte _ _) = no (λ ())
≟-IExpr false (gt _ _) = no (λ ())
≟-IExpr false (gte _ _) = no (λ ())
≟-IExpr false (eq _ _) = no (λ ())
≟-IExpr false true = no (λ ())
≟-IExpr false false = yes refl
≟-IExpr false (or _ _) = no (λ ())
≟-IExpr false (and _ _) = no (λ ())
≟-IExpr false (not _) = no (λ ())
≟-IExpr false (deref _) = no (λ ())
≟-IExpr false (tenary _ _ _) = no (λ ())
≟-IExpr (or _ _) (lt _ _) = no (λ ())
≟-IExpr (or _ _) (lte _ _) = no (λ ())
≟-IExpr (or _ _) (gt _ _) = no (λ ())
≟-IExpr (or _ _) (gte _ _) = no (λ ())
≟-IExpr (or _ _) (eq _ _) = no (λ ())
≟-IExpr (or _ _) true = no (λ ())
≟-IExpr (or _ _) false = no (λ ())
≟-IExpr (or a b) (or x y) with ≟-IExpr a x | ≟-IExpr b y
... | yes refl | yes refl = yes refl
... | yes refl | no ¬p = no λ { refl → ¬p refl }
... | no ¬p | _ = no λ { refl → ¬p refl }
≟-IExpr (or _ _) (and _ _) = no (λ ())
≟-IExpr (or _ _) (not _) = no (λ ())
≟-IExpr (or _ _) (deref _) = no (λ ())
≟-IExpr (or _ _) (tenary _ _ _) = no (λ ())
≟-IExpr (and _ _) (lt _ _) = no (λ ())
≟-IExpr (and _ _) (lte _ _) = no (λ ())
≟-IExpr (and _ _) (gt _ _) = no (λ ())
≟-IExpr (and _ _) (gte _ _) = no (λ ())
≟-IExpr (and _ _) (eq _ _) = no (λ ())
≟-IExpr (and _ _) true = no (λ ())
≟-IExpr (and _ _) false = no (λ ())
≟-IExpr (and _ _) (or _ _) = no (λ ())
≟-IExpr (and a b) (and x y) with ≟-IExpr a x | ≟-IExpr b y
... | yes refl | yes refl = yes refl
... | yes refl | no ¬p = no λ { refl → ¬p refl }
... | no ¬p | _ = no λ { refl → ¬p refl }
≟-IExpr (and _ _) (not _) = no (λ ())
≟-IExpr (and _ _) (deref _) = no (λ ())
≟-IExpr (and _ _) (tenary _ _ _) = no (λ ())
≟-IExpr (not _) (lt _ _) = no (λ ())
≟-IExpr (not _) (lte _ _) = no (λ ())
≟-IExpr (not _) (gt _ _) = no (λ ())
≟-IExpr (not _) (gte _ _) = no (λ ())
≟-IExpr (not _) (eq _ _) = no (λ ())
≟-IExpr (not _) true = no (λ ())
≟-IExpr (not _) false = no (λ ())
≟-IExpr (not _) (or _ _) = no (λ ())
≟-IExpr (not _) (and _ _) = no (λ ())
≟-IExpr (not a) (not b) with ≟-IExpr a b
... | yes refl = yes refl
... | no ¬p = no λ { refl → ¬p refl }
≟-IExpr (not _) (deref _) = no (λ ())
≟-IExpr (not _) (tenary _ _ _) = no (λ ())
≟-IExpr (deref _) (lit _) = no (λ ())
≟-IExpr (deref _) (add _ _) = no (λ ())
≟-IExpr (deref _) (mul _ _) = no (λ ())
≟-IExpr (deref _) (sub _ _) = no (λ ())
≟-IExpr (deref _) (div _ _) = no (λ ())
≟-IExpr (deref _) (lt _ _) = no (λ ())
≟-IExpr (deref _) (lte _ _) = no (λ ())
≟-IExpr (deref _) (gt _ _) = no (λ ())
≟-IExpr (deref _) (gte _ _) = no (λ ())
≟-IExpr (deref _) (eq _ _) = no (λ ())
≟-IExpr (deref _) true = no (λ ())
≟-IExpr (deref _) false = no (λ ())
≟-IExpr (deref _) (or _ _) = no (λ ())
≟-IExpr (deref _) (and _ _) = no (λ ())
≟-IExpr (deref _) (not _) = no (λ ())
≟-IExpr {α} (deref a) (deref b) =
  ∨-dec (helper a b)
  where
    helper : Decidable (λ (a b : IRef α) → a ≡ b)
    helper (n , a) (m , b) with n ℕ.≟ m | ≟-List ≟-IExpr a b
    ... | _ | _ = {!!}
    ∨-dec : ∀ { a b : IRef α } → Dec (a ≡ b) → Dec (deref a ≡ deref b)
    ∨-dec (yes refl) = yes refl
    ∨-dec (no ¬p) = no λ { refl → ¬p refl }
≟-IExpr (deref _) (tenary _ _ _) = no (λ ())
≟-IExpr (tenary _ _ _) (lit _) = no (λ ())
≟-IExpr (tenary _ _ _) (add _ _) = no (λ ())
≟-IExpr (tenary _ _ _) (mul _ _) = no (λ ())
≟-IExpr (tenary _ _ _) (sub _ _) = no (λ ())
≟-IExpr (tenary _ _ _) (div _ _) = no (λ ())
≟-IExpr (tenary _ _ _) (lt _ _) = no (λ ())
≟-IExpr (tenary _ _ _) (lte _ _) = no (λ ())
≟-IExpr (tenary _ _ _) (gt _ _) = no (λ ())
≟-IExpr (tenary _ _ _) (gte _ _) = no (λ ())
≟-IExpr (tenary _ _ _) (eq _ _) = no (λ ())
≟-IExpr (tenary _ _ _) true = no (λ ())
≟-IExpr (tenary _ _ _) false = no (λ ())
≟-IExpr (tenary _ _ _) (or _ _) = no (λ ())
≟-IExpr (tenary _ _ _) (and _ _) = no (λ ())
≟-IExpr (tenary _ _ _) (not _) = no (λ ())
≟-IExpr (tenary _ _ _) (deref _) = no (λ ())
≟-IExpr (tenary a b c) (tenary x y z) with ≟-IExpr a x | ≟-IExpr b y | ≟-IExpr c z
... | yes refl | yes refl | yes refl = yes refl
... | yes refl | yes refl | no ¬p = no λ { refl → ¬p refl }
... | yes refl | no ¬p | _ = no λ { refl → ¬p refl }
... | no ¬p | _ | _ = no λ { refl → ¬p refl }

