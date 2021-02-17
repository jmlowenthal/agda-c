{-# OPTIONS --safe --exact-split --sized-types #-}

module Print.Eval where

open import Size
import Level

open import C using (Lang ; c_type ; Array ; Int ; Bool)
open import C.Semantics.SmallStep.Model.State using (⟦_⟧)
open import Codata.Cowriter
open import Codata.Thunk
open import Data.Bool using (true ; false ; not ; _∨_ ; _∧_) renaming (Bool to 𝔹 ; if_then_else_ to If_Then_Else_)
open import Data.Integer as ℤ using (ℤ ; 1ℤ)
open import Data.Maybe using ()
open import Data.Product
open import Data.Unit using (tt)
open import Data.Vec using ([] ; _∷_)
open import Data.Nat as ℕ using (ℕ)
open import Data.String using (String ; fromChar)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Function

import Data.Integer.Properties as ℤₚ
import Data.Integer.DivMod as ℤ÷
import Data.Nat as ℕ
import Data.Char as Char

divide : ℤ → ℤ → ℤ
divide x (ℤ.pos 0) = ℤ.+ 0 -- Implementation defined
divide x y@(ℤ.+[1+ n ]) = (x ℤ÷.div y) {tt}
divide x y@(ℤ.negsuc n) = (x ℤ÷.div y) {tt}

module Var where
  data Var (α : c_type) : Set where
    var : ℕ → Var α
    index : ∀ { n } → Var (Array α n) → ℤ → Var α

  AnyVar : Set
  AnyVar = ∃[ α ] Var α

  depth : ∀ { α } → Var α → ℕ
  depth (var _) = 0
  depth (index x _) = ℕ.suc (depth x)

  _≟_ : ∀ { α } (x : Var α) (y : Var α) → Dec (x ≡ y)
  var a       ≟ var b       with a ℕ.≟ b
  ... | yes refl = yes refl
  ... | no   a≢b = no λ { refl → a≢b refl }
  var _       ≟ index _ _   = no λ ()
  index _  _  ≟ var _       = no λ ()
  index {n₁} r₁ i₁ ≟ index {n₂} r₂ i₂ with n₁ ℕ.≟ n₂
  ... | no n₁≢n₂ = no λ { refl → n₁≢n₂ refl }
  ... | yes refl with i₁ ℤ.≟ i₂
  ... | no i₁≢i₂ = no λ { refl → i₁≢i₂ refl }
  ... | yes refl with r₁ ≟ r₂
  ... | no r₁≢r₂ = no λ { refl → r₁≢r₂ refl }
  ... | yes refl = yes refl

  _≟′_ : ∀ (x y : AnyVar) → Dec (x ≡ y)
  _≟′_ (α , x) (β , y) with α C.≟ β
  ... | no   α≢β = no λ { refl → α≢β refl }
  ... | yes refl with x ≟ y
  ... | no  x≢y = no λ { refl → x≢y refl }
  ... | yes refl = yes refl

open Var

module Env where
  Env : Set
  Env = ∀ { α } → Var α → ⟦ α ⟧

  bind : ∀ { α } → Env → Var α → ⟦ α ⟧ → Env
  bind E b v r with (_ , r) ≟′ (_ , b)
  ... | yes refl = v
  ... | no _ = E r

  -- Default base environment
  E0 : Env
  E0 {Int} _ = ℤ.+ 0
  E0 {Bool} _ = 𝔹.false
  E0 {Array α ℕ.zero} _ = []
  E0 {Array α (ℕ.suc n)} _ = E0 {α} (var 0) ∷ E0 (var 0)

open Env

Expr : c_type → Set
Expr α = Env → ⟦ α ⟧

record State : Set where
  constructor MkState
  field
    output : String
    next  : ℕ
    env    : Env

  fresh : ∀ { α } → State × Var α
  fresh = record { output = output ; next = ℕ.suc next ; env = env } , var next

open State

Evolution : ∀ { i : Size } → Set
Evolution {i} = Cowriter State State i

module Statement where
  Statement : ∀ { i : Size } → Set
  Statement {i} = State → Evolution {i}

  _；_ : ∀ { i } → Statement {i} → Statement {i} → Statement {i}
  (fst ； snd) s = ([ s ] >>= fst) >>= snd

  nop : Statement
  nop = [_]

  infixr 1 _；_

open Statement

module Ref where
  Ref : c_type → Set
  Ref α = Env → Var α

  decl : ∀ α → (Ref α → Statement) → Statement
  decl _ binder s = let new , fresh = fresh s in binder (const fresh) new

  _≔_ : ∀ { α } → Ref α → Expr α → Statement
  (r ≔ e) s = [ record s { env = let E = env s in bind E (r E) (e E) } ]

  ★_ : ∀ { α } → Ref α → Expr α
  (★ r) E = E (r E)

open Ref

⟪_⟫ : ℤ → Expr Int
⟪ x ⟫ = const x

_+_ : Expr Int → Expr Int → Expr Int
(x + y) E = x E ℤ.+ y E

_++ : Ref Int → Statement
r ++ = r ≔ ((★ r) + ⟪ 1ℤ ⟫)

_-_ : Expr Int → Expr Int → Expr Int
(x - y) E = x E ℤ.- y E

_≥_ : Expr Int → Expr Int → Expr Bool
(x ≥ y) E = ⌊ y E ℤ.≤? x E ⌋

if_then_else_ : ∀ { i } → Expr Bool → Statement {i} → Statement {i} → Statement {i}
(if cond then pos else neg) s with cond (env s)
... | true  = pos s
... | false = neg s

loop : ∀ { i } → Expr Bool → Statement {i} → Statement {i}
-- TODO: ugh so ugly... make a combinator
loop cond body = if cond then (λ s → body s >>= λ s → s ∷ λ where .force {j} → loop {j} cond body s) else nop

iter : ℤ → Expr Int → (Ref Int → Statement) → Statement
iter base upper f = decl Int λ r → (r ≔ const base) ； loop (upper ≥ (★ r)) (f r ； r ++)

Eval-C : Lang
Lang.Ref Eval-C = Ref
Lang.Expr Eval-C = Expr
Lang.Statement Eval-C = Statement
Lang.⟪_⟫ Eval-C = ⟪_⟫
Lang._+_ Eval-C = _+_
Lang._*_ Eval-C x y E = x E ℤ.* y E
Lang._-_ Eval-C = _-_
Lang._/_ Eval-C x y E = divide (x E) (y E)
Lang._<_ Eval-C x y E = ⌊ x E ℤ.<? y E ⌋
Lang._<=_ Eval-C x y E = ⌊ x E ℤ.≤? y E ⌋
Lang._>_ Eval-C x y E = ⌊ y E ℤ.<? x E ⌋
Lang._>=_ Eval-C x y E = ⌊ y E ℤ.≤? x E ⌋
Lang._==_ Eval-C x y E = ⌊ x E ℤ.≟ y E ⌋
Lang.true Eval-C E = 𝔹.true
Lang.false Eval-C E = 𝔹.false
Lang._||_ Eval-C x y E = x E ∨ y E
Lang._&&_ Eval-C x y E = x E ∧ y E
Lang.!_ Eval-C x E = not (x E)
Lang._[_] Eval-C r i E = index (r E) (i E)
Lang.★_ Eval-C x E = E (x E)
Lang._⁇_∷_ Eval-C c x y E with c E
... | true  = x E
... | false = y E
Lang._≔_ Eval-C = _≔_
Lang.if_then_else_ Eval-C = if_then_else_
Lang._；_ Eval-C = _；_
Lang.decl Eval-C = decl
Lang.nop Eval-C = nop
Lang.for_to_then_ Eval-C l u f s = iter (l (env s)) u f s
Lang.while_then_ Eval-C = loop
Lang.putchar Eval-C x s =
  [ record s
    { output = output s Data.String.++ fromChar (Char.fromℕ ℤ.∣ (x (env s)) ℤ.⊔ (ℤ.+ 0) ∣)
    } ]
