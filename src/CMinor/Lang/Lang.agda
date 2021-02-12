open import Data.Float using () renaming (Float to 𝔽)
open import Data.Integer as ℤ using (ℤ)
open import Data.List as List using (List; []; _∷_)
open import Data.Maybe as Maybe using (Maybe)
open import Data.Nat as ℕ using (ℕ)
open import Data.Nat.Binary as ℕᵇ using (ℕᵇ)
open import Data.Product as Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Level as Level using (Level; suc; _⊔_)

module CMinor.Lang.Lang where

Arrows : ∀ {t e l n} {Type : Set t} → Vec Type n → Set l → (T : Type → Set e) → Set (e ⊔ l)
Arrows {e = e} [] τ T = Level.Lift e τ
Arrows (h ∷ t) τ T = T h → (Arrows t τ T)


record Lang (t v c e f l s : Level) : Set (suc (t ⊔ v ⊔ c ⊔ e ⊔ f ⊔ l ⊔ s)) where
  field
    Type : Set t
    Constant : Type → Set c
    Expr : Type → Set e
    Variable : Type → Set v
    Function : ∀ n → Vec Type n → Type → Set f
    Label : Set l
    Statement : Set s

    -- TODO: consider if Statement : Maybe Type → Set s -- Is it possible to define a refinement of this record type with this restriction? It should be.
    
  infixr 0 _⇉_
  _⇉_ : ∀ {n l} → Vec Type n → Set l → Set (v ⊔ l)
  x ⇉ y = Arrows x y Variable

  field
    Int : Type
    Float : Type

    id : ∀ {τ} → Variable τ → Expr τ
    mem-read : ∀ τ → Expr Int → Expr τ -- κ[a]
    tenary : ∀ {α} → Expr Int → Expr α → Expr α → Expr α

    -- op₁(a₁)
    negint notint notbool : Expr Int → Expr Int
    negf absf : Expr Float → Expr Float
    cast8u cast8s cast16u cast16s : Expr Int → Expr Int
    singleoffloat : Expr Float → Expr Float
    intoffloat intuoffloat : Expr Float → Expr Int
    floatofint floatofintu : Expr Int → Expr Float

    -- op₂(a₁, a₂)
    add sub mul div divu mod modu : Expr Int → Expr Int → Expr Int
    and or xor shl shr shru : Expr Int → Expr Int → Expr Int
    addf subf mulf divf : Expr Float → Expr Float → Expr Float
    cmp-== cmp-!= cmp-> cmp->= cmp-< cmp-<= : Expr Int → Expr Int → Expr Int
    cmpu-== cmpu-!= cmpu-> cmpu->= cmpu-< cmpu-<= : Expr Int → Expr Int → Expr Int
    cmpf-== cmpf-!= cmpf-> cmpf->= cmpf-< cmpf-<= : Expr Float → Expr Float → Expr Float

    -- cst
    cst : ∀ {α} → Constant α → Expr α
    cst-int : ℕᵇ → Constant Int
    cst-float : 𝔽 → Constant Float
    -- addrsymbol : ? → ?
    addrstack : ℕᵇ → Constant Int -- returns a pointer into the function stack

    skip : Statement
    assignment : ∀ {τ} → Variable τ → Expr τ → Statement
    mem-write : ∀ {τ} → Expr Int → Expr τ → Statement
    func-call : ∀ { n A β } → Maybe (Variable β) → Function n A β → A ⇉ Statement
    tailcall : ∀ { n A β } → Function n A β → A ⇉ Statement
    return : ∀ {τ} → Maybe (Expr τ) → Statement
    sequence : Statement → Statement → Statement
    if-else : Expr Int → Statement → Statement → Statement
    loop : Statement → Statement
    block : Statement → Statement
    exit : ℕ → Statement
    switch : Expr Int → List (ℕ × ℕ) → Statement
    label : Label → Statement → Statement
    goto : Label → Statement

    define-function : ∀ {n m} (params : Vec Type n) ret (vars : Vec Type m) → ℕ → params Vec.++ vars ⇉ Statement → Function n params ret

  _⇒_ : ∀ {n} → Vec Type n → Type → Set f
  _⇒_ {n} = Function n

