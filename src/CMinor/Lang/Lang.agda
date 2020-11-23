open import Level as Level using (Level; suc; _⊔_)
open import Data.Maybe as Maybe using (Maybe)
open import Data.Nat as ℕ using (ℕ)
open import Data.Integer as ℤ using (ℤ)
open import Data.List as List using (List; []; _∷_)
open import Data.Product as Product using (_×_; _,_)
open import Function.Nary.NonDependent as Nary using (Sets; _⇉_)

record Lang (t v e s : Level) : Set (suc (t ⊔ v ⊔ e ⊔ s)) where
  field
    τ : Set t
    Int : τ
    Float : τ
    
    Expr : τ → Set e
    Variable : τ → Set v
    Function : List τ → τ → Set
    Label : Set

    id : ∀ { τ } → Variable τ → Expr τ
    cst : ℤ → Expr Int

    negint notint notbool : Expr Int → Expr Int
    negf absf : Expr Float → Expr Float
    cast8u cast8s cast16u cast16s : Expr Int → Expr Int
    singleoffloat : Expr Float → Expr Float
    intoffloat intuoffloat : Expr Float → Expr Int
    floatofint floatofintu : Expr Int → Expr Float

    add sub mul div divu mod modu : Expr Int → Expr Int → Expr Int
    and or xor shl shr shru : Expr Int → Expr Int → Expr Int
    addf subf mulf divf : Expr Float → Expr Float → Expr Float
    cmp-== cmp-!= cmp-> cmp->= cmp-< cmp-<= : Expr Int → Expr Int → Expr Int
    cmpu-== cmpu-!= cmpu-> cmpu->= cmpu-< cmpu-<= : Expr Int → Expr Int → Expr Int
    cmpf-== cmpf-!= cmpf-> cmpf->= cmpf-< cmpf-<= : Expr Float → Expr Float → Expr Float

    Statement : Set s
    skip : Statement
    assignment : ∀ { τ } → Variable τ → Expr τ → Statement
    mem-write : ∀ { τ } → Expr Int → Expr τ → Statement
    func-call : ∀ { A β } → Maybe (Variable β) → Function A β → {!List.map ? A!} ⇉ Statement
    tailcall : ∀ { α β } → Function α β → {!Expr α!} → Statement -- call and return
    return : ∀ { τ } → Maybe (Expr τ) → Statement
    sequence : Statement → Statement → Statement
    if-else : Expr Int → Statement → Statement → Statement
    loop : Statement → Statement
    block : Statement → Statement
    exit : ℕ → Statement
    switch : Expr Int → List (ℕ × ℕ) → Statement
    label : Label → Statement → Statement
    goto : Label → Statement
