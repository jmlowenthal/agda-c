open import Level as Level using (Level; suc; _⊔_)
open import Data.Maybe as Maybe using (Maybe)
open import Data.Nat as ℕ using (ℕ)
open import Data.Integer as ℤ using (ℤ)
open import Data.List as List using (List; []; _∷_)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Product as Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)


_⇉_[_] : ∀ {t e l n} {Type : Set t} → Vec Type n → Set l → (Expr : Type → Set e) → Set (e ⊔ l)
_⇉_[_] {e = e} [] τ Expr = Level.Lift e τ
(h ∷ t) ⇉ τ [ Expr ] = Expr h → (t ⇉ τ [ Expr ])


record Lang (t v e f l s : Level) : Set (suc (t ⊔ v ⊔ e ⊔ f ⊔ l ⊔ s)) where
  field
    Type : Set t
    Expr : Type → Set e
    Variable : Type → Set v
    Function : ∀ n → Vec Type n → Type → Set f
    Label : Set l
    Statement : Set s
  
    Int : Type
    Float : Type

    id : ∀ {τ} → Variable τ → Expr τ
    cst : ℤ → Expr Int
    mem-read : ∀ τ → Expr Int → Expr τ
    tenary : ∀ {α β} → Expr α → Expr β → Expr β → Expr β

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

    skip : Statement
    assignment : ∀ {τ} → Variable τ → Expr τ → Statement
    mem-write : ∀ {τ} → Expr Int → Expr τ → Statement
    func-call : ∀ { n A β } → Maybe (Variable β) → Function n A β → A ⇉ Statement [ Expr ]
    tailcall : ∀ { n A β } → Function n A β → A ⇉ Statement [ Expr ]
    return : ∀ {τ} → Maybe (Expr τ) → Statement
    sequence : Statement → Statement → Statement
    if-else : Expr Int → Statement → Statement → Statement
    loop : Statement → Statement
    block : Statement → Statement
    exit : ℕ → Statement
    switch : Expr Int → List (ℕ × ℕ) → Statement
    label : Label → Statement → Statement
    goto : Label → Statement


module Example {a b c d e f} (L : Lang a b c d e f) where
  -- Example from Leroy et al
  -- ```
  -- // C:
  -- double average(int arr[], int sz) {
  --   double s; int i;
  --   for (i = 0, s = 0; i < sz; i++)
  --     s += arr[i];
  --   return s / sz;
  -- }
  -- // CMinor:
  -- "average"(arr, sz) : int, int -> float {
  -- vars s, i; stacksize 0;
  -- s = 0.0; i = 0;
  -- block { loop {
  --   if (i >= sz) exit(0);
  --   s = s +. floatofint(int32[arr + i * 4]);
  --   i = i + 1;
  -- } }
  -- return s /. floatofint(sz)
  -- ```
  open Lang L
  average : Function 2 (Int ∷ Int ∷ []) Float
  average = {!!}
