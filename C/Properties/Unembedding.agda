-- Based on https://www.cl.cam.ac.uk/~jdy22/papers/unembedding.pdf

module C.Properties.Unembedding where

open import C

open import Data.Bool using () renaming (Bool to 𝔹 ; true to True ; false to False)
open import Data.Empty
open import Data.Fin as 𝔽 using (Fin)
open import Data.Integer as ℤ using (ℤ)
open import Data.Maybe
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Unit using (⊤ ; tt)
open import Data.Vec hiding (_>>=_)
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

data Ctx : ∀ n → Vec c_type n → Set where
  wrap : ∀ { n } (v : Vec c_type n) → Ctx n v

data Expr : ∀ n → Vec c_type n → c_type → Set

data IRef : ∀ n → Vec c_type n → c_type → Set where
  zero : ∀ { n α l } → IRef (suc n) (α ∷ l) α
  suc : ∀ { n ctx α β } → IRef n ctx α → IRef (suc n) (β ∷ ctx) α
  arr : ∀ { n ctx α m } → IRef n ctx (Array α m) → Expr n ctx Int → IRef n ctx α

abstract

  Ref : ∀ n → Vec c_type n → c_type → Set
  Ref = IRef

  index : ∀ { n ctx α m } → Ref n ctx (Array α m) → Expr n ctx Int → Ref n ctx α
  index = arr

  ref-contra : ∀ { α } → Ref 0 [] α → ⊥
  ref-contra (arr r i) = ref-contra r

  refs-lemma : ∀ { n Γ α } (r : Ref n Γ α) → 0 < n
  refs-lemma zero = s≤s z≤n
  refs-lemma (suc r) = s≤s z≤n
  refs-lemma (arr r x) = refs-lemma r

  compare-type : ∀ (α β : c_type) → Dec (α ≡ β)
  compare-type Int Int = yes refl
  compare-type Int Bool = no (λ ())
  compare-type Int (Array β n) = no (λ ())
  compare-type Bool Int = no (λ ())
  compare-type Bool Bool = yes refl
  compare-type Bool (Array β n) = no (λ ())
  compare-type (Array α n) Int = no (λ ())
  compare-type (Array α n) Bool = no (λ ())
  compare-type (Array α n) (Array β m)
    with compare-type α β | n ≟ m
  ... | yes refl | yes refl = yes refl
  ... | yes refl | no ¬p    = no λ { refl → ¬p refl }
  ... | no ¬p    | _        = no λ { refl → ¬p refl }

  tshift' : ∀ { α n m Γ₁ Γ₂ } → (i : ℕ) → Ctx n Γ₁ → Ctx (suc m) (α ∷ Γ₂) → i < n → Ref n Γ₁ α
  tshift' 0 (wrap (h₁ ∷ t₁)) (wrap (α ∷ _)) _
    with compare-type h₁ α
  ... | yes refl = zero
  ... | no _ = {!!}
  tshift' (suc n) (wrap (h ∷ t)) Γ₂ (s≤s n≤m) = suc (tshift' n (wrap t) Γ₂ n≤m)

  tshift : ∀ { α n m Γ₁ Γ₂ } → Ctx (suc n) Γ₁ → Ctx (suc m) (α ∷ Γ₂) → Ref (suc n) Γ₁ α
  tshift {n = n} {m} Γ₁ Γ₂ = tshift' ((suc n) ∸ (suc m)) Γ₁ Γ₂ (s≤s (n∸m≤n m n))


data Op : c_type → c_type → c_type → Set where
  add sub mul div : Op Int Int Int
  lt lte gt gte eq : Op Int Int Bool
  || && : Op Bool Bool Bool

data Expr where
  op : ∀ { α β γ n Γ } → Op α β γ → Expr n Γ α → Expr n Γ β → Expr n Γ γ
  not : ∀ { n Γ } → Expr n Γ Bool → Expr n Γ Bool
  true false : ∀ { n Γ } → Expr n Γ Bool
  int : ∀ { n Γ } → ℤ → Expr n Γ Int
  var : ∀ { α n Γ } → Ref n Γ α → Expr n Γ α

data Statement : ∀ n → Vec c_type n → Set where
  if : ∀ { n Γ } → Expr n Γ Bool → Statement n Γ → Statement n Γ → Statement n Γ
  assign : ∀ { α n Γ } → Ref n Γ α → Expr n Γ α → Statement n Γ
  seq : ∀ { n Γ } → Statement n Γ → Statement n Γ → Statement n Γ
  decl : ∀ { n Γ } α → Statement (suc n) (α ∷ Γ) → Statement n Γ
  nop : ∀ { n Γ } → Statement n Γ
  for : ∀ { n Γ } → Expr n Γ Int → Expr n Γ Int → Statement (suc n) (Int ∷ Γ) → Statement n Γ
  while : ∀ { n Γ } → Expr n Γ Bool → Statement n Γ → Statement n Γ

abstract
  private
    impl : C
    C.Ref impl α = ∀ n Γ → Maybe (Ref n Γ α)
    C.Expr impl α = ∀ n Γ → Maybe (Expr n Γ α)
    C.Statement impl = ∀ n Γ → Maybe (Statement n Γ)
    C.⟨_⟩ impl x n Γ = just (int x)
    C._+_ impl x y n Γ = x n Γ >>= λ x → y n Γ >>= λ y → just (op add x y)
    C._*_ impl x y n Γ = op mul (x n Γ) (y n Γ)
    C._-_ impl x y n Γ = op sub (x n Γ) (y n Γ)
    C._/_ impl x y n Γ = op div (x n Γ) (y n Γ)
    C._<_ impl x y n Γ = op lt (x n Γ) (y n Γ)
    C._<=_ impl x y n Γ = op lte (x n Γ) (y n Γ)
    C._>_ impl x y n Γ = op gt (x n Γ) (y n Γ)
    C._>=_ impl x y n Γ = op gte (x n Γ) (y n Γ)
    C._==_ impl x y n Γ = op eq (x n Γ) (y n Γ)
    C.true impl n Γ = true
    C.false impl n Γ = false
    C._||_ impl x y n Γ = op || (x n Γ) (y n Γ)
    C._&&_ impl x y n Γ = op && (x n Γ) (y n Γ)
    C.!_ impl x n Γ = not (x n Γ)
    C.if_then_else_ impl cond s₁ s₂ n Γ = if (cond n Γ) (s₁ n Γ) (s₂ n Γ)
    C._[_] impl x i n Γ = index (x n Γ) (i n Γ)
    C.★_ impl x n Γ = var (x n Γ)
    C._≔_ impl x y n Γ = assign (x n Γ) (y n Γ)
    C._；_ impl s₁ s₂ n Γ = seq (s₁ n Γ) (s₂ n Γ)
    C.decl impl α f n Γ₁ = decl α (f v (suc n) (α ∷ Γ₁))
      where
        v : C.Ref impl α
        v 0 _ = {!!}
        v (suc m) Γ₂ = tshift (wrap Γ₂) (wrap (α ∷ Γ₁))
    C.nop impl n Γ = nop
    C.for_to_then_ impl l u f n Γ₁ = for (l n Γ₁) (u n Γ₁) (f v (suc n) (Int ∷ Γ₁))
      where
        v : C.Ref impl Int
        v (suc m) Γ₂ = tshift (wrap Γ₂) (wrap (Int ∷ Γ₁))
    C.while_then_ impl e s n Γ = while (e n Γ) (s n Γ)

data Env { impl : C } : ∀ n → Vec c_type n → Set where
  empty : Env 0 []
  extend : ∀ { n Γ α } → Env {impl} n Γ → C.Ref impl α → Env (suc n) (α ∷ Γ)

pattern ↶⁰ = zero
pattern ↶¹ = suc ↶⁰
pattern ↶² = suc ↶¹
pattern ↶³ = suc ↶²
pattern ↶⁴ = suc ↶³
pattern ↶⁵ = suc ↶⁴
pattern ↶⁶ = suc ↶⁵
pattern ↶⁷ = suc ↶⁶
pattern ↶⁸ = suc ↶⁷
pattern ↶⁹ = suc ↶⁸

Expr* : ∀ n → Vec c_type n → c_type → Set₁
Expr* n Γ α = ∀ impl → Env {impl} n Γ → C.Expr impl α

toExpr* : ∀ { n Γ α } → Expr n Γ α → Expr* n Γ α

lookupT : ∀ { impl n Γ α } → Env {impl} n Γ → Ref n Γ α → C.Ref impl α
lookupT E r = {!!}
-- lookupT (extend _ v) zero = v
-- lookupT (extend env _) (suc r) = lookupT env r
-- lookupT {impl} E (index r i) = C._[_] impl (lookupT E r) (toExpr* i impl E)

op₂ : ∀ { α β γ n Γ } → (∀ impl → C.Expr impl α → C.Expr impl β → C.Expr impl γ) → Expr n Γ α → Expr n Γ β → Expr* n Γ γ
op₂ _∙_ x y impl env = _∙_ impl (toExpr* x impl env) (toExpr* y impl env)
toExpr* (op add x y) = op₂ C._+_ x y
toExpr* (op sub x y) = op₂ C._-_ x y
toExpr* (op mul x y) = op₂ C._*_ x y
toExpr* (op div x y) = op₂ C._/_ x y
toExpr* (op lt x y) = op₂ C._<_ x y
toExpr* (op lte x y) = op₂ C._<=_ x y
toExpr* (op gt x y) = op₂ C._>_ x y
toExpr* (op gte x y) = op₂ C._>=_ x y
toExpr* (op eq x y) = op₂ C._==_ x y
toExpr* (op || x y) = op₂ C._||_ x y
toExpr* (op && x y) = op₂ C._&&_ x y
toExpr* (not x) impl env = C.!_ impl (toExpr* x impl env)
toExpr* true impl env = C.true impl
toExpr* false impl env = C.false impl
toExpr* (int n) impl env = C.⟨_⟩ impl n
toExpr* (var x) impl env = C.★_ impl (lookupT env x)

Statement* : ∀ n → Vec c_type n → Set₁
Statement* n Γ = ∀ impl → Env {impl} n Γ → C.Statement impl

toStatement* : ∀ { n Γ } → Statement n Γ → Statement* n Γ
toStatement* (if cond x y) impl env =
  C.if_then_else_ impl
    (toExpr* cond impl env)
    (toStatement* x impl env)
    (toStatement* y impl env)
toStatement* (assign x y) impl env =
  C._≔_ impl (lookupT env x) (toExpr* y impl env)
toStatement* (seq x y) impl env =
  C._；_ impl (toStatement* x impl env) (toStatement* y impl env)
toStatement* (decl α f) impl env =
  C.decl impl α (λ x → toStatement* f impl (extend env x))

convert-to : (∀ ⦃ impl ⦄ → C.Statement impl) → C.Statement impl
convert-to s = s ⦃ impl ⦄

convert-from : Statement 0 [] → (∀ ⦃ impl ⦄ → C.Statement impl)
convert-from s ⦃ impl ⦄ = toStatement* s impl empty

open C.C ⦃ ... ⦄

bad : C.Expr impl Int
bad = (λ (y : C.Ref impl Int) → C.★_ impl y) v
  where
    v : C.Ref impl Int
    v = {!IRef.suc IRef.zero!}

_ : {!!}
_ = {!bad!}
