open import CMinor.Lang.Lang
open import Level using (Level ; _⊔_)
open import Data.Nat.Binary as ℕᵇ using (ℕᵇ ; 0ᵇ ; 1ᵇ)
open import Data.Nat as ℕ using (ℕ)
open import Data.Float as 𝔽 using () renaming (Float to 𝔽)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)

import Data.Nat.DivMod as ℕ÷

module CMinor.Semantics.NaturalExpressionSemantics where

_mod2^32 : ℕᵇ → ℕᵇ
_mod2^32 n = ℕᵇ.fromℕ ((ℕᵇ.toℕ n) ℕ÷.% (2 ℕ.^ 32))

record NaturalExpressionSemantics (l₁ l₂ l₃ l₄ l₅ l₆ l₇ g s e m j₁ j₂ j₃ t : Level) (ℒ : Lang l₁ l₂ l₃ l₄ l₅ l₆ l₇) : Set (Level.suc (l₁ ⊔ l₂ ⊔ l₃ ⊔ l₄ ⊔ g ⊔ s ⊔ e ⊔ m ⊔ j₁ ⊔ j₂ ⊔ j₃ ⊔ t)) where

  open Lang ℒ

  field
    Value : Type → Set
    GlobalEnvironment : Set g
    Stack : Set s
    Environment : Set e
    MemoryState : Set m

    _,_,_,_⊢_⇒_ : ∀ {α} → GlobalEnvironment → Stack → Environment → MemoryState → Expr α → Value α → Set j₁    
    _↦_∈_ : ∀ {α} → Variable α → Value α → Environment  → Set j₂
    _↦_∈_,_ : ∀ {α} → ℕᵇ → Value α → MemoryState → Stack → Set j₃

    eval-constant : ∀ {α} → GlobalEnvironment → Stack → Constant α → Value α
    eval-unop : ∀ {α β} → (Expr α → Expr β) → Value α → Value β
    eval-binop : ∀ {α β γ} → (Expr α → Expr β → Expr γ) → Value α → Value β → Value γ
  
    ⌊int_⌋ : ℕᵇ → Value Int -- binary representation of n
    ⌊float_⌋ : 𝔽 → Value Float
    -- symbol : {!!} → {!!} → Value {!!}
    ⌊ptr_,_⌋ : Stack → ℕᵇ → Value Int

    istrue : Value Int → Set t
    isfalse : Value Int → Set t

    istrue-ptr : ∀ b δ → istrue (⌊ptr b , δ ⌋)
    istrue-int-true : ∀ n → n ≡ 0ᵇ → istrue (⌊int n ⌋)
    istrue-int-false : ∀ n → ¬ (n ≡ 0ᵇ) → ¬ istrue (⌊int n ⌋)

    isfalse-true : ∀ v → ¬ istrue v → isfalse v
    isfalse-false : ∀ v → istrue v → ¬ isfalse v

    ⊢-id : ∀ G σ E M {α x} {v : Value α} →
      x ↦ v ∈ E →
      ----------------------------------------
      G , σ , E , M ⊢ id x ⇒ v
    ⊢-cst : ∀ G σ E M {α} x v →
      eval-constant {α} G σ x ≡ v →
      -----------------------------
      G , σ , E , M ⊢ cst x ⇒ v
    ⊢-unop : ∀ G σ E M {α β} a₁ v₁ v (op : Expr α → Expr β) →
      G , σ , E , M ⊢ a₁ ⇒ v₁ →
      eval-unop op v₁ ≡ v →
      --------------------------------
      G , σ , E , M ⊢ op a₁ ⇒ v
    ⊢-binop : ∀ G σ E M {α β γ} a₁ a₂ v₁ v₂ v (op : Expr α → Expr β → Expr γ) →
      G , σ , E , M ⊢ a₁ ⇒ v₁ →
      G , σ , E , M ⊢ a₂ ⇒ v₂ →
      eval-binop op v₁ v₂ ≡ v →
      --------------------------------
      G , σ , E , M ⊢ op a₁ a₂ ⇒ v
    ⊢-mem-read : ∀ G σ E M e b δ τ (v : Value τ) →
      G , σ , E , M ⊢ e ⇒ ⌊ptr b , δ ⌋ →
      δ ↦ v ∈ M , b →
      -----------------------------------
      G , σ , E , M ⊢ mem-read τ e ⇒ v
    ⊢-tenary-true : ∀ G σ E M {α} a₁ a₂ a₃ v₁ (v₂ : Value α) →
      G , σ , E , M ⊢ a₁ ⇒ v₁ →
      istrue v₁ →
      G , σ , E , M ⊢ a₂ ⇒ v₂ →
      -----------------------------------
      G , σ , E , M ⊢ tenary a₁ a₂ a₃ ⇒ v₂
    ⊢-tenary-false : ∀ G σ E M {α} a₁ a₂ a₃ v₁ (v₃ : Value α) →
      G , σ , E , M ⊢ a₁ ⇒ v₁ →
      isfalse v₁ →
      G , σ , E , M ⊢ a₃ ⇒ v₃ →
      -----------------------------------
      G , σ , E , M ⊢ tenary a₁ a₂ a₃ ⇒ v₃

    -- op₁(a₁)
    -- negint notint
    eval-notbool-true : ∀ v → istrue v → eval-unop notbool v ≡ ⌊int 0ᵇ ⌋
    eval-notbool-false : ∀ v → isfalse v → eval-unop notbool v ≡ ⌊int 1ᵇ ⌋
    eval-negf : ∀ v → eval-unop negf ⌊float v ⌋ ≡ ⌊float 𝔽.- v ⌋
    -- absf cast8u cast8s cast16u cast16s
    -- singleoffloat intoffloat intuoffloat floatofint floatofintu

    -- op₂(a₁, a₂)
    eval-add-int-int : ∀ n₁ n₂ →
      eval-binop add ⌊int n₁ ⌋ ⌊int n₂ ⌋ ≡ ⌊int (n₁ ℕᵇ.+ n₂) mod2^32 ⌋
    eval-add-ptr-int : ∀ b δ n →
      eval-binop add ⌊ptr b , δ ⌋ ⌊int n ⌋ ≡ ⌊ptr b , (δ ℕᵇ.+ n) mod2^32 ⌋
    -- sub mul div divu mod modu
    -- and or xor shl shr shru
    eval-addf : ∀ f₁ f₂ →
      eval-binop addf ⌊float f₁ ⌋ ⌊float f₂ ⌋ ≡ ⌊float f₁ 𝔽.+ f₂ ⌋
    -- subf mulf divf
    -- cmp-== cmp-!= cmp-> cmp->= cmp-< cmp-<=
    -- cmpu-== cmpu-!= cmpu-> cmpu->= cmpu-< cmpu-<=
    -- cmpf-== cmpf-!= cmpf-> cmpf->= cmpf-< cmpf-<=

    -- cst
    eval-cst-int : ∀ n G σ → eval-constant G σ (cst-int n) ≡ ⌊int n ⌋
    eval-cst-float : ∀ f G σ → eval-constant G σ (cst-float f) ≡ ⌊float f ⌋
    -- ⊢-addrsymbol : ?
    eval-addrstack : ∀ n G σ → eval-constant G σ (addrstack n) ≡ ⌊ptr σ , n ⌋

  
  
