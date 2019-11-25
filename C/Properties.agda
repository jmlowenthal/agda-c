module C.Properties where

open import C.Base
open import Function
open import Relation.Binary
open import Level using (0ℓ)
open import Data.Product using (_×_ ; _,_)
open import Data.Integer using (+_)
open import Algebra.FunctionProperties
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Sum
open import Data.Integer as ℤ using (ℤ)
open import Relation.Nullary

open C.Base.C ⦃ ... ⦄

data Value : ∀ ⦃ _ : C ⦄ → (α : c_type) → Expr α → Set where
  v-true : ∀ ⦃ _ : C ⦄ → Value Bool true
  v-false : ∀ ⦃ _ : C ⦄ → Value Bool false
  v-int : ∀ ⦃ _ : C ⦄ → (n : ℤ) → Value Int ⟨ n ⟩

data Env ⦃ _ : C ⦄ : Set where
  _↦_,_ : ∀ { α } → ∀ { v : Expr α } → Ref α → Value α v → Env → Env
  _,_ : ∀ { α } → Ref α → Env → Env
  ε : Env

_↦_∈_ : ∀ ⦃ _ : C ⦄ → ∀ { α } → ∀ { v : Expr α } → Ref α → Value α v → Env → Set
x ↦ v ∈ (y ↦ w , E) = ({!x ≡ y!} × {!v ≡ w!}) ⊎ (x ↦ v ∈ E)
x ↦ v ∈ (_ , E) = x ↦ v ∈ E
_ ↦ _ ∈ ε = ⊥

_∈_ : ∀ ⦃ _ : C ⦄ → ∀ { α } → Ref α → Env → Set
x ∈ (y ↦ v , E) = {!(x ≡ y)!} ⊎ (x ∈ E)
x ∈ (y , E) = {!x ≡ y!} ⊎ (x ∈ E)
x ∈ ε = ⊥

data Continuation ⦃ _ : C ⦄ : Set where
  stop : Continuation
  _then_ : Statement → Continuation → Continuation

data State ⦃ _ : C ⦄ : Set where
  𝒮 : Statement → Continuation → Env → State

-- Based on "A formally verified compiler back-end" by Xavier Leroy
record Semantics ⦃ _ : C ⦄ : Set₁ where
  field
    _⊢_⇒_ : ∀ { α } → ∀ { v : Expr α } → Env → Expr α → Value α v → Set
    deref : ∀ { E : Env } → ∀ { α } → ∀ { x : Ref α } → ∀ { e : Expr α } → ∀ { v : Value α e }
      → (x ↦ v ∈ E) → (E ⊢ (★ x) ⇒ v)
    +-eval : ∀ { E : Env } → ∀ { x y : Expr Int } → ∀ { x' y' : ℤ }
      → E ⊢ x ⇒ v-int x' → E ⊢ y ⇒ v-int y'
      → E ⊢ x + y ⇒ v-int (x' ℤ.+ y')
    *-eval : ∀ { E : Env } → ∀ { x y : Expr Int } → ∀ { x' y' : ℤ }
      → E ⊢ x ⇒ v-int x' → E ⊢ y ⇒ v-int y'
      → E ⊢ x * y ⇒ v-int (x' ℤ.* y')
    ∸-eval : ∀ { E : Env } → ∀ { x y : Expr Int } → ∀ { x' y' : ℤ }
      → E ⊢ x ⇒ v-int x' → E ⊢ y ⇒ v-int y'
      → E ⊢ x - y ⇒ v-int (x' ℤ.- y')
    -- /-eval : ∀ { E : Env } → ∀ { x y : Expr Int } → ∀ { x' y' : ℤ }
    --   → E ⊢ x ⇒ v-int x' → E ⊢ y ⇒ v-int y'
    --   → E ⊢ x / y ⇒ v-int (x' ℤ./ y')
    ||-eval : ∀ { E : Env } → ∀ { x y : Expr Bool } → ∀ { x' y' }
      → E ⊢ x ⇒ x' → E ⊢ y ⇒ y' → E ⊢ x || y ⇒ {!!}

    _↝_ : State → State → Set
    ↝-if-true : ∀ { E : Env } → ∀ { k : Continuation }
      → ∀ { cond : Expr Bool } → ∀ { s₁ s₂ : Statement }
      → E ⊢ cond ⇒ v-true → 𝒮 (if cond then s₁ else s₂) k E ↝ 𝒮 s₁ k E
    ↝-if-false : ∀ { E : Env } → ∀ { k : Continuation }
      → ∀ { cond : Expr Bool } → ∀ { s₁ s₂ : Statement }
      → E ⊢ cond ⇒ v-false → 𝒮 (if cond then s₁ else s₂) k E ↝ 𝒮 s₂ k E
    ↝-assignment : ∀ { E : Env } → ∀ { k : Continuation }
      → ∀ { α } → ∀ { id : Ref α } → ∀ { e : Expr α } → ∀ { e' : Expr α } → ∀ { v : Value α e' }
      → E ⊢ e ⇒ v → 𝒮 (id ≔ e) k E ↝ 𝒮 nop k (id ↦ v , E)
    ↝-seq : ∀ { E : Env } → ∀ { k : Continuation }
      → ∀ { s₁ s₂ : Statement } → 𝒮 (s₁ ； s₂) k E ↝ 𝒮 s₁ (s₂ then k) E
    ↝-decl : ∀ { E : Env } → ∀ { k : Continuation }
      → ∀ { α } → ∀ { f : Ref α → Statement }
      → ∀ { x : Ref α } → ∀ { _ : ¬ (x ∈ E) }
      → 𝒮 (decl α f) k E ↝ 𝒮 (f x) k (x , E) 
    ↝-nop : ∀ { E : Env } → ∀ { k : Continuation } → ∀ { s : Statement }
      → 𝒮 nop (s then k) E ↝ 𝒮 s k E
    ↝-for : ∀ { E : Env } → ∀ { k : Continuation }
      → ∀ { l u : Expr Int } → ∀ { f : Ref Int → Statement }
      → 𝒮 (for l to u then f) k E ↝ 𝒮 (if (l < u) then ((decl Int λ i → i ≔ l ； f i) ； for (l + ⟨ + 1 ⟩) to u then f) else nop) k E
    ↝-while : ∀ { E : Env } → ∀ { k : Continuation }
      → ∀ { e : Expr Bool } → ∀ { s : Statement }
      → 𝒮 (while e then s) k E ↝ 𝒮 (if e then (s ； while e then s) else nop) k E

open Semantics ⦃ ... ⦄

infix 0 _≡ₑ_
infix 0 _≡ₛ_
_≡ₑ_ : ∀ ⦃ _ : C ⦄ → ∀ ⦃ _ : Semantics ⦄ → ∀ { α } → Rel (Expr α) 0ℓ
_≡ₑ_ { α } x y = ∀ { E : Env } → ∀ { e : Expr α } → ∀ { v : Value α e } → E ⊢ x ⇒ v → E ⊢ y ⇒ v 

≡ₑ-symmetric : ∀ ⦃ _ : C ⦄ → ∀ ⦃ _ : Semantics ⦄ → ∀ { α } → Symmetric (_≡ₑ_ { α })
≡ₑ-symmetric i≡j E⊢j⇒v = {!!}

≡ₑ-transitive : ∀ ⦃ _ : C ⦄ → ∀ ⦃ _ : Semantics ⦄ → ∀ { α } → Transitive (_≡ₑ_ { α })
≡ₑ-transitive i≡j j≡k E⊢i⇒v = {!!}

≡ₑ-isEquivalence : ∀ ⦃ _ : C ⦄ → ∀ ⦃ _ : Semantics ⦄ → ∀ { α } → IsEquivalence (_≡ₑ_ { α })
≡ₑ-isEquivalence = record { refl = id ; sym = ≡ₑ-symmetric ; trans = ≡ₑ-transitive }

+-id : ∀ ⦃ _ : C ⦄ → ∀ ⦃ _ : Semantics ⦄ → Identity _≡ₑ_ (⟨ + 0 ⟩) _+_
+-assoc : ∀ ⦃ _ : C ⦄ → ∀ ⦃ _ : Semantics ⦄ → Associative _≡ₑ_ _+_
+-commute : ∀ ⦃ _ : C ⦄ → ∀ ⦃ _ : Semantics ⦄ → Commutative _≡ₑ_ _+_
*-id : ∀ ⦃ _ : C ⦄ → ∀ ⦃ _ : Semantics ⦄ → Identity _≡ₑ_ (⟨ + 1 ⟩) _*_
*-zero : ∀ ⦃ _ : C ⦄ → ∀ ⦃ _ : Semantics ⦄ → Zero _≡ₑ_ (⟨ + 0 ⟩) _*_
*-assoc : ∀ ⦃ _ : C ⦄ → ∀ ⦃ _ : Semantics ⦄ → Associative _≡ₑ_ _*_
*-commute : ∀ ⦃ _ : C ⦄ → ∀ ⦃ _ : Semantics ⦄ → Commutative _≡ₑ_ _*_
∸-id : ∀ ⦃ _ : C ⦄ → ∀ ⦃ _ : Semantics ⦄ → Identity _≡ₑ_ (⟨ + 0 ⟩) _-_
/-id : ∀ ⦃ _ : C ⦄ → ∀ ⦃ _ : Semantics ⦄ → Identity _≡ₑ_ (⟨ + 1 ⟩) _/_
-- TODO: algebra properties of _<_ _<=_ _>_ _>=_ _==_ using standard library algebra
<-trans : ∀ ⦃ _ : C ⦄ → ∀ ⦃ _ : Semantics ⦄ → ∀ { x y z : Expr Int } → x < y ≡ₑ true → y < z ≡ₑ true → x < z ≡ₑ true
||-id : ∀ ⦃ _ : C ⦄ → ∀ ⦃ _ : Semantics ⦄ → Identity _≡ₑ_ false _||_
||-zero : ∀ ⦃ _ : C ⦄ → ∀ ⦃ _ : Semantics ⦄ → Zero _≡ₑ_ true _||_
||-assoc : ∀ ⦃ _ : C ⦄ → ∀ ⦃ _ : Semantics ⦄ → Associative _≡ₑ_ _||_
||-commute : ∀ ⦃ _ : C ⦄ → ∀ ⦃ _ : Semantics ⦄ → Commutative _≡ₑ_ _||_
&&-id : ∀ ⦃ _ : C ⦄ → ∀ ⦃ _ : Semantics ⦄ → Identity _≡ₑ_ true _&&_
&&-zero : ∀ ⦃ _ : C ⦄ → ∀ ⦃ _ : Semantics ⦄ → Zero _≡ₑ_ false _&&_
&&-assoc : ∀ ⦃ _ : C ⦄ → ∀ ⦃ _ : Semantics ⦄ → Associative _≡ₑ_ _&&_
&&-commute : ∀ ⦃ _ : C ⦄ → ∀ ⦃ _ : Semantics ⦄ → Commutative _≡ₑ_ _&&_

-- _≡ₛ_ : Rel Statement 0ℓ
    

--open Equivalence ⦃ ... ⦄

-- β-if-true : ∀ ⦃ _ : C ⦄ → ∀ ⦃ _ : Equivalence ⦄ → ∀ { x y : Statement }
--   → if true then x else y ≡ₛ x
-- β-if-true = {!!}

-- β-if-false : ∀ ⦃ _ : C ⦄ → ⦃ _ : Equivalence ⦄ → ∀ { x y : Statement }
--   → if false then x else y ≡ y
-- β-if-false = {!!}

-- η-if : ∀ ⦃ _ : C ⦄ → ⦃ _ : Equivalence ⦄ → ∀ { cond : Expr Bool } → ∀ { e : Statement }
--   → if cond then e else e ≡ e
-- η-if = {!!}

-- β-while : ∀ ⦃ _ : C ⦄ → ⦃ _ : Equivalence ⦄ → ∀ { e₁ : Expr Bool } → ∀ { e₂ : Statement }
--   → while e₁ then e₂ ≡ if e₁ then (e₂ ； while e₁ then e₂) else nop
