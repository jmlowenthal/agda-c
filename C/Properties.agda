-- Based in-part on "A formally verified compiler back-end" by Xavier Leroy

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
open import Data.Bool as 𝔹 using () renaming (Bool to 𝔹)
open import Relation.Binary.PropositionalEquality
open import Data.Vec

open C.Base.C ⦃ ... ⦄

⟦_⟧ : c_type → Set
⟦ Int ⟧ = ℤ
⟦ Bool ⟧ = 𝔹
⟦ Array α n ⟧ = Vec ⟦ α ⟧ n

data Value : ∀ ⦃ _ : C ⦄ → (α : c_type) → ⟦ α ⟧ → Set where
  val : ∀ ⦃ _ : C ⦄ → ∀ { α } → (v : ⟦ α ⟧) → Value α v

data Env ⦃ _ : C ⦄ : Set where
  _↦_,_ : ∀ { α } → ∀ { v : ⟦ α ⟧ } → Ref α → Value α v → Env → Env
  _,_ : ∀ { α } → Ref α → Env → Env
  ε : Env

_↦_∈_ : ∀ ⦃ _ : C ⦄ → ∀ { α } → ∀ { v : ⟦ α ⟧ } → Ref α → Value α v → Env → Set

_∈_ : ∀ ⦃ _ : C ⦄ → ∀ { α } → Ref α → Env → Set

data Continuation ⦃ _ : C ⦄ : Set where
  stop : Continuation
  _then_ : Statement → Continuation → Continuation

data State ⦃ _ : C ⦄ : Set where
  𝒮 : Statement → Continuation → Env → State

data _⊢_⇒_ ⦃ _ : C ⦄ : ∀ { α } → ∀ { v : ⟦ α ⟧ } → Env → Expr α → Value α v → Set where
  deref : ∀ { E α } → ∀ { x : Ref α } → ∀ { e : ⟦ α ⟧ } → ∀ { v : Value α e }
    → (x ↦ v ∈ E) → (E ⊢ (★ x) ⇒ v)
  +-eval : ∀ { E x y x' y' }
    → E ⊢ x ⇒ val x' → E ⊢ y ⇒ val y'
    → E ⊢ x + y ⇒ val (x' ℤ.+ y')
  *-eval : ∀ { E x y x' y' }
    → E ⊢ x ⇒ val x' → E ⊢ y ⇒ val y'
    → E ⊢ x * y ⇒ val (x' ℤ.* y')
  ∸-eval : ∀ { E x y x' y' }
    → E ⊢ x ⇒ val x' → E ⊢ y ⇒ val y'
    → E ⊢ x - y ⇒ val (x' ℤ.- y')
  -- /-eval : ∀ { E x y x' y' }
  --   → E ⊢ x ⇒ v-int x' → E ⊢ y ⇒ v-int y'
  --   → E ⊢ x / y ⇒ v-int (x' ℤ./ y')
  ||-eval : ∀ { E x y x' y' }
    → E ⊢ x ⇒ val x' → E ⊢ y ⇒ val y' → E ⊢ x || y ⇒ val (x' 𝔹.∨ y')
  &&-eval : ∀ { E x y x' y' }
    → E ⊢ x ⇒ val x' → E ⊢ y ⇒ val y' → E ⊢ x && y ⇒ val (x' 𝔹.∧ y')

data _↝_ ⦃ _ : C ⦄ : State → State → Set where
  ↝-if-true : ∀ { E : Env } → ∀ { k : Continuation }
    → ∀ { cond : Expr Bool } → ∀ { s₁ s₂ : Statement }
    → E ⊢ cond ⇒ val 𝔹.true → 𝒮 (if cond then s₁ else s₂) k E ↝ 𝒮 s₁ k E
  ↝-if-false : ∀ { E : Env } → ∀ { k : Continuation }
    → ∀ { cond : Expr Bool } → ∀ { s₁ s₂ : Statement }
    → E ⊢ cond ⇒ val 𝔹.false → 𝒮 (if cond then s₁ else s₂) k E ↝ 𝒮 s₂ k E
  ↝-assignment : ∀ { E : Env } → ∀ { k : Continuation }
    → ∀ { α } → ∀ { id : Ref α } → ∀ { e : Expr α } → ∀ { e' : ⟦ α ⟧ } → ∀ { v : Value α e' }
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
    → 𝒮 (for l to u then f) k E
      ↝ 𝒮 (if (l < u) then (
              (decl Int λ i → i ≔ l ； f i) ；
              for (l + ⟨ + 1 ⟩) to u then f)
           else nop) k E
  ↝-while : ∀ { E : Env } → ∀ { k : Continuation }
    → ∀ { e : Expr Bool } → ∀ { s : Statement }
    → 𝒮 (while e then s) k E ↝ 𝒮 (if e then (s ； while e then s) else nop) k E

infix 0 _≅ₑ_
_≅ₑ_ : ∀ ⦃ _ : C ⦄ → ∀ { α } → Rel (Expr α) 0ℓ
_≅ₑ_ { α } x y = ∀ { E : Env } → ∀ { v w : ⟦ α ⟧ }
  → (E ⊢ x ⇒ val v) × (E ⊢ y ⇒ val w) × (v ≡ w)

≅-over-⊢ : ∀ ⦃ _ : C ⦄
  → ∀ { E : Env } → ∀ { α } → ∀ { x : Expr α } → ∀ { v w : ⟦ α ⟧ }
  → E ⊢ x ⇒ val v → v ≡ w → E ⊢ x ⇒ val w
≅-over-⊢ (deref x↦v) refl = deref x↦v
≅-over-⊢ (+-eval x⇒x' y⇒y') refl = +-eval x⇒x' y⇒y'
≅-over-⊢ (*-eval x⇒x' y⇒y') refl = *-eval x⇒x' y⇒y'
≅-over-⊢ (∸-eval x⇒x' y⇒y') refl = ∸-eval x⇒x' y⇒y'
≅-over-⊢ (||-eval x⇒x' y⇒y') refl = ||-eval x⇒x' y⇒y'
≅-over-⊢ (&&-eval x⇒x' y⇒y') refl = &&-eval x⇒x' y⇒y'

≅ₑ-refl : ∀ ⦃ _ : C ⦄ → ∀ { α } → Reflexive (_≅ₑ_ { α })
≅ₑ-refl = {!!}

≅ₑ-symmetric : ∀ ⦃ _ : C ⦄ → ∀ { α } → Symmetric (_≅ₑ_ { α })
≅ₑ-symmetric i≅j =
  let i⇒v , j⇒w , v≡w = i≅j in
    ≅-over-⊢ j⇒w (sym v≡w) , ≅-over-⊢ i⇒v v≡w , v≡w

≅ₑ-transitive : ∀ ⦃ _ : C ⦄ → ∀ { α } → Transitive (_≅ₑ_ { α })
≅ₑ-transitive i≅j j≅k =
  let i⇒a , j⇒b , a≡b = i≅j in
  let j⇒b , k⇒c , b≡c = j≅k in
    i⇒a , ≅-over-⊢ k⇒c b≡c , a≡b

≅ₑ-isEquivalence : ∀ ⦃ _ : C ⦄ → ∀ { α } → IsEquivalence (_≅ₑ_ { α })
≅ₑ-isEquivalence = record { refl = ≅ₑ-refl ; sym = ≅ₑ-symmetric ; trans = ≅ₑ-transitive }

+-left-id : ∀ ⦃ _ : C ⦄ → LeftIdentity _≅ₑ_ (⟨ + 0 ⟩) _+_
+-left-id = {!!}

+-right-id : ∀ ⦃ _ : C ⦄ → RightIdentity _≅ₑ_ (⟨ + 0 ⟩) _+_
+-right-id x {E} {e} {v} = {!!}

+-id : ∀ ⦃ _ : C ⦄ → Identity _≅ₑ_ (⟨ + 0 ⟩) _+_
+-id = +-left-id , +-right-id

+-assoc : ∀ ⦃ _ : C ⦄ → Associative _≅ₑ_ _+_
+-assoc x y z = {!!}

+-commute : ∀ ⦃ _ : C ⦄ → Commutative _≅ₑ_ _+_
*-id : ∀ ⦃ _ : C ⦄ → Identity _≅ₑ_ (⟨ + 1 ⟩) _*_
*-zero : ∀ ⦃ _ : C ⦄ → Zero _≅ₑ_ (⟨ + 0 ⟩) _*_
*-assoc : ∀ ⦃ _ : C ⦄ → Associative _≅ₑ_ _*_
*-commute : ∀ ⦃ _ : C ⦄ → Commutative _≅ₑ_ _*_
∸-id : ∀ ⦃ _ : C ⦄ → Identity _≅ₑ_ (⟨ + 0 ⟩) _-_
/-id : ∀ ⦃ _ : C ⦄ → Identity _≅ₑ_ (⟨ + 1 ⟩) _/_
-- TODO: algebra properties of _<_ _<=_ _>_ _>=_ _==_ using standard library algebra
<-trans : ∀ ⦃ _ : C ⦄ → ∀ { x y z : Expr Int } → x < y ≅ₑ true → y < z ≅ₑ true → x < z ≅ₑ true
||-id : ∀ ⦃ _ : C ⦄ → Identity _≅ₑ_ false _||_
||-zero : ∀ ⦃ _ : C ⦄ → Zero _≅ₑ_ true _||_
||-assoc : ∀ ⦃ _ : C ⦄ → Associative _≅ₑ_ _||_
||-commute : ∀ ⦃ _ : C ⦄ → Commutative _≅ₑ_ _||_
&&-id : ∀ ⦃ _ : C ⦄ → Identity _≅ₑ_ true _&&_
&&-zero : ∀ ⦃ _ : C ⦄ → Zero _≅ₑ_ false _&&_
&&-assoc : ∀ ⦃ _ : C ⦄ → Associative _≅ₑ_ _&&_
&&-commute : ∀ ⦃ _ : C ⦄ → Commutative _≅ₑ_ _&&_

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
