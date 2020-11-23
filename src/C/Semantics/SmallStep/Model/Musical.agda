{-# OPTIONS --safe --exact-split --without-K --sized-types #-}

open import C.Lang
open import C.Semantics.SmallStep.Model.State

open import Size
open import Codata.Colist as Colist hiding (_++_ ; [_] ; fromList)
open import Codata.Delay
open import Codata.Thunk
open import Data.Empty
open import Data.Unit hiding (setoid)
open import Data.List hiding (_++_ ; [_])
open import Data.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_] ; setoid)
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Function

import Level
import Data.Integer as ℤ
import Data.Integer.DivMod as ℤ÷
import Data.Nat as ℕ
import Data.Bool as 𝔹

open Lang ⦃ ... ⦄

module C.Semantics.SmallStep.Model.Musical ⦃ _ : Lang ⦄ where

-- Based on:
-- Coinductive Verification of Program Optimizations Using Similarity Relations by Glesner et al.
-- Undecidability of Equality for Codata Types by Berger and Setzer

data Effect : Set where
  emit : ⟦ Int ⟧ → Effect
  terminated : Effect

data Internal : Set where
  τ : Internal
  _↦_ : ∀ { α } → Ref α → ⟦ α ⟧ → Internal

infix 10 _↓
infix 10 _↗
data Label : Set where
  _↓ : Internal → Label
  _↗ : Effect → Label

data Reduction (_~[_]↝_ : State → Label → State → Set) : (A : State) → Size → Set where
  []   : {i : Size}                                                    → Reduction _~[_]↝_ Ω i
  _↓∷_ : ∀ { A B α i } → A ~[ α ↓ ]↝ B →        Reduction _~[_]↝_ B  i → Reduction _~[_]↝_ A i
  _↗∷_ : ∀ { A B α i } → A ~[ α ↗ ]↝ B → Thunk (Reduction _~[_]↝_ B) i → Reduction _~[_]↝_ A i

Productive : ∀ { R A i } → Reduction R A i → Set
Productive []        = ⊥
Productive (_ ↓∷ xs) = Productive xs
Productive (_ ↗∷ _)  = ⊤

Effects : Size → Set
Effects = Colist Effect

data Labels (i : Size) : Set where
  []   :                             Labels i
  _↗∷_ : Effect   → Thunk Labels i → Labels i
  _↓∷_ : Internal →       Labels i → Labels i

Next : Label → (Size → Set) → Size → Set
Next (x ↓) C i = C i
Next (x ↗) C i = Thunk C i

next : ∀ { i } (e : Label) → Labels ∞ → Next e Labels i
next (_ ↓) = id
next (_ ↗) es = λ where .force → es

-- Positivity checker prevents inlining into Labels
_↝∷_ : ∀ { i } (e : Label) → Next e Labels i → Labels i
_↝∷_ (x ↓) = x ↓∷_
_↝∷_ (x ↗) = x ↗∷_

fromList : ∀ { i } → List Label → Labels i
fromList [] = []
fromList (x ↓ ∷ xs) = x ↓∷ fromList xs
fromList (x ↗ ∷ xs) = x ↗∷ λ where .force → fromList xs

data Finite : Labels ∞ → Set where
  []   : Finite []
  _↗∷_ : ∀ x {xs} (fin : Finite (force xs)) → Finite (x ↗∷ xs)
  _↓∷_ : ∀ x {xs} (fin : Finite xs)         → Finite (x ↓∷ xs)

_++_ : ∀ {i} → Labels ∞ → Labels ∞ → Labels i
[] ++ ys = ys
(x ↗∷ xs) ++ ys = x ↗∷ λ where .force → force xs ++ ys
(x ↓∷ xs) ++ ys = x ↓∷ (xs ++ ys)

τs : ∀ {i} → ℕ.ℕ → Labels i
τs ℕ.zero = []
τs (ℕ.suc n) = τ ↓∷ τs n

labels-of : ∀ { R A i } → Reduction R A i → Labels i
labels-of [] = []
labels-of (_↓∷_ {α = α} _ xs) = α ↓∷ labels-of xs
labels-of (_↗∷_ {α = α} _ xs) = α ↗∷ λ where .force → labels-of (force xs)

-- bisimilarity
infix 0 [_]_≈_
data [_]_≈_ (i : Size) : Labels ∞ → Labels ∞ → Set where
  [] : [ i ] [] ≈ []
  _↗∷_ : ∀ x { xs ys } → Thunk ([_] force xs ≈ force ys) i → [ i ] (x ↗∷ xs) ≈ (x ↗∷ ys)
  _↓∷_ : ∀ x { xs ys } →      [ i ]       xs ≈ ys          → [ i ] (x ↓∷ xs) ≈ (x ↓∷ ys)

infix 0 _≈_
_≈_ = [ ∞ ]_≈_

setoid : ∀ {ℓ} → Set ℓ → Setoid _ _
setoid A = record
  { Carrier       = Labels ∞
  ; _≈_           = _≈_
  ; isEquivalence = record
    { refl  = ≈-refl
    ; sym   = ≈-sym
    ; trans = ≈-trans
    }
  }
  where
  ≈-refl : ∀ { i } → Reflexive [ i ]_≈_
  ≈-refl {_} {[]}      = []
  ≈-refl {_} {x ↗∷ xs} = x ↗∷ λ where .force → ≈-refl
  ≈-refl {_} {x ↓∷ xs} = x ↓∷ ≈-refl

  ≈-sym : ∀ { i } → Symmetric [ i ]_≈_
  ≈-sym []         = []
  ≈-sym (x ↗∷ xs≈) = x ↗∷ λ where .force → ≈-sym (force xs≈)
  ≈-sym (x ↓∷ xs≈) = x ↓∷ ≈-sym xs≈

  ≈-trans : ∀ { i } → Transitive [ i ]_≈_
  ≈-trans []         []          = []
  ≈-trans (x ↗∷ xs≈) (.x ↗∷ ys≈) = x ↗∷ λ where .force → ≈-trans (force xs≈) (force ys≈)
  ≈-trans (x ↓∷ xs≈) (.x ↓∷ ys≈) = x ↓∷ ≈-trans xs≈ ys≈

-- weak bisimilarity
-- see http://www.cse.chalmers.se/~nad/publications/danielsson-up-to-using-sized-types.pdf
infix 0 [_]_[≈]_
data [_]_[≈]_ (i : Size) : Labels ∞ → Labels ∞ → Set where
  []    :                                                       [ i ] []        [≈] []
  _∷_   : ∀ x { xs ys } → Thunk ([_] force xs [≈] force ys) i → [ i ] (x ↗∷ xs) [≈] (x ↗∷ ys)
  left  : ∀ x { xs ys } →      [ i ]       xs [≈] ys          → [ i ] (x ↓∷ xs) [≈] ys
  right : ∀ y { xs ys } →      [ i ]       xs [≈] ys          → [ i ] xs        [≈] (y ↓∷ ys)
-- NOTE: this representation is not canonical -- left and right are commutative

infix 0 _[≈]_
_[≈]_ = [ ∞ ]_[≈]_

[≈]-refl : ∀ {i} → Reflexive [ i ]_[≈]_
[≈]-refl {_} {[]}       = []
[≈]-refl {_} {_ ↗∷ _}  = _ ∷ λ where .force → [≈]-refl
[≈]-refl {_} {x ↓∷ xs} = left x (right x [≈]-refl)

[≈]-reflexive : ∀ { A B i } → A ≈ B → [ i ] A [≈] B
[≈]-reflexive [] = []
[≈]-reflexive (x ↗∷ xs≈) = x ∷ λ where .force → [≈]-reflexive (force xs≈)
[≈]-reflexive (x ↓∷ xs≈) = left x (right x ([≈]-reflexive xs≈))

[≈]-sym : ∀ {i} → Symmetric [ i ]_[≈]_
[≈]-sym [] = []
[≈]-sym (_ ∷ xs) = _ ∷ λ where .force → [≈]-sym (force xs)
[≈]-sym (left p x)  = right p ([≈]-sym x)
[≈]-sym (right p x) = left  p ([≈]-sym x)

[≈]-trans : ∀ { i } → Trans _[≈]_ _[≈]_ ([ i ]_[≈]_)
[≈]-trans []          []          = []
[≈]-trans []          (right i p) = right i ([≈]-trans [] p)
[≈]-trans (x ∷ xs)    (.x ∷ ys)   = _ ∷ λ where .force → [≈]-trans (force xs) (force ys)
[≈]-trans (x ∷ xs)    (right i p) = right i ([≈]-trans (x ∷ xs) p)
[≈]-trans (left i p)  y~z         = left  i ([≈]-trans p y~z)
[≈]-trans (right i p) (right j q) = right j ([≈]-trans (right i p) q)
[≈]-trans (right _ p) (left _ q)  = [≈]-trans p q

[≈]-setoid : Setoid _ _
[≈]-setoid = record
  { Carrier = _
  ; _≈_ = _[≈]_
  ; isEquivalence = record
    { refl = [≈]-refl
    ; sym = [≈]-sym
    ; trans = [≈]-trans
    }
  }

infixr 4 _↗◅_
infixr 4 _↓◅_
data SmallStep* (_~[_]↝_ : State → Label → State → Set) : State → State → Labels ∞ → Size → Set where
  ε    : ∀ { X i }                                                                        → SmallStep* _~[_]↝_ X X []        i
  _↓◅_ : ∀ { X Y Z e es i } → X ~[ e ↓ ]↝ Y →        SmallStep* _~[_]↝_ Y Z es          i → SmallStep* _~[_]↝_ X Z (e ↓∷ es) i
  _↗◅_ : ∀ { X Y Z e es i } → X ~[ e ↗ ]↝ Y → Thunk (SmallStep* _~[_]↝_ Y Z (force es)) i → SmallStep* _~[_]↝_ X Z (e ↗∷ es) i

-- This is generalized transitivity
_◅◅_ : ∀ { R X Y Z e f i } → SmallStep* R X Y e ∞ → SmallStep* R Y Z f ∞ → SmallStep* R X Z (e ++ f) i
ε ◅◅ ε = ε
ε ◅◅ (x ↓◅ xs) = x ↓◅ (ε ◅◅ xs) -- this is a weird laundering of size
ε ◅◅ (x ↗◅ xs) = x ↗◅ xs
(h ↓◅ t) ◅◅ B = h ↓◅ (t ◅◅ B)
(h ↗◅ t) ◅◅ B = h ↗◅ λ where .force → force t ◅◅ B

SmallStep⁺ : ∀ (_~[_]↝_ : State → Label → State → Set) → State → State → Labels ∞ → Size → Set
SmallStep⁺ _~[_]↝_ X Y [] _ = ⊥
SmallStep⁺ _~[_]↝_ X Y (e ↗∷ es) i = ∃[ X' ] (X ~[ e ↗ ]↝ X' × Thunk (SmallStep* _~[_]↝_ X' Y (force es)) i)
SmallStep⁺ _~[_]↝_ X Y (e ↓∷ es) i = ∃[ X' ] (X ~[ e ↓ ]↝ X' × SmallStep* _~[_]↝_ X' Y es i)

record Semantics : Set₁ where
  field
    _⊢_⇒_ : ∀ { α } → Env → Expr α → ⟦ α ⟧ → Set
    _~[_]↝_ : State → Label → State → Set

    ⊢-total : ∀ { α E } { e : Expr α } → ∃[ v ] (E ⊢ e ⇒ v) -- should ensure no free variables
    ⊢-det : ∀ { α E } { e : Expr α } { v w : ⟦ α ⟧ } → E ⊢ e ⇒ v → E ⊢ e ⇒ w → v ≡ w 
    ⊢-weakening : ∀ { E E' α β } { e : Expr α } { v : ⟦ α ⟧ } { x : Ref β } { w : ⟦ β ⟧ }
      → x ∉nv E → x ∉nv E'
      → (E ⊕ E') ⊢ e ⇒ v → (E ⊕ (x Env.↦ w , ε) ⊕ E') ⊢ e ⇒ v
    ⊢-exchange : ∀ { E E' α γ } { x : Ref α } { y : Ref α }
      → { v : ⟦ α ⟧ } { w : ⟦ α ⟧ } { e : Expr γ } { ev : ⟦ γ ⟧ }
      → ¬ (x ≡ y)
      → (E ⊕ (x Env.↦ v , (y Env.↦ w , ε)) ⊕ E') ⊢ e ⇒ ev
      → (E ⊕ (y Env.↦ w , (x Env.↦ v , ε)) ⊕ E') ⊢ e ⇒ ev
    -- TODO: variants on Env constructor (and x ≢ y and α ≢ β)
    nat : ∀ { E } n → E ⊢ ⟪ n ⟫ ⇒ n
    deref : ∀ { E α } { x : Ref α } { v : ⟦ α ⟧ }
      → x ↦ v ∈nv E → (E ⊢ (★ x) ⇒ v)
    +-eval : ∀ { E x y x' y' }
      → E ⊢ x ⇒ x' → E ⊢ y ⇒ y'
      → E ⊢ x + y ⇒ (x' ℤ.+ y')
    *-eval : ∀ { E x y x' y' }
      → E ⊢ x ⇒ x' → E ⊢ y ⇒ y'
      → E ⊢ x * y ⇒ (x' ℤ.* y')
    ∸-eval : ∀ { E x y x' y' }
      → E ⊢ x ⇒ x' → E ⊢ y ⇒ y'
      → E ⊢ x - y ⇒ (x' ℤ.- y')
    /-eval : ∀ { E x y x' y' }
      → E ⊢ x ⇒ x' → E ⊢ y ⇒ y' → (y≠0 : False (ℤ.∣ y' ∣ ℕ.≟ 0))
      → E ⊢ x / y ⇒ ((x' ℤ÷.div y') {y≠0})
    <-eval : ∀ { E x y x' y' }
      → E ⊢ x ⇒ x' → E ⊢ y ⇒ y'
      → E ⊢ x < y ⇒ (⌊ x' ℤ.<? y' ⌋)
    >-eval : ∀ { E x y x' y' }
      → E ⊢ x ⇒ x' → E ⊢ y ⇒ y'
      → E ⊢ x > y ⇒ (⌊ y' ℤ.<? x' ⌋)
    true-eval : ∀ { E } → E ⊢ true ⇒ 𝔹.true
    false-eval : ∀ { E } → E ⊢ false ⇒ 𝔹.false
    ||-eval : ∀ { E x y x' y' }
      → E ⊢ x ⇒ x' → E ⊢ y ⇒ y' → E ⊢ x || y ⇒ (x' 𝔹.∨ y')
    &&-eval : ∀ { E x y x' y' }
      → E ⊢ x ⇒ x' → E ⊢ y ⇒ y' → E ⊢ x && y ⇒ (x' 𝔹.∧ y')
    ⁇-eval-t : ∀ { E c α } { x y : Expr α } { x' }
      → E ⊢ c ⇒ 𝔹.true → E ⊢ x ⇒ x' → E ⊢ c ⁇ x ∷ y ⇒ x'
    ⁇-eval-f : ∀ { E c α } { x y : Expr α } { y' }
      → E ⊢ c ⇒ 𝔹.false → E ⊢ y ⇒ y' → E ⊢ c ⁇ x ∷ y ⇒ y'

    ↝-if-true : ∀ { E k } { cond : Expr Bool } { s₁ s₂ : Statement }
      → E ⊢ cond ⇒ 𝔹.true → 𝒮 (if cond then s₁ else s₂) k E ~[ τ ↓ ]↝ 𝒮 s₁ k E
    ↝-if-false : ∀ { E k } { cond : Expr Bool } { s₁ s₂ : Statement }
      → E ⊢ cond ⇒ 𝔹.false → 𝒮 (if cond then s₁ else s₂) k E ~[ τ ↓ ]↝ 𝒮 s₂ k E
    ↝-assignment : ∀ { E k α } { id : Ref α } { e : Expr α } { v : ⟦ α ⟧ }
      → E ⊢ e ⇒ v → 𝒮 (id ≔ e) k E ~[ id ↦ v ↓ ]↝ 𝒮 nop k (id Env.↦ v , E)
    ↝-seq : ∀ { E k } { s₁ s₂ : Statement }
      → 𝒮 (s₁ ； s₂) k E ~[ τ ↓ ]↝ 𝒮 s₁ (s₂ ∷ k) E
    ↝-decl : ∀ { E k α } { f : Ref α → Statement }
      → ∃ λ (x : Ref α) → (x ∉nv E) × (𝒮 (decl α f) k E ~[ τ ↓ ]↝ 𝒮 (f x) k (x , E))
    ↝-nop : ∀ { E k } { s : Statement } → 𝒮 nop (s ∷ k) E ~[ τ ↓ ]↝ 𝒮 s k E
    ↝-stuck : ∀ { E } → 𝒮 nop [] E ~[ terminated ↗ ]↝ Ω
    ↝-Ω : ∀ { S' e } → ¬ (Ω ~[ e ]↝ S')
    ↝-for : ∀ { E k } { l u : Expr Int } { f : Ref Int → Statement } { x : Ref Int }
      → 𝒮 (for l to u then f) k E
        ~[ τ ↓ ]↝ 𝒮 (if (l < u) then (
                (decl Int λ i → i ≔ l ； f i) ；
                for (l + ⟪ ℤ.+ 1 ⟫) to u then f)
             else nop) k E
    ↝-while : ∀ { E k } { e : Expr Bool } { s : Statement }
      → 𝒮 (while e then s) k E ~[ τ ↓ ]↝ 𝒮 (if e then (s ； while e then s) else nop) k E
    ↝-putchar : ∀ { E k } { e : Expr Int } { v : ℤ.ℤ }
      → E ⊢ e ⇒ v → 𝒮 (putchar e) k E ~[ emit v ↗ ]↝ 𝒮 nop k E
    ↝-det : ∀ { S S₁ S₂ e f } → S ~[ e ]↝ S₁ → S ~[ f ]↝ S₂ → e ≡ f × S₁ ≡ S₂
    ↝-reduce : ∀ {i} X → Reduction _~[_]↝_ X i
    ↝-irr-cont : ∀ { s s' k₁ k₂ E E' e }
      → 𝒮 s k₁ E ~[ e ]↝ 𝒮 s' k₁ E' → 𝒮 s k₂ E ~[ e ]↝ 𝒮 s' k₂ E'

  labels : State → Labels ∞
  labels = labels-of ∘ ↝-reduce

  infix 0 _≅ₛ_
  _≅ₛ_ : Rel State Level.zero
  X ≅ₛ Y = labels X [≈] labels Y

  field
    ≅ₛ-subst :
      ∀ { α E₁ E₂ k } { v w : ⟦ α ⟧ } { f : Expr α → Statement } { e₁ e₂ : Expr α }
      → E₁ ⊢ e₁ ⇒ v → E₂ ⊢ e₂ ⇒ w → v ≡ w
      → 𝒮 (f e₁) k E₁ ≅ₛ 𝒮 (f e₂) k E₂
    ≅ₛ-decl : ∀ { α f k E } → 𝒮 (decl α λ x → f) k E ≅ₛ 𝒮 f k E
    ≅ₛ-cong :
      ∀ (V : Set) (f : (V → Statement) → Statement) (x y : V → Statement) →
      (∀ v k E → 𝒮 (x v) k E ≅ₛ 𝒮 (y v) k E) →
      (∀ k E → 𝒮 (f x) k E ≅ₛ 𝒮 (f y) k E)

  Stuck : State → Set
  Stuck S = ∀ S' e → ¬ (S ~[ e ]↝ S')

  data Terminating (X : State) : Set where
    [_] : Stuck X → Terminating X
    _∷_ : ∀ { e Y } → X ~[ e ]↝ Y → Terminating Y → Terminating X

  _~[_]↝*_ : {i : Size} → State → Labels ∞ → State → Set
  _~[_]↝*_ {i} X e Y = SmallStep* _~[_]↝_ X Y e i
  
  _~[_]↝⁺_ : {i : Size} → State → Labels ∞ → State → Set
  _~[_]↝⁺_ {i} X e Y = SmallStep⁺ _~[_]↝_ X Y e i
