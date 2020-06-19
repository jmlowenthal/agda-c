open import C.Lang
open import C.Semantics.SmallStep.Model.State
open import Codata.Musical.Colist as Colist hiding ([_])
open import Codata.Musical.Notation
open import Data.Empty
open import Data.List hiding (_++_ ; [_])
open import Data.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable

import Level
import Data.Integer as ℤ
import Data.Integer.DivMod as ℤ÷
import Data.Nat as ℕ
import Data.Bool as 𝔹

open Lang ⦃ ... ⦄

module C.Semantics.SmallStep.Model.Musical ⦃ _ : Lang ⦄ where

-- Based on:
-- Coinductive Verification of Program Optimizations Using Similarity Relations by Glesner et al.
-- Undecidability of Equality for Codata Types by Berger and Setzner

data SideEffect : Set where
  _↦_ : ∀ { α } → Ref α → ⟦ α ⟧ → SideEffect
  emit : ⟦ Int ⟧ → SideEffect
  terminated : SideEffect

data Label : Set where
  τ : Label
  _↗ : SideEffect → Label

data Reduction (_~[_]↝_ : State → Label → State → Set) : (A : State) → Set where
  [] : Reduction _~[_]↝_ Ω
  _∷_ : ∀ { A B α } → A ~[ α ]↝ B → ∞ (Reduction _~[_]↝_ B) → Reduction _~[_]↝_ A

SideEffects : Set
SideEffects = Colist SideEffect

Labels : Set
Labels = Colist Label

τs : ℕ.ℕ → Labels
τs ℕ.zero = []
τs (ℕ.suc n) = τ ∷ ♯ τs n

labels-of : ∀ { R A } → Reduction R A → Labels
labels-of [] = []
labels-of (_∷_ {α = α} h t) = α ∷ ♯ (labels-of (♭ t))

{-# NON_TERMINATING #-} -- May have no side-effects, forever...
labels-to-effects : ∀ (l : Labels) → SideEffects
labels-to-effects [] = []
labels-to-effects (τ ∷ t) = labels-to-effects (♭ t)
labels-to-effects ((x ↗) ∷ t) = x ∷ ♯ (labels-to-effects (♭ t))
  
effects-of : ∀ { R A } → Reduction R A → SideEffects
effects-of r = labels-to-effects (labels-of r)

data Ignorable : Label → Set where
  ignore-τ : Ignorable τ
  ignore-↦ : ∀ { α } { x : Ref α } { v : ⟦ α ⟧ } → Ignorable ((x ↦ v) ↗)

infix 0 _[≈]_
data _[≈]_ : Labels → Labels → Set where
  [] : [] [≈] []
  _∷_ : ∀ x { xs ys } → ∞ ((♭ xs) [≈] (♭ ys)) → (x ∷ xs) [≈] (x ∷ ys)
  left : ∀ { x xs ys } → Ignorable x → ∞ ((♭ xs) [≈] ys) → (x ∷ xs) [≈] ys
  right : ∀ { x xs ys } → Ignorable x → ∞ (xs [≈] (♭ ys)) → xs [≈] (x ∷ ys)

[≈]-refl : Reflexive _[≈]_
[≈]-refl {[]} = []
[≈]-refl {_ ∷ _} = _ ∷ ♯ [≈]-refl

[≈]-reflexive : ∀ { A B } → A ≈ B → A [≈] B
[≈]-reflexive [] = []
[≈]-reflexive (x ∷ xs≈) = x ∷ ♯ [≈]-reflexive (♭ xs≈)

[≈]-sym : Symmetric _[≈]_
[≈]-sym [] = []
[≈]-sym (_ ∷ xs) = _ ∷ ♯ [≈]-sym (♭ xs)
[≈]-sym (left p x) = right p (♯ [≈]-sym (♭ x))
[≈]-sym (right p x) = left p (♯ [≈]-sym (♭ x))

{-# NON_TERMINATING #-}
[≈]-trans : ∀ { i j k } → i [≈] j → j [≈] k → i [≈] k
[≈]-trans [] p = p
[≈]-trans (x ∷ xs) (.x ∷ ys) = _ ∷ ♯ [≈]-trans (♭ xs) (♭ ys)
[≈]-trans (x ∷ xs) (left i p) = left i (♯ [≈]-trans (♭ xs) (♭ p))
[≈]-trans (x ∷ xs) (right i p) = right i (♯ [≈]-trans (x ∷ xs) (♭ p))
[≈]-trans (left i p) j~k = left i (♯ [≈]-trans (♭ p) j~k)
[≈]-trans (right i p) (_ ∷ xs) = right i (♯ [≈]-trans (♭ p) (♭ xs))
[≈]-trans (right _ p) (left _ q) = [≈]-trans (♭ p) (♭ q)
[≈]-trans (right i p) (right j q) = right j (♯ [≈]-trans (right i p) (♭ q))

[≈]-setoid : Setoid _ _
[≈]-setoid = record
  { Carrier = _
  ; _≈_ = _[≈]_
  ; isEquivalence = record
    { refl = [≈]-refl
    ; sym = [≈]-sym
    ; trans = [≈]-trans } }

infixr 4 _◅_
data SmallStep* (_~[_]↝_ : State → Label → State → Set) : State → State → Labels → Set where
  ε : ∀ { X } → SmallStep* _~[_]↝_ X X []
  _◅_ : ∀ { X Y Z e es } → X ~[ e ]↝ Y → ∞ (SmallStep* _~[_]↝_ Y Z (♭ es))
    → SmallStep* _~[_]↝_ X Z (e ∷ es)

_◅◅_ : ∀ { R X Y Z e f } → SmallStep* R X Y e → SmallStep* R Y Z f → SmallStep* R X Z (e ++ f)
ε ◅◅ B = B
(h ◅ t) ◅◅ B = h ◅ ♯ (♭ t ◅◅ B)

SmallStep⁺ : ∀ (_~[_]↝_ : State → Label → State → Set) → State → State → Labels → Set
SmallStep⁺ _~[_]↝_ X Y [] = ⊥
SmallStep⁺ _~[_]↝_ X Y (e ∷ es) = ∃[ X' ] (X ~[ e ]↝ X' × SmallStep* _~[_]↝_ X' Y (♭ es))

reducer : ∀ X { R } → (∀ x k E → ∃[ S' ] ∃[ e ] (R (𝒮 x k E) e S')) → Reduction R X
reducer Ω _ = []
reducer (𝒮 x k E) f =
  let S' , e , S↝S' = f x k E in
    S↝S' ∷ ♯ reducer S' f

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
      → E ⊢ cond ⇒ 𝔹.true → 𝒮 (if cond then s₁ else s₂) k E ~[ τ ]↝ 𝒮 s₁ k E
    ↝-if-false : ∀ { E k } { cond : Expr Bool } { s₁ s₂ : Statement }
      → E ⊢ cond ⇒ 𝔹.false → 𝒮 (if cond then s₁ else s₂) k E ~[ τ ]↝ 𝒮 s₂ k E
    ↝-assignment : ∀ { E k α } { id : Ref α } { e : Expr α } { v : ⟦ α ⟧ }
      → E ⊢ e ⇒ v → 𝒮 (id ≔ e) k E ~[ (id ↦ v) ↗ ]↝ 𝒮 nop k (id Env.↦ v , E)
    ↝-seq : ∀ { E k } { s₁ s₂ : Statement }
      → 𝒮 (s₁ ； s₂) k E ~[ τ ]↝ 𝒮 s₁ (s₂ ∷ k) E
    ↝-decl : ∀ { E k α } { f : Ref α → Statement }
      → ∃ λ (x : Ref α) → (x ∉nv E) × (𝒮 (decl α f) k E ~[ τ ]↝ 𝒮 (f x) k (x , E))
    ↝-nop : ∀ { E k } { s : Statement } → 𝒮 nop (s ∷ k) E ~[ τ ]↝ 𝒮 s k E
    ↝-stuck : ∀ { E } → 𝒮 nop [] E ~[ terminated ↗ ]↝ Ω
    ↝-Ω : ∀ { S' e } → ¬ (Ω ~[ e ]↝ S')
    ↝-for : ∀ { E k } { l u : Expr Int } { f : Ref Int → Statement } { x : Ref Int }
      → 𝒮 (for l to u then f) k E
        ~[ τ ]↝ 𝒮 (if (l < u) then (
                (decl Int λ i → i ≔ l ； f i) ；
                for (l + ⟪ ℤ.+ 1 ⟫) to u then f)
             else nop) k E
    ↝-while : ∀ { E k } { e : Expr Bool } { s : Statement }
      → 𝒮 (while e then s) k E ~[ τ ]↝ 𝒮 (if e then (s ； while e then s) else nop) k E
    ↝-putchar : ∀ { E k } { e : Expr Int } { v : ℤ.ℤ }
      → E ⊢ e ⇒ v → 𝒮 (putchar e) k E ~[ emit v ↗ ]↝ 𝒮 nop k E
    ↝-det : ∀ { S S₁ S₂ e f } → S ~[ e ]↝ S₁ → S ~[ f ]↝ S₂ → e ≡ f × S₁ ≡ S₂
    ↝-progress : ∀ (x k E) → ∃[ S' ] ∃[ e ] (𝒮 x k E ~[ e ]↝ S')
    ↝-irr-cont : ∀ { s s' k₁ k₂ E E' e }
      → 𝒮 s k₁ E ~[ e ]↝ 𝒮 s' k₁ E' → 𝒮 s k₂ E ~[ e ]↝ 𝒮 s' k₂ E'

  reduce : ∀ X → Reduction _~[_]↝_ X
  reduce X = reducer X ↝-progress

  labels : State → Labels
  labels X = labels-of (reduce X)

  effects : State → SideEffects
  effects X = effects-of (reduce X)

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

  _~[_]↝*_ : State → Labels → State → Set
  X ~[ e ]↝* Y = SmallStep* _~[_]↝_ X Y e
  
  _~[_]↝⁺_ : State → Labels → State → Set
  X ~[ e ]↝⁺ Y = SmallStep⁺ _~[_]↝_ X Y e
