{-# OPTIONS --safe --exact-split --sized-types #-}

open import Level using (0ℓ)
open import Size using (Size ; ∞)

open import C.Lang
open import C.Semantics.SmallStep.Model.State

open import Codata.Colist as Colist hiding (_++_ ; [_] ; fromList)
open import Codata.Cowriter using (Cowriter ; [_] ; _∷_)
import Codata.Cowriter.Bisimilarity as W
open import Codata.Conat using (Conat)
open import Codata.Delay
open import Codata.Thunk
open import Data.Empty
open import Data.Unit hiding (setoid)
open import Data.Nat as ℕ using (ℕ)
open import Data.Nat.Properties
open import Data.List hiding (_++_ ; [_])
open import Data.Product
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Unary using (Pred)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_] ; setoid)
open import Algebra.Definitions
open import Function

import Data.Integer as ℤ
import Data.Integer.DivMod as ℤ÷
import Data.Bool as 𝔹

open Lang ⦃ ... ⦄

module C.Semantics.SmallStep.Model.Musical ⦃ _ : Lang ⦄ where

private
  variable
    i : Size

-- Based on:
-- Coinductive Verification of Program Optimizations Using Similarity Relations by Glesner et al.
-- Undecidability of Equality for Codata Types by Berger and Setzer

data Effect : Set where
  _↦_ : ∀ { α } → Ref α → ⟦ α ⟧ → Effect
  emit : ⟦ Int ⟧ → Effect
  terminated : Effect

Effects : Size → Set
Effects = Colist Effect

infix 10 _↗
data Label : Set where
  τ  : Label
  _↗ : Effect → Label

Process : Size → Set → Set → Set
Process i F I = Cowriter (I × F) I i

Labels : Size → Set
Labels i = Process i Effect ℕ

labels-to-effects : Labels i → Effects i
labels-to-effects ([ _ ]) = []
labels-to-effects ((_ , x) ∷ xs) = x ∷ λ where .force → labels-to-effects (force xs)

_++_ : Labels i → Labels i → Labels i
[ x ]    ++ [ y ]            = [ x ℕ.+ y ]
[ x ]    ++ ((y , eff) ∷ ys) = ( x ℕ.+ y , eff) ∷ ys
(x ∷ xs) ++ ys               = x ∷ λ where .force → force xs ++ ys

τ∷ : Labels ∞ → Labels i
τ∷ = [ 1 ] ++_

τ+ : ℕ × Effect → ℕ × Effect
τ+ = map₁ ℕ.suc

_↗∷_ : Effect → Thunk Labels i → Labels i
eff ↗∷ ls = (0 , eff) ∷ ls

infix 0 _⊢_≈_
_⊢_≈_ : Size → Rel (Labels ∞) 0ℓ
_⊢_≈_ = W._⊢_≈_

infix 0 _≈_
_≈_ = ∞ ⊢_≈_

≈-refl = W.refl
≈-sym = W.sym
≈-trans = W.trans

++-identityˡ : LeftIdentity (i ⊢_≈_) [ 0 ] _++_
++-identityˡ ([ x ])  = W.refl
++-identityˡ (x ∷ x₁) = W.refl

++-identityʳ : RightIdentity (i ⊢_≈_) [ 0 ] _++_
++-identityʳ ([ x ])  = W.fromEq (cong [_] (+-comm x 0))
++-identityʳ (x ∷ xs) = refl W.∷ λ where .force → ++-identityʳ (force xs)

++-assoc : Associative (i ⊢_≈_) _++_
++-assoc [ x ]    [ y ]     ([ z ])          = W.fromEq (cong [_] (+-assoc x y z))
++-assoc [ x ]    [ y ]     ((z , eff) ∷ zs) = W.fromEq (cong (λ n → (n , eff) ∷ zs) (+-assoc x y z))
++-assoc [ _ ]    (_ ∷ _)   _                = W.refl
++-assoc (x ∷ xs) ys        zs               = refl W.∷ λ where .force → ++-assoc (force xs) ys zs

-- TODO: ++ and [ 0 ] form a monoid under ≈ and thus [≈]

infix 0 _⊢_[≈]_
_⊢_[≈]_ : Size → Rel (Labels ∞) 0ℓ
_⊢_[≈]_ = W.Bisim (_≡_ on proj₂) (const (const ⊤))

infix 0 _[≈]_
_[≈]_ = ∞ ⊢_[≈]_

[≈]-refl : Reflexive (i ⊢_[≈]_)
[≈]-refl = W.reflexive refl tt

[≈]-sym : Symmetric (i ⊢_[≈]_)
[≈]-sym = W.symmetric sym (const tt)

[≈]-trans : Transitive (i ⊢_[≈]_)
[≈]-trans = W.transitive trans const

≈⇒[≈] : ∀ {A B} → i ⊢ A ≈ B → i ⊢ A [≈] B
≈⇒[≈] W.[ x ] = W.[ tt ]
≈⇒[≈] (refl W.∷ xs) = refl W.∷ λ where .force → ≈⇒[≈] (force xs)

τ∷x[≈]x : ∀ {x} → τ∷ x [≈] x
τ∷x[≈]x {[ _ ]} = W.[ tt ]
τ∷x[≈]x {_ ∷ xs} = refl W.∷ λ where .force → [≈]-refl

Transition : Set₁
Transition = State → Label → State → Set

infixr 4 _↗◅_
infixr 4 _↓◅_
data SmallStep* (_~[_]↝_ : Transition) : Labels i → Size → Rel State 0ℓ where
  ε     : ∀ { X }                                                                                → SmallStep* _~[_]↝_ [ 0 ]         i X X
  _↓_   : ∀ { X Y Z n }    → X ~[ τ   ]↝ Y →              SmallStep* _~[_]↝_ [ n ]      i Y Z    → SmallStep* _~[_]↝_ [ ℕ.suc n ]   i X Z
  _↓◅_  : ∀ { X Y Z e es } → X ~[ τ   ]↝ Y →              SmallStep* _~[_]↝_ (e ∷ es)   i Y Z    → SmallStep* _~[_]↝_ (τ+ e ∷ es) i X Z
  _↗◅_  : ∀ { X Y Z e es } → X ~[ e ↗ ]↝ Y → Thunk (λ j → SmallStep* _~[_]↝_ (force es) j Y Z) i → SmallStep* _~[_]↝_ (e ↗∷ es)     i X Z

_↗◂ : ∀ {R X e Y} → R X (e ↗) Y → SmallStep* R (e ↗∷ λ where .force → [ 0 ]) i X Y
x ↗◂ = x ↗◅ λ where .force → ε

_↓∷_ : ∀ {_~[_]↝_ es X Y Z} → X ~[ τ ]↝ Y → SmallStep* _~[_]↝_ es i Y Z → SmallStep* _~[_]↝_ (τ∷ es) i X Z
X↝Y ↓∷ ε             = X↝Y ↓  ε
X↝Y ↓∷ Y↝*Z@(_ ↓ _)  = X↝Y ↓  Y↝*Z
X↝Y ↓∷ Y↝*Z@(_ ↓◅ _) = X↝Y ↓◅ Y↝*Z
X↝Y ↓∷ Y↝*Z@(_ ↗◅ _) = X↝Y ↓◅ Y↝*Z

SmallStep*-≈ : ∀ {R e f X Y} → SmallStep* R e i X Y → e ≈ f → SmallStep* R f i X Y
SmallStep*-≈  X↝*Y       W.[ refl ]        = X↝*Y
SmallStep*-≈ (x ↗◅ xs)   (refl W.∷ e≈f)   = x ↗◅ λ where .force → SmallStep*-≈ (force xs) (force e≈f)
SmallStep*-≈ (x ↓◅ X↝*Y) e≈f@(refl W.∷ _) = unroll (x ↓◅ X↝*Y) e≈f
  where
    unroll : ∀ {i R X Y n eff e f} → SmallStep* R ((ℕ.suc n , eff) ∷ e) i X Y → ((ℕ.suc n , eff) ∷ e) ≈ ((ℕ.suc n , eff) ∷ f) → SmallStep* R ((ℕ.suc n , eff) ∷ f) i X Y
    unroll (x ↓◅ X↝*Y@(_ ↓◅ _)) (_ W.∷ e≈f) = x ↓◅ unroll X↝*Y (refl W.∷ e≈f)
    unroll (x ↓◅ X↝*Y@(_ ↗◅ _)) (_ W.∷ e≈f) = x ↓◅ (SmallStep*-≈ X↝*Y (refl W.∷ e≈f))

-- This is the monoidal operation (≈ transitivity)
_◅◅_ : ∀ { R e f X Y Z } → SmallStep* R e ∞ X Y → SmallStep* R f ∞ Y Z → SmallStep* R (e ++ f) i X Z
ε ◅◅ ε         = ε
ε ◅◅ (x ↓ xs)  = x ↓  (ε ◅◅ xs)
ε ◅◅ (x ↓◅ xs) = x ↓◅ (ε ◅◅ xs)
ε ◅◅ (x ↗◅ xs) = x ↗◅ λ where .force → force xs
(h ↓ t)  ◅◅ B = SmallStep*-≈ (h ↓∷ (t ◅◅ B)) (W.sym (++-assoc _ _ _))
(h ↓◅ t) ◅◅ B = h ↓◅ (t ◅◅ B)
(h ↗◅ t) ◅◅ B = h ↗◅ λ where .force → force t ◅◅ B

_≈ₛ_ : ∀ {R e f X Y} → SmallStep* R e i X Y → SmallStep* R f i X Y → Set
_≈ₛ_ {e = e} {f} _ _ = e ≈ f

≈ₛ-refl : ∀ {R e X Y} {x : SmallStep* R e i X Y} → x ≈ₛ x
≈ₛ-refl = ≈-refl

≈ₛ-sym : ∀ {R e f X Y} {x : SmallStep* R e i X Y} {y : SmallStep* R f i X Y} → x ≈ₛ y → y ≈ₛ x
≈ₛ-sym = ≈-sym

≈ₛ-trans : ∀ {R e f g X Y} {x : SmallStep* R e i X Y} {y : SmallStep* R f i X Y} {z : SmallStep* R g i X Y} → x ≈ₛ y → y ≈ₛ z → x ≈ₛ z
≈ₛ-trans = ≈-trans

◅◅-identityˡ : ∀ {R e X Y} (x : SmallStep* R e ∞ X Y) → (ε ◅◅ x) ≈ₛ x
◅◅-identityˡ {e = e} _ = ++-identityˡ e

◅◅-identityʳ : ∀ {R e X Y} (x : SmallStep* R e ∞ X Y) → (x ◅◅ ε) ≈ₛ x
◅◅-identityʳ {e = e} _ = ++-identityʳ e

◅◅-assoc : ∀ {R e f g X Y Z W} (x : SmallStep* R e ∞ X Y) (y : SmallStep* R f ∞ Y Z) (z : SmallStep* R g ∞ Z W) → ((x ◅◅ y) ◅◅ z) ≈ₛ (x ◅◅ (y ◅◅ z))
◅◅-assoc {e = e} {f} {g} _ _ _ = ++-assoc e f g

Reduction : Transition → State → Size → Set
Reduction R A i = ∃[ es ] SmallStep* R es i A Ω

labels-of : ∀ { R A } → Reduction R A i → Labels i
labels-of = proj₁

effects-of : ∀ { R A } → Reduction R A i → Effects i
effects-of = labels-to-effects ∘ labels-of


record Semantics : Set₁ where
  field
    _⊢_⇒_ : ∀ { α } → Env → Expr α → ⟦ α ⟧ → Set
    _~[_]↝_ : Transition

    ⊢-total : ∀ { α } E (e : Expr α) → ∃[ v ] (E ⊢ e ⇒ v) -- should ensure no free variables
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
      → E ⊢ e ⇒ v → 𝒮 (id ≔ e) k E ~[ id ↦ v ↗ ]↝ 𝒮 nop k (id Env.↦ v , E)
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
    ↝-irr-cont : ∀ { s s' k₁ k₂ E E' e }
      → 𝒮 s k₁ E ~[ e ]↝ 𝒮 s' k₁ E' → 𝒮 s k₂ E ~[ e ]↝ 𝒮 s' k₂ E'

    ↝-reduce : ∀ {i} X → Reduction _~[_]↝_ X i

  _⊢_~[_]↝*_ : (i : Size) → State → Labels i → State → Set
  _⊢_~[_]↝*_ i X e Y = SmallStep* _~[_]↝_ e i X Y

  _~[_]↝*_ : State → Labels ∞ → State → Set
  _~[_]↝*_ = ∞ ⊢_~[_]↝*_

  reduce-labels : State → Labels ∞
  reduce-labels = labels-of ∘ ↝-reduce

  reduce-effects : State → Effects ∞
  reduce-effects = effects-of ∘ ↝-reduce

  _⊢_≅ₛ_ : Size → Rel State 0ℓ
  _⊢_≅ₛ_ i = (i ⊢_[≈]_) on reduce-labels

  infix 0 _≅ₛ_
  _≅ₛ_ : Rel State 0ℓ
  _≅ₛ_ = ∞ ⊢_≅ₛ_

  field
    ≅ₛ-subst :
      ∀ { α E₁ E₂ k } { v w : ⟦ α ⟧ } { f : Expr α → Statement } { e₁ e₂ : Expr α }
      → E₁ ⊢ e₁ ⇒ v → E₂ ⊢ e₂ ⇒ w → v ≡ w
      → 𝒮 (f e₁) k E₁ ≅ₛ 𝒮 (f e₂) k E₂
    ≅ₛ-decl : ∀ { α s k E } → 𝒮 (decl α (const s)) k E ≅ₛ 𝒮 s k E
    ≅ₛ-cong :
      ∀ (V : Set) (f : (V → Statement) → Statement) (x y : V → Statement) →
      (∀ v k E → 𝒮 (x v) k E ≅ₛ 𝒮 (y v) k E) →
      (∀ k E → 𝒮 (f x) k E ≅ₛ 𝒮 (f y) k E)

  Stuck : State → Set
  Stuck S = ∀ S' e → ¬ (S ~[ e ]↝ S')

  data Terminating (X : State) : Set where
    [_] : Stuck X → Terminating X
    _∷_ : ∀ { e Y } → X ~[ e ]↝ Y → Terminating Y → Terminating X

module X (S : Semantics) where
  open Semantics S

  ↗↓⇒⊥ : ∀ {A e B C} → A ~[ e ↗ ]↝ B → A ~[ τ ]↝ C → ⊥
  ↗↓⇒⊥ A↗B AτC with ↝-det A↗B AτC
  ... | ()

  -- TODO: are the ≈ₛ necessary? can we make a type combinator?
  data ↝*-det : ∀ { A B es fs } → i ⊢ A ~[ es ]↝* B → i ⊢ A ~[ fs ]↝* B → Set where
    τ-run  : ∀ {A B n} → (x y : A ~[ [ n ] ]↝* B) → ↝*-det x y
    coalg  : ∀ {A X Y B n e es fs}
               (A↝X : A ~[ [ n ] ]↝* X) (X↝Y : X ~[ e ↗ ]↝ Y)
               (Y↝B : i ⊢ Y ~[ force es ]↝* B) (Y↝B′ : i ⊢ Y ~[ force fs ]↝* B)
               (A↝B : i ⊢ A ~[ (n , e) ∷ es ]↝* B) (A↝B′ : i ⊢ A ~[ (n , e) ∷ fs ]↝* B) →
               ↝*-det {i} A↝B A↝B′
    dloopˡ : ∀ {A B es n} (sled : A ~[ es ]↝* B) (loop : B ~[ [ ℕ.suc n ] ]↝* B) (sloop : A ~[ es ++ [ ℕ.suc n ] ]↝* B) → (sled ◅◅ loop) ≈ₛ sloop → ↝*-det sloop sled
    dloopʳ : ∀ {A B es n} (sled : A ~[ es ]↝* B) (loop : B ~[ [ ℕ.suc n ] ]↝* B) (sloop : A ~[ es ++ [ ℕ.suc n ] ]↝* B) → (sled ◅◅ loop) ≈ₛ sloop → ↝*-det sled sloop
    ploopˡ : ∀ {A B ss e es} (sled : A ~[ ss ]↝* B) (loop : B ~[ e ∷ es ]↝* B) (sloop : A ~[ ss ++ (e ∷ es) ]↝* B) → (sled ◅◅ loop) ≈ₛ sloop → ↝*-det sloop sled
    ploopʳ : ∀ {A B ss e es} (sled : A ~[ ss ]↝* B) (loop : B ~[ e ∷ es ]↝* B) (sloop : A ~[ ss ++ (e ∷ es) ]↝* B) → (sled ◅◅ loop) ≈ₛ sloop → ↝*-det sled sloop

  ↝*-det? : ∀ {A B es fs} (x : i ⊢ A ~[ es ]↝* B) (y : i ⊢ A ~[ fs ]↝* B) → ↝*-det {i} x y
  ↝*-det? ε ε = τ-run ε ε
  ↝*-det? ε y@(_ ↓ _) = dloopʳ ε y y W.refl
  ↝*-det? ε y@(_ ↓◅ _) = ploopʳ ε y y W.refl
  ↝*-det? ε y@(_ ↗◅ _) = ploopʳ ε y y W.refl
  ↝*-det? x@(_ ↓ _) ε = dloopˡ ε x x W.refl
  ↝*-det? (A↝X ↓ X↝B) (A↝Y ↓ Y↝B) with ↝-det A↝X A↝Y
  ... | refl , refl with ↝*-det? X↝B Y↝B
  ... | τ-run .X↝B .Y↝B = τ-run (A↝X ↓ X↝B) (A↝Y ↓ Y↝B)
  ... | dloopˡ .Y↝B loop sloop _ = dloopˡ (A↝Y ↓ Y↝B) loop (A↝X ↓ sloop) W.refl
  ... | dloopʳ .X↝B loop sloop _ = dloopʳ (A↝X ↓ X↝B) loop (A↝Y ↓ sloop) W.refl
  ↝*-det? (A↝X ↓ X↝B) (A↝Y ↓◅ Y↝B) with ↝-det A↝X A↝Y
  ... | refl , refl with ↝*-det? X↝B Y↝B
  ... | ploopʳ .X↝B loop .Y↝B x = ploopʳ (A↝X ↓ X↝B) loop (A↝Y ↓◅ Y↝B) W.refl
  ↝*-det? (A↝X ↓ X↝B) (A↝Y ↗◅ Y↝B) = ⊥-elim (↗↓⇒⊥ A↝Y A↝X)
  ↝*-det? x@(_ ↓◅ _) ε = ploopˡ ε x x W.refl
  ↝*-det? (A↝X ↓◅ X↝B) (A↝Y ↓ Y↝B) with ↝-det A↝X A↝Y
  ... | refl , refl with ↝*-det? X↝B Y↝B
  ... | ploopˡ .Y↝B loop .X↝B x = ploopˡ (A↝Y ↓ Y↝B) loop (A↝X ↓◅ X↝B) W.refl
  ↝*-det? (A↝X ↓◅ X↝B) (A↝Y ↓◅ Y↝B) with ↝-det A↝X A↝Y
  ... | refl , refl with ↝*-det? X↝B Y↝B
  ... | coalg X↝X′ X′↝Y Y↝B₁ Y↝B′ .X↝B .Y↝B = coalg (A↝X ↓ X↝X′) X′↝Y Y↝B₁ Y↝B′ (A↝X ↓◅ X↝B) (A↝Y ↓◅ Y↝B)
  ... | dloopˡ .Y↝B loop .X↝B x = dloopˡ (A↝Y ↓◅ Y↝B) loop (A↝X ↓◅ X↝B) W.refl
  ... | dloopʳ .X↝B loop .Y↝B x = dloopʳ (A↝X ↓◅ X↝B) loop (A↝Y ↓◅ Y↝B) W.refl
  ... | ploopˡ .Y↝B loop .X↝B x = ploopˡ (A↝Y ↓◅ Y↝B) loop (A↝X ↓◅ X↝B) W.refl
  ... | ploopʳ .X↝B loop .Y↝B x = ploopʳ (A↝X ↓◅ X↝B) loop (A↝Y ↓◅ Y↝B) W.refl
  ↝*-det? (A↝X ↓◅ X↝B) (A↝Y ↗◅ Y↝B) = ⊥-elim (↗↓⇒⊥ A↝Y A↝X)
  ↝*-det? x@(_ ↗◅ _) ε = ploopˡ ε x x W.refl
  ↝*-det? (A↝X ↗◅ X↝B) (A↝Y ↓ Y↝B) = ⊥-elim (↗↓⇒⊥ A↝X A↝Y)
  ↝*-det? (A↝X ↗◅ X↝B) (A↝Y ↓◅ Y↝B) = ⊥-elim (↗↓⇒⊥ A↝X A↝Y)
  ↝*-det? (A↝X ↗◅ X↝B) (A↝Y ↗◅ Y↝B) with ↝-det A↝X A↝Y
  ... | refl , refl = coalg ε A↝X (force X↝B) (force Y↝B) (A↝X ↗◅ X↝B) (A↝Y ↗◅ Y↝B)

  reduce-det : ∀ { A } (x y : Reduction _~[_]↝_ A ∞) → i ⊢ labels-of x ≈ labels-of y
  reduce-det (xl , xs) (yl , ys) with ↝*-det? xs ys
  ... | τ-run .xs .ys = W.refl
  ... | coalg A↝X X↝Y Y↝B Y↝B′ .xs .ys = refl W.∷ λ where .force → reduce-det (_ , Y↝B) (_ , Y↝B′)
  ... | dloopˡ .ys (x ↓  _) .xs _ = ⊥-elim (↝-Ω x)
  ... | dloopʳ .xs (x ↓  _) .ys _ = ⊥-elim (↝-Ω x)
  ... | ploopˡ .ys (x ↓◅ _) .xs _ = ⊥-elim (↝-Ω x)
  ... | ploopˡ .ys (x ↗◅ _) .xs _ = ⊥-elim (↝-Ω x)
  ... | ploopʳ .xs (x ↓◅ _) .ys _ = ⊥-elim (↝-Ω x)
  ... | ploopʳ .xs (x ↗◅ _) .ys _ = ⊥-elim (↝-Ω x)
  
  extend-τ : ∀ {A A′ B} → A′ ~[ τ ]↝ A → i ⊢ A ≅ₛ B → i ⊢ A′ ≅ₛ B
  extend-τ {_} {A} {A′} {B} A′↝A A≅ₛB with ↝-reduce A′
  ... | _ , ε = ⊥-elim (↝-Ω A′↝A)
  ... | _ , A′↝Y ↗◅ _ = ⊥-elim (↗↓⇒⊥ A′↝Y A′↝A)
  extend-τ {_} {A} {A′} {B} A′↝A A≅ₛB | _ , A′↝Y ↓  snd rewrite proj₂ (↝-det A′↝Y A′↝A) =
    [≈]-trans ([≈]-trans τ∷x[≈]x (≈⇒[≈] (reduce-det (_ , snd) (↝-reduce A)))) A≅ₛB
  extend-τ {_} {A} {A′} {B} A′↝A A≅ₛB | _ , A′↝Y ↓◅ snd rewrite proj₂ (↝-det A′↝Y A′↝A) =
    [≈]-trans ([≈]-trans τ∷x[≈]x (≈⇒[≈] (reduce-det (_ , snd) (↝-reduce A)))) A≅ₛB

  extend-τs : ∀ {A A′ B n} → A′ ~[ [ n ] ]↝* A → i ⊢ A ≅ₛ B → i ⊢ A′ ≅ₛ B
  extend-τs ε A≅ₛB = A≅ₛB
  extend-τs (A′↝Y ↓ Y↝A) A≅ₛB = extend-τ A′↝Y (extend-τs Y↝A A≅ₛB)

  extend-↗′ : ∀ {A A′ B B′ e} → A′ ~[ e ↗ ]↝ A → B′ ~[ e ↗ ]↝ B → Thunk (_⊢ A ≅ₛ B) i → i ⊢ A′ ≅ₛ B′
  extend-↗′ {A′ = A′} {B′ = B′} A′↝A B′↝B A≅ₛB with ↝-reduce A′
  ... | _ , ε         = ⊥-elim (↝-Ω A′↝A)
  ... | _ , A′↝Y ↓  _ = ⊥-elim (↗↓⇒⊥ A′↝A A′↝Y)
  ... | _ , A′↝Y ↓◅ _ = ⊥-elim (↗↓⇒⊥ A′↝A A′↝Y)
  ... | _ , _↗◅_ {Y = Y} A′↝Y Y↝Ω with ↝-det A′↝A A′↝Y
  ... | refl , refl with ↝-reduce B′
  ... | _ , ε         = ⊥-elim (↝-Ω B′↝B)
  ... | _ , B′↝Z ↓  _ = ⊥-elim (↗↓⇒⊥ B′↝B B′↝Z)
  ... | _ , B′↝Z ↓◅ _ = ⊥-elim (↗↓⇒⊥ B′↝B B′↝Z)
  ... | _ , _↗◅_ {Y = Z} B′↝Z Z↝Ω with ↝-det B′↝B B′↝Z
  ... | refl , refl =
    refl W.∷ λ where .force → [≈]-trans (≈⇒[≈] (reduce-det (_ , force Y↝Ω) (↝-reduce Y))) ([≈]-trans (force A≅ₛB) (≈⇒[≈] (reduce-det (↝-reduce Z) (_ , force Z↝Ω))))

  extend-↗ : ∀ {A A′ B B′ e} → A′ ~[ e ↗ ]↝ A → B′ ~[ e ↗ ]↝ B → A ≅ₛ B → A′ ≅ₛ B′
  extend-↗ A′↝A B′↝B A≅ₛB = extend-↗′ A′↝A B′↝B λ where .force → A≅ₛB

  extend* : ∀ {A B es fs A′ B′} → i ⊢ A ≅ₛ B → A′ ~[ es ]↝* A → B′ ~[ fs ]↝* B → i ⊢ es [≈] fs → i ⊢ A′ ≅ₛ B′
  extend* A≅B A′↝A          B′↝B          W.[ tt ]       = [≈]-sym (extend-τs B′↝B ([≈]-sym (extend-τs A′↝A A≅B)))
  extend* A≅B (A′↝Y ↓◅ Y↝A) B′↝B          (refl W.∷ eqs) = extend-τ A′↝Y (extend* A≅B Y↝A B′↝B (refl W.∷ eqs))
  extend* A≅B A′↝A@(_ ↗◅ _) (B′↝Z ↓◅ Z↝B) (refl W.∷ eqs) = [≈]-sym (extend-τ B′↝Z ([≈]-sym (extend* A≅B A′↝A Z↝B (refl W.∷ eqs))))
  extend* A≅B (A′↝Y ↗◅ Y↝A) (B′↝Z ↗◅ Z↝B) (refl W.∷ eqs) = extend-↗′ A′↝Y B′↝Z λ where .force → extend* A≅B (force Y↝A) (force Z↝B) (force eqs)


  infix 0 _≅ₚ_
  _≅ₚ_ : Rel Statement 0ℓ
  x ≅ₚ y = ∀ {k E} → 𝒮 x k E ≅ₛ 𝒮 y k E

  ⁇-lemma : ∀ { α } { r : Ref α } { a : Expr Bool } { b c : Expr α } → r ≔ a ⁇ b ∷ c ≅ₚ if a then r ≔ b else r ≔ c
  ⁇-lemma {r = r} {a} {b} {c} {k} {E = E} with ⊢-total E a
  ... | 𝔹.false , snd =
    extend* [≈]-refl
            (↝-assignment (⁇-eval-f snd (proj₂ (⊢-total E c))) ↗◂)
            (↝-if-false snd ↓◅ ↝-assignment (proj₂ (⊢-total E c)) ↗◂)
            ([≈]-sym τ∷x[≈]x)
  ... | 𝔹.true , snd =
    extend* [≈]-refl
            (↝-assignment (⁇-eval-t snd (proj₂ (⊢-total E b))) ↗◂)
            (↝-if-true snd ↓◅ ↝-assignment (proj₂ (⊢-total E b)) ↗◂)
            ([≈]-sym τ∷x[≈]x)
