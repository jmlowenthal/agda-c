open import Algebra.FunctionProperties
open import C
open import C.Properties.State
open import Codata.Musical.Colist as Colist hiding ([_])
open import Codata.Musical.Notation
open import Data.Empty
open import Data.List as L using (List ; [] ; _∷_)
open import Data.Maybe
open import Data.Product
open import Data.Sum
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable

import Level
import Data.Integer as ℤ
import Data.Integer.DivMod as ℤ÷
import Data.Nat as ℕ
import Data.Bool as 𝔹
import Codata.Musical.Conat as Coℕ
import Relation.Binary.Reasoning.Setoid as SReason

open C ⦃ ... ⦄

module C.Properties.Musical ⦃ _ : C ⦄ where

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

Congruence : ∀ { a l } { A : Set a } → Rel A l → Set _
Congruence {A = A} _~_ = ∀ (f : A → A) x y → x ~ y → (f x) ~ (f y)

record Semantics : Set₁ where
  field
    _⊢_⇒_ : ∀ { α } → Env → Expr α → ⟦ α ⟧ → Set
    _~[_]↝_ : State → Label → State → Set
    reduce : ∀ X → Reduction _~[_]↝_ X

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
    ↝-progress : ∀ (x k E) → (x ≡ nop × k ≡ []) ⊎ (∃[ S' ] ∃[ e ] (𝒮 x k E ~[ e ]↝ S'))
    ↝-irr-cont : ∀ { s s' k₁ k₂ E E' e }
      → 𝒮 s k₁ E ~[ e ]↝ 𝒮 s' k₁ E' → 𝒮 s k₂ E ~[ e ]↝ 𝒮 s' k₂ E'

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
    ≅ₛ-cong : Congruence _≅ₛ_

open Semantics ⦃ ... ⦄
module _ ⦃ _ : Semantics ⦄ where

  infix 0 _≅ₑ_
  _≅ₑ_ : ∀ { α } → Rel (Expr α) Level.zero
  _≅ₑ_ { α } x y = ∀ { E : Env } { v w : ⟦ α ⟧ }
    → (E ⊢ x ⇒ v) → (E ⊢ y ⇒ w) → (v ≡ w)

  Stuck : State → Set
  Stuck S = ∀ S' e → ¬ (S ~[ e ]↝ S')

  data Terminating (X : State) : Set where
    [_] : Stuck X → Terminating X
    _∷_ : ∀ { e Y } → X ~[ e ]↝ Y → Terminating Y → Terminating X

  -- EXPRESSION EQUIVALENCE

  ≅ₑ-refl : ∀ { α } → Reflexive (_≅ₑ_ {α})
  ≅ₑ-refl ⇒v ⇒w = ⊢-det ⇒v ⇒w

  ≅ₑ-sym : ∀ { α } → Symmetric (_≅ₑ_ {α})
  ≅ₑ-sym i≅j ⇒v ⇒w = sym (i≅j ⇒w ⇒v)

  ≅ₑ-trans : ∀ { α } → Transitive (_≅ₑ_ {α})
  ≅ₑ-trans i≅j j≅k ⇒v ⇒w =
    let _ , ⇒a = ⊢-total in
      trans (i≅j ⇒v ⇒a) (j≅k ⇒a ⇒w)

  ≅ₑ-equiv : ∀ { α } → IsEquivalence (_≅ₑ_ {α})
  ≅ₑ-equiv = record { refl = ≅ₑ-refl ; sym = ≅ₑ-sym ; trans = ≅ₑ-trans }


  -- REDUCTION LEMMAS
    
  _~[_]↝*_ : State → Labels → State → Set
  X ~[ e ]↝* Y = SmallStep* _~[_]↝_ X Y e
  
  _~[_]↝⁺_ : State → Labels → State → Set
  X ~[ e ]↝⁺ Y = SmallStep⁺ _~[_]↝_ X Y e

  ↝*-trans : ∀ { e f } → Trans (_~[ e ]↝*_) (_~[ f ]↝*_) (_~[ e ++ f ]↝*_)
  ↝*-trans ε j↝*k = j↝*k
  ↝*-trans (i↝X ◅ X↝*j) j↝*k = i↝X ◅ ♯ (↝*-trans (♭ X↝*j) j↝*k)

  ↝*-to-↝⁺ : ∀ { A B C e es } → A ~[ e ]↝ B → B ~[ es ]↝* C → A ~[ e ∷ ♯ es ]↝⁺ C
  ↝*-to-↝⁺ A↝B B↝*C = _ , A↝B , B↝*C

  ↝⁺-to-↝* : ∀ { A B es } → A ~[ es ]↝⁺ B → A ~[ es ]↝* B
  ↝⁺-to-↝* {A} {B} {[]} ()
  ↝⁺-to-↝* {es = _ ∷ _} (X , A↝X , X↝*B) = A↝X ◅ ♯ X↝*B

  ↝̸-transᵇ : ∀ { S S' : State } { e }
    → S ~[ e ]↝* S' → Finite e → Terminating S' → Terminating S
  ↝̸-transᵇ ε _ S'↝ = S'↝
  ↝̸-transᵇ (S↝X ◅ X↝*S') (_ ∷ p) S'↝ = S↝X ∷ ↝̸-transᵇ (♭ X↝*S') p S'↝

  ↝̸-transᶠ : ∀ { S S' : State } { e }
    → S ~[ e ]↝* S' → Finite e → Terminating S → Terminating S'
  ↝̸-transᶠ ε _ S↝ = S↝
  ↝̸-transᶠ (S↝X ◅ X↝*S') (_ ∷ p) ([ S↝̸ ]) = ⊥-elim (S↝̸ _ _ S↝X)
  ↝̸-transᶠ (S↝X ◅ X↝*S') (_ ∷ p) (S↝Y ∷ Y↝)
    rewrite proj₂ (↝-det S↝X S↝Y) = ↝̸-transᶠ (♭ X↝*S') p Y↝

  ↝ω-transᵇ : ∀ { X Y : State } { e }
    → X ~[ e ]↝* Y → Finite e → ¬ Terminating Y → ¬ Terminating X
  ↝ω-transᵇ X↝*Y p Y↝ω X↝̸ = Y↝ω (↝̸-transᶠ X↝*Y p X↝̸)

  ↝ω-transᶠ : ∀ { X Y : State } { e }
    → X ~[ e ]↝* Y → Finite e → ¬ Terminating X → ¬ Terminating Y
  ↝ω-transᶠ X↝*Y p X↝ω Y↝̸ = X↝ω (↝̸-transᵇ X↝*Y p Y↝̸)

  {-# NON_TERMINATING #-} -- Either reduction could be infinite
  ↝*-det : ∀ { S S₁ S₂ x y }
    → Stuck S₁ → Stuck S₂ → S ~[ x ]↝* S₁ → S ~[ y ]↝* S₂ → S₁ ≡ S₂
  ↝*-det _ _ ε ε = refl
  ↝*-det S↝̸ _ ε (S↝X ◅ _) = ⊥-elim (S↝̸ _ _ S↝X)
  ↝*-det _ S↝̸ (S↝X ◅ _) ε = ⊥-elim (S↝̸ _ _ S↝X)
  ↝*-det S₁↝̸ S₂↝̸ (S↝X ◅ X↝*S₁) (S↝Y ◅ Y↝*S₂)
    rewrite proj₂ (↝-det S↝X S↝Y) = ↝*-det S₁↝̸ S₂↝̸ (♭ X↝*S₁) (♭ Y↝*S₂)

  {-# NON_TERMINATING #-} -- Could be two infinite reductions
  ↝*-det' : ∀ { S S₁ S₂ x y }
    → S ~[ x ]↝* S₁ → S ~[ y ]↝* S₂ → ∃[ z ] (S₁ ~[ z ]↝* S₂ ⊎ S₂ ~[ z ]↝* S₁)
  ↝*-det' {x = []} {y} ε S↝*S₂ = _ , inj₁ S↝*S₂
  ↝*-det' {x = x ∷ xs} {[]} S↝*S₁@(_ ◅ _) ε = _ , inj₂ S↝*S₁
  ↝*-det' {x = x ∷ xs} {x₁ ∷ xs₁} (S↝X ◅ X↝*S₁) (S↝Y ◅ Y↝*S₂)
    rewrite proj₂ (↝-det S↝X S↝Y) = ↝*-det' (♭ X↝*S₁) (♭ Y↝*S₂)

  Colist-refl : ∀ {a} {A : Set a} → Reflexive (_≈_ {a} {A})
  Colist-refl = Setoid.refl (Colist.setoid _)

  Colist-sym : ∀ {a} {A : Set a} → Symmetric (_≈_ {a} {A})
  Colist-sym = Setoid.sym (Colist.setoid _)

  Colist-trans : ∀ {a} {A : Set a} → Transitive (_≈_ {a} {A})
  Colist-trans = Setoid.trans (Colist.setoid _)

  ≅ₛ-refl : Reflexive _≅ₛ_
  ≅ₛ-refl = [≈]-refl

  ≅ₛ-sym : Symmetric _≅ₛ_
  ≅ₛ-sym = [≈]-sym

  ≅ₛ-trans : Transitive _≅ₛ_
  ≅ₛ-trans = [≈]-trans

  ≅ₛ-equiv : IsEquivalence _≅ₛ_
  ≅ₛ-equiv = record { refl = ≅ₛ-refl ; sym = ≅ₛ-sym ; trans = ≅ₛ-trans }

  reduce-[] : ∀ { A } → labels A ≈ [] → Stuck A
  reduce-[] {A} r with reduce A
  reduce-[] {A} [] | [] = λ _ _ → ↝-Ω

  reduce-det : ∀ { A } (x y : Reduction _~[_]↝_ A) → labels-of x ≈ labels-of y
  reduce-det [] [] = []
  reduce-det [] (Ω↝Y ∷ _) = ⊥-elim (↝-Ω Ω↝Y)
  reduce-det (Ω↝X ∷ _) [] = ⊥-elim (↝-Ω Ω↝X)
  reduce-det (A↝X ∷ X↝) (A↝Y ∷ Y↝) with (↝-det A↝X A↝Y)
  ... | refl , refl = _ ∷ ♯ reduce-det (♭ X↝) (♭ Y↝)

  ↝⇒≅ₛ : ∀ { A B } → A ~[ τ ]↝ B → A ≅ₛ B
  ↝⇒≅ₛ {A} {B} A↝B with reduce A
  ... | [] = ⊥-elim (↝-Ω A↝B)
  ... | A↝C ∷ C↝
    with ↝-det A↝B A↝C
  ... | refl , refl = left ignore-τ (♯ [≈]-reflexive (reduce-det (♭ C↝) (reduce B)))

  ↝*⇒≅ₛ : ∀ { A B n } → A ~[ fromList (L.replicate n τ) ]↝* B → A ≅ₛ B
  ↝*⇒≅ₛ {n = ℕ.zero} ε = ≅ₛ-refl
  ↝*⇒≅ₛ {n = ℕ.suc n} (A↝Y ◅ Y↝*B) = ≅ₛ-trans (↝⇒≅ₛ A↝Y) (↝*⇒≅ₛ {n = n} (♭ Y↝*B))

  postulate cont-equiv : ∀ { a b c d E } → labels (𝒮 nop a E) [≈] labels (𝒮 nop c E) → (∀ E' → labels (𝒮 nop b E') [≈] labels (𝒮 nop d E')) → labels (𝒮 nop (a L.++ b) E) [≈] labels (𝒮 nop (c L.++ d) E)

  reduction-of : ∀ { A B e } → A ~[ e ]↝* B → Reduction _~[_]↝_ A
  reduction-of {A} ε = reduce A
  reduction-of (A↝X ◅ X↝*B) = A↝X ∷ ♯ reduction-of (♭ X↝*B)

  postulate ↝*-irr-cont : ∀ { x y k k' E e } → 𝒮 x k E ~[ e ]↝* 𝒮 y k E → 𝒮 x k' E ~[ e ]↝* 𝒮 y k' E
  postulate cont-comb : ∀ { s E E' e f k X } → 𝒮 s [] E ~[ e ]↝* 𝒮 nop [] E' → 𝒮 nop k E' ~[ f ]↝* X → 𝒮 s k E ~[ e ++ f ]↝* X
  postulate ≅ₛ-while-true : ∀ { s : Statement } { k k' E } → 𝒮 (while true then s) k E ≅ₛ 𝒮 (while true then s) k' E
  -- s ； ...
  -- nop ； ... or s' ； ...
