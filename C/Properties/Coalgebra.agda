open import Algebra.FunctionProperties
open import Codata.Thunk
open import Data.Empty
open import Data.Maybe
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.List using (List)
open import Function using (id ; _∘_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Size

import Codata.Colist as Colist
import Codata.Colist.Bisimilarity as CoB
import Data.Bool as 𝔹
import Data.Nat as ℕ
import Data.Integer as ℤ
import Data.Integer.DivMod as ℤ÷
import Level

open import C.Base
open import C.Properties.State
open C ⦃ ... ⦄

module C.Properties.Coalgebra ⦃ _ : C ⦄ where

-- Coinductive Verification of ProgramOptimizations Using Similarity Relations by Glesner et al.
--
-- We define the functor Reduction(X) = 1 + (SideEffect × X) and the Reduction-coalgebra [ stop , ⟨ effects , next ⟩ ] : X → 1 + (SideEffect × X), where SideEffect is the set of possible side-effects and State is the set of all states.

data SideEffect : Set where
  _↦_ : ∀ { α } → Ref α → ⟦ α ⟧ → SideEffect
  emit : ⟦ Int ⟧ → SideEffect

data Reduction (i : Size) : Set where
  stop : Reduction i
  continue : SideEffect → Thunk Reduction i → Reduction i

-- For polynomial functors, unique final coalgebras exist and hence coinduction can rely on the fact that homomorphisms from arbitrary coalgebras into the final coalgebra exist. The proof principle of coinduction can then use the uniqueness of the final coalgebra.
--
-- The Reduction-coalgebra is homomorphic to the coalgebra of infinite list of elements of set A, defined by coalgebra [ empty , ⟨ head , tail ⟩ ] : A∞ → 1 + (A × A∞), where A∞ is the final coalgrebra of the functor T(X) = 1 + A × X. The homomorphism is defined by the function ψ : X → SideEffect∞.

ψ : ∀ { i } → Reduction i → Colist.Colist SideEffect i
ψ stop = Colist.[]
ψ (continue e r) = e Colist.∷ (λ where .force → ψ (Thunk.force r))

-- The homomorphism is illustrated by the diagram below:
--            X --------------[ ψ ]----------> SideEffect∞
--            |                                    |
--            |                                    |
-- [ stop , ⟨ effects , next ⟩ ]        [ empty , ⟨ head , tail ⟩ ]
--            |                                    |
--            v                                    v
--     1 + (SideEffect × X) --[ ψ ]--> 1 + SideEffect × SideEffect∞

[stop,⟨effects,next⟩] : ∀ { i } { j : Size< i } → Reduction i → ⊤ ⊎ (SideEffect × Reduction j)
[stop,⟨effects,next⟩] stop = inj₁ tt
[stop,⟨effects,next⟩] (continue e l) = inj₂ (e , Thunk.force l)

[empty,⟨head,tail⟩] : ∀ { i } { j : Size< i }
  → Colist.Colist SideEffect i → ⊤ ⊎ (SideEffect × Colist.Colist SideEffect j)
[empty,⟨head,tail⟩] Colist.[] = inj₁ tt
[empty,⟨head,tail⟩] (h Colist.∷ t) = inj₂ (h , Thunk.force t)

homomorphic : ∀ { i } { j : Size< i } (r : Reduction i)
  → (Data.Sum.[ inj₁ , inj₂ ∘ Data.Product.map id ψ ] ([stop,⟨effects,next⟩] {j = j} r))
    ≡ ([empty,⟨head,tail⟩] {j = j} (ψ r))
homomorphic stop = refl
homomorphic (continue _ _) = refl

-- Given our Reduction-coalgebra definition above, we define the bisimulation ~, closed under the operations of the coalgebra, on the coalgebraic type. This means that given (inj₂ (a , A')) ~ (inj₂ (b, B'), we can conclude that a ≡ b and A' ~ B'.

Bisimulation : ∀ { r } → (SideEffect → SideEffect → Set r) → Size → Reduction ∞ → Reduction ∞ → Set r
Bisimulation f i a b = CoB.Bisim f i (ψ a) (ψ b)

corec : ∀ { a i } { A : Set a } → A → (A → Maybe (A × SideEffect)) → Reduction i
corec x f with f x
... | nothing = stop
... | just (x' , b) = continue b (λ where .force → corec x' f)
    
-- Formal operational semantics of imperative programming languages often define a small-step reduction semantics which give a sequence of states reached during the run of a program. Therefore, programs can be considered as elements of coalgebras, that take a state as input and output a new state together with the transitions side-effects.

data MaybeSideEffect : Set where
  τ : MaybeSideEffect
  _↦_ : ∀ { α } → Ref α → ⟦ α ⟧ → MaybeSideEffect
  emit : ⟦ Int ⟧ → MaybeSideEffect

data MaybeSideEffects : Set where
  τ : MaybeSideEffects
  _∷_ : SideEffect → MaybeSideEffects → MaybeSideEffects

_+̂_ : MaybeSideEffect → MaybeSideEffects → MaybeSideEffects
τ +̂ t = t
(x ↦ v) +̂ t = (x ↦ v) ∷ t
emit v +̂ t = emit v ∷ t

_++_ : MaybeSideEffects → MaybeSideEffects → MaybeSideEffects
τ ++ b = b
(x ∷ a) ++ b = x ∷ (a ++ b)

+-++-assoc : ∀ (a b c) → (a +̂ b) ++ c ≡ a +̂ (b ++ c)
+-++-assoc τ _ _ = refl
+-++-assoc (_ ↦ _) b c = refl
+-++-assoc (emit _) b c = refl

Reducer : Set
Reducer = ∀ { i } → State → Reduction i

_⊢_~[_]↝_ : Reducer → State → MaybeSideEffect → State → Set
reduce ⊢ A ~[ τ ]↝ B = ∀ { i } → Bisimulation _≡_ i (reduce A) (reduce B)
reduce ⊢ A ~[ x ↦ v ]↝ B = ∀ { i } → Bisimulation _≡_ i (reduce A) (continue (x ↦ v) λ { .force → reduce B })
reduce ⊢ A ~[ emit v ]↝ B = ∀ { i } → Bisimulation _≡_ i (reduce A) (continue (emit v) λ { .force → reduce B })

Congruence : ∀ { a l } { A : Set a } → Rel A l → Set _
Congruence {A = A} _~_ = ∀ (f : A → A) x y → x ~ y → (f x) ~ (f y)

data _⊢_~[_]↝⁺_ (reduce : Reducer) : State → MaybeSideEffects → State → Set where
  [_] : ∀ { x y e } (x~y : reduce ⊢ x ~[ e ]↝ y) → reduce ⊢ x ~[ e +̂ τ ]↝⁺ y
  _∷_ : ∀ { x y z e f } (x~y : reduce ⊢ x ~[ e ]↝ y) (y∼⁺z : reduce ⊢ y ~[ f ]↝⁺ z)
    → reduce ⊢ x ~[ e +̂ f ]↝⁺ z

data _⊢_~[_]↝*_ (reduce : Reducer) : State → MaybeSideEffects → State → Set where
  ε : ∀ { s } → reduce ⊢ s ~[ τ ]↝* s
  _◅_ : ∀ { i j k e es } (x : reduce ⊢ i ~[ e ]↝ j) (xs : reduce ⊢ j ~[ es ]↝* k)
    → reduce ⊢ i ~[ e +̂ es ]↝* k

_◅◅_ : ∀ { reduce : Reducer } { i j k e f }
  → reduce ⊢ i ~[ e ]↝* j → reduce ⊢ j ~[ f ]↝* k → reduce ⊢ i ~[ e ++ f ]↝* k
ε ◅◅ b = b
_◅◅_ {f = f} (_◅_ {e = e} {es} x a) b rewrite +-++-assoc e es f = x ◅ (a ◅◅ b) 

record Semantics : Set₁ where
  field
    evaluate : ∀ { α } → Env → Expr α → ⟦ α ⟧
    reduce : ∀ { i } → State → Reduction i

  _⊢_⇒_ : ∀ { α } → Env → Expr α → ⟦ α ⟧ → Set
  _⊢_⇒_ E e v = evaluate E e ≡ v

  _~[_]↝_ : State → MaybeSideEffect → State → Set
  _~[_]↝_ = reduce ⊢_~[_]↝_
  
  _~[_]↝⁺_ : State → MaybeSideEffects → State → Set
  _~[_]↝⁺_ = reduce ⊢_~[_]↝⁺_
  
  _~[_]↝*_ : State → MaybeSideEffects → State → Set
  _~[_]↝*_ = reduce ⊢_~[_]↝*_
  
  field
    ⊢-total : ∀ { α E } { e : Expr α } → ∃[ v ] (E ⊢ e ⇒ v)
    ⊢-det : ∀ { α E } { e : Expr α } { v w : ⟦ α ⟧ } → E ⊢ e ⇒ v → E ⊢ e ⇒ w → v ≡ w 
    ⊢-weakening : ∀ { E E' α β } { e : Expr α } { v : ⟦ α ⟧ } { x : Ref β } { w : ⟦ β ⟧ }
      → { _ : x ∉nv E × x ∉nv E' }
      → (E ⊕ E') ⊢ e ⇒ v → (E ⊕ (x Env.↦ w , ε) ⊕ E') ⊢ e ⇒ v
    ⊢-exchange : ∀ { E E' α β γ } { x : Ref α } { y : Ref β }
      → { v : ⟦ α ⟧ } { w : ⟦ β ⟧ } { e : Expr γ } { ev : ⟦ γ ⟧ }
      → (E ⊕ (x Env.↦ v , (y Env.↦ w , ε)) ⊕ E') ⊢ e ⇒ ev
      → (E ⊕ (y Env.↦ w , (x Env.↦ v , ε)) ⊕ E') ⊢ e ⇒ ev
    -- TODO: variants on Env constructor
    nat : ∀ { E } n → E ⊢ ⟨ n ⟩ ⇒ n
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
      → E ⊢ e ⇒ v → 𝒮 (id ≔ e) k E ~[ τ ]↝ 𝒮 nop k (id Env.↦ v , E)
    ↝-seq : ∀ { E k } { s₁ s₂ : Statement }
      → 𝒮 (s₁ ； s₂) k E ~[ τ ]↝ 𝒮 s₁ (s₂ then k) E
    ↝-decl : ∀ { E k α } { f : Ref α → Statement }
      → ∃ λ (x : Ref α) → (x ∉nv E) × (𝒮 (decl α f) k E ~[ τ ]↝ 𝒮 (f x) k (x , E))
    ↝-nop : ∀ { E k } { s : Statement } → 𝒮 nop (s then k) E ~[ τ ]↝ 𝒮 s k E
    ↝-stuck : ∀ { E } → ¬ ∃[ S' ] (𝒮 nop stop E ~[ τ ]↝ S')
    ↝-for : ∀ { E k } { l u : Expr Int } { f : Ref Int → Statement } { x : Ref Int }
      → 𝒮 (for l to u then f) k E
        ~[ τ ]↝ 𝒮 (if (l < u) then (
                (decl Int λ i → i ≔ l ； f i) ；
                for (l + ⟨ ℤ.+ 1 ⟩) to u then f)
             else nop) k E
    ↝-while : ∀ { E k } { e : Expr Bool } { s : Statement }
      → 𝒮 (while e then s) k E ~[ τ ]↝ 𝒮 (if e then (s ； while e then s) else nop) k E
    ↝-putchar : ∀ { E k } { e : Expr Int } { v : ℤ.ℤ }
      → E ⊢ e ⇒ v → 𝒮 (putchar e) k E ~[ emit v ]↝ 𝒮 nop k E
    ↝-det : ∀ { S S₁ S₂ e f } → S ~[ e ]↝ S₁ → S ~[ f ]↝ S₂ → S₁ ≡ S₂
    ↝-progress : ∀ (x k E) → (x ≡ nop × k ≡ stop) ⊎ (∃[ S' ] (𝒮 x k E ~[ τ ]↝ S'))

  infix 0 _≅ₑ_
  _≅ₑ_ : ∀ { α } → Rel (Expr α) Level.zero
  _≅ₑ_ { α } x y = ∀ { E : Env } { v w : ⟦ α ⟧ }
    → (E ⊢ x ⇒ v) → (E ⊢ y ⇒ w) → (v ≡ w)

  Stuck : State → Set
  Stuck S = ∀ S' e → ¬ (S ~[ e ]↝ S')

  Terminating : State → Set
  Terminating S = ∃[ S' ] ∃[ es ] (S ~[ es ]↝* S' × Stuck S')

  infix 0 _≅ₛ_
  _≅ₛ_ : Rel State Level.zero
  X ≅ₛ Y = ∀ { i } → Bisimulation _≡_ i (reduce X) (reduce Y)

  field
    ≅ₛ-subst :
      ∀ { α E₁ E₂ k } { v w : ⟦ α ⟧ } { f : Expr α → Statement } { e₁ e₂ : Expr α }
      → E₁ ⊢ e₁ ⇒ v → E₂ ⊢ e₂ ⇒ w → v ≡ w
      → 𝒮 (f e₁) k E₁ ≅ₛ 𝒮 (f e₂) k E₂
    ≅ₛ-decl : ∀ { α f k E } → 𝒮 (decl α λ x → f) k E ≅ₛ 𝒮 f k E
    ≅ₛ-cong : Congruence _≅ₛ_


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

  ↝*-trans : ∀ { e f } → Trans _~[ e ]↝*_ _~[ f ]↝*_ _~[ e ++ f ]↝*_
  ↝*-trans = _◅◅_

  ↝*-to-↝⁺ : ∀ { A B C e es } → A ~[ e ]↝ B → B ~[ es ]↝* C → A ~[ e +̂ es ]↝⁺ C
  ↝*-to-↝⁺ A↝B ε = [ A↝B ]
  ↝*-to-↝⁺ A↝B (B↝X ◅ X↝*C) = A↝B ∷ (↝*-to-↝⁺ B↝X X↝*C)

  ↝⁺-to-↝* : ∀ { A B es } → A ~[ es ]↝⁺ B → A ~[ es ]↝* B
  ↝⁺-to-↝* ([ A↝B ]) = A↝B ◅ ε
  ↝⁺-to-↝* (A↝X ∷ X↝⁺B) = A↝X ◅ (↝⁺-to-↝* X↝⁺B)

  ↝̸-transᵇ : ∀ { S S' : State } { e }
    → S ~[ e ]↝* S' → Terminating S' → Terminating S
  ↝̸-transᵇ {S} {S'} S↝*S' (X , e , S'↝*X , X↝̸) = X , _ , (S↝*S' ◅◅ S'↝*X) , X↝̸

  ↝̸-transᶠ : ∀ { S S' : State } { e }
    → S ~[ e ]↝* S' → Terminating S → Terminating S'
  ↝̸-transᶠ ε S↝̸ = S↝̸
  ↝̸-transᶠ (S↝X ◅ X↝*S') (S , _ , ε , S↝̸) = ⊥-elim (S↝̸ _ _ S↝X)
  ↝̸-transᶠ (S↝A ◅ A↝*S') (X , e , S↝Y ◅ Y↝*X , X↝̸)
    with ↝-det S↝A S↝Y
  ... | refl = ↝̸-transᶠ A↝*S' (X , _ , Y↝*X , X↝̸)

  ↝ω-transᵇ : ∀ { X Y : State } { e }
    → X ~[ e ]↝* Y → ¬ Terminating Y → ¬ Terminating X
  ↝ω-transᵇ {X} {Y} X↝*Y Y↝ω X↝̸ = Y↝ω (↝̸-transᶠ X↝*Y X↝̸)

  ↝ω-transᶠ : ∀ { X Y : State } { e }
    → X ~[ e ]↝* Y → ¬ Terminating X → ¬ Terminating Y
  ↝ω-transᶠ {X} {Y} X↝*Y X↝ω Y↝̸ = X↝ω (↝̸-transᵇ X↝*Y Y↝̸)

  ↝*-det : ∀ { S S₁ S₂ x y }
    → Stuck S₁ → Stuck S₂ → S ~[ x ]↝* S₁ → S ~[ y ]↝* S₂ → S₁ ≡ S₂
  ↝*-det S₁↝̸ S₂↝̸ ε ε = refl
  ↝*-det S↝̸ S₂↝̸ ε (_◅_ {j = X} S↝X X↝*S₂) = ⊥-elim (S↝̸ X _ S↝X)
  ↝*-det S₁↝̸ S↝̸ (_◅_ {j = X} S↝X X↝*S₂) ε = ⊥-elim (S↝̸ X _ S↝X)
  ↝*-det S₁↝̸ S₂↝̸ (S↝X ◅ X↝*S₁) (S↝Y ◅ Y↝*S₂)
    rewrite ↝-det S↝X S↝Y = ↝*-det S₁↝̸ S₂↝̸ X↝*S₁ Y↝*S₂

  ↝*-det' : ∀ { S S₁ S₂ x y }
    → S ~[ x ]↝* S₁ → S ~[ y ]↝* S₂ → ∃[ z ] (S₁ ~[ z ]↝* S₂ ⊎ S₂ ~[ z ]↝* S₁)
  ↝*-det' ε S↝*S₂ = _ , inj₁ S↝*S₂
  ↝*-det' S↝*S₁@(S↝X ◅ X↝*S₁) ε = _ , inj₂ S↝*S₁
  ↝*-det' (S↝X ◅ X↝*S₁) (S↝Y ◅ Y↝*S₂)
    rewrite ↝-det S↝X S↝Y = ↝*-det' X↝*S₁ Y↝*S₂

  ≅ₛ-refl : Reflexive _≅ₛ_
  ≅ₛ-refl = CoB.reflexive refl
  
  ≅ₛ-sym : Symmetric _≅ₛ_
  ≅ₛ-sym x = CoB.symmetric sym x

  ≅ₛ-trans : Transitive _≅ₛ_
  ≅ₛ-trans p q = CoB.transitive trans p q
  
  ≅ₛ-equiv : IsEquivalence _≅ₛ_
  ≅ₛ-equiv = record { refl = ≅ₛ-refl ; sym = ≅ₛ-sym ; trans = ≅ₛ-trans }
