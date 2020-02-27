-- Based in-part on "A formally verified compiler back-end" by Xavier Leroy

open import C

open import Algebra.FunctionProperties
open import C.Properties.State
open import Data.Bool as 𝔹 using () renaming (Bool to 𝔹)
open import Data.Empty
open import Data.Integer as ℤ using (ℤ ; +_)
open import Data.Product using (Σ ; ∃ ; ∃-syntax ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum
open import Data.Unit
open import Data.Vec using (Vec ; [] ; _∷_)
open import Data.List using (List) renaming (_∷_ to _∷ₗ_ ; _++_ to _++ₗ_)
open import Data.List.Properties
open import Function
open import Level using (0ℓ)
open import Relation.Binary
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.Construct.Closure.Transitive hiding (_++_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable

import Data.Integer.DivMod as ℤ÷
import Data.Integer.Properties as ℤₚ
import Data.Nat as ℕ
import Data.Nat.Properties as ℕₚ

open C.C ⦃ ... ⦄
open ≡-Reasoning

module C.Properties.ReductionSemantics ⦃ _ : C ⦄ where

Congruence : ∀ { a l } { A : Set a } → Rel A l → Set _
Congruence {A = A} _~_ = ∀ (f : A → A) x y → x ~ y → (f x) ~ (f y)

-- SEMANTIC EQUIVALENCE
-- Two states are equivalent if: they are identical; they transition to two states that are equivalent; or they produce the same side-effects.

syntax SemEquiv R X Y = X ≅[ R ] Y
data SemEquiv (R : Rel State Level.zero) : Rel State Level.zero

record SameEffects (R : Rel State Level.zero) (s₁ s₂ s₃ s₄ : Statement) (k₁ k₂ k₃ k₄ E₁ E₂ E₃ E₄) (f e : SideEffects) : Set where
  coinductive
  X = 𝒮 s₁ k₁ E₁ e
  X' = 𝒮 s₂ k₂ E₂ (f ++ₗ e)
  Y = 𝒮 s₃ k₃ E₃ e
  Y' = 𝒮 s₄ k₄ E₄ (f ++ₗ e)
  field
    left : Star R X X'
    right : Star R Y Y'
    eq : X' ≅[ R ] Y'
    
data SemEquiv R where
  sem-refl : ∀ { X } → X ≅[ R ] X
  sem-converge : ∀ { X Y }
    → ∃[ A ] (∃[ B ] (Star R X A × Star R Y B × A ≅[ R ] B)) → X ≅[ R ] Y
  sem-loop : ∀ { s₁ s₂ s₃ s₄ : Statement } { k₁ k₂ k₃ k₄ E₁ E₂ E₃ E₄ } { f e : SideEffects }
    → SameEffects R s₁ s₂ s₃ s₄ k₁ k₂ k₃ k₄ E₁ E₂ E₃ E₄ f e
    → 𝒮 s₁ k₁ E₁ e ≅[ R ] 𝒮 s₃ k₃ E₃ e

record Semantics : Set₁ where
  field
    _⊢_⇒_ : ∀ { α } → ∀ { v : ⟦ α ⟧ } → Env → Expr α → Value α v → Set
    ⊢-total : ∀ { α E } { e : Expr α } → ∃[ v ] (E ⊢ e ⇒ val v)
    ⊢-det : ∀ { α E } { e : Expr α } { v w : ⟦ α ⟧ } → E ⊢ e ⇒ val v → E ⊢ e ⇒ val w → v ≡ w 
    ⊢-weakening : ∀ { E E' α β } { e : Expr α } { v : ⟦ α ⟧ } { x : Ref β } { w : ⟦ β ⟧ }
      → { _ : x ∉nv E × x ∉nv E' }
      → (E ⊕ E') ⊢ e ⇒ val v → (E ⊕ (x ↦ val w , ε) ⊕ E') ⊢ e ⇒ val v
    ⊢-exchange : ∀ { E E' α β γ } { x : Ref α } { y : Ref β }
      → { v : ⟦ α ⟧ } { w : ⟦ β ⟧ } { e : Expr γ } { ev : ⟦ γ ⟧ }
      → (E ⊕ (x ↦ val v , (y ↦ val w , ε)) ⊕ E') ⊢ e ⇒ val ev
      → (E ⊕ (y ↦ val w , (x ↦ val v , ε)) ⊕ E') ⊢ e ⇒ val ev
    -- TODO: variants on Env constructor
    nat : ∀ { E } n → E ⊢ ⟨ n ⟩ ⇒ val n
    deref : ∀ { E α } { x : Ref α } { v : ⟦ α ⟧ }
      → x ↦ val v ∈nv E → (E ⊢ (★ x) ⇒ val v)
    +-eval : ∀ { E x y x' y' }
      → E ⊢ x ⇒ val x' → E ⊢ y ⇒ val y'
      → E ⊢ x + y ⇒ val (x' ℤ.+ y')
    *-eval : ∀ { E x y x' y' }
      → E ⊢ x ⇒ val x' → E ⊢ y ⇒ val y'
      → E ⊢ x * y ⇒ val (x' ℤ.* y')
    ∸-eval : ∀ { E x y x' y' }
      → E ⊢ x ⇒ val x' → E ⊢ y ⇒ val y'
      → E ⊢ x - y ⇒ val (x' ℤ.- y')
    /-eval : ∀ { E x y x' y' }
      → E ⊢ x ⇒ val x' → E ⊢ y ⇒ val y' → (y≠0 : False (ℤ.∣ y' ∣ ℕ.≟ 0))
      → E ⊢ x / y ⇒ val ((x' ℤ÷.div y') {y≠0})
    true-eval : ∀ { E } → E ⊢ true ⇒ val 𝔹.true
    false-eval : ∀ { E } → E ⊢ false ⇒ val 𝔹.false
    ||-eval : ∀ { E x y x' y' }
      → E ⊢ x ⇒ val x' → E ⊢ y ⇒ val y' → E ⊢ x || y ⇒ val (x' 𝔹.∨ y')
    &&-eval : ∀ { E x y x' y' }
      → E ⊢ x ⇒ val x' → E ⊢ y ⇒ val y' → E ⊢ x && y ⇒ val (x' 𝔹.∧ y')
    ⁇-eval-t : ∀ { E c α } { x y : Expr α } { x' }
      → E ⊢ c ⇒ val 𝔹.true → E ⊢ x ⇒ val x' → E ⊢ c ⁇ x ∷ y ⇒ val x'
    ⁇-eval-f : ∀ { E c α } { x y : Expr α } { y' }
      → E ⊢ c ⇒ val 𝔹.false → E ⊢ y ⇒ val y' → E ⊢ c ⁇ x ∷ y ⇒ val y'

    _↝_ : Rel State 0ℓ
    ↝-if-true : ∀ { E k e } { cond : Expr Bool } { s₁ s₂ : Statement }
      → E ⊢ cond ⇒ val 𝔹.true → 𝒮 (if cond then s₁ else s₂) k E e ↝ 𝒮 s₁ k E e
    ↝-if-false : ∀ { E k e } { cond : Expr Bool } { s₁ s₂ : Statement }
      → E ⊢ cond ⇒ val 𝔹.false → 𝒮 (if cond then s₁ else s₂) k E e ↝ 𝒮 s₂ k E e
    ↝-assignment : ∀ { E k α ef } { id : Ref α } { e : Expr α } { v : ⟦ α ⟧ }
      → E ⊢ e ⇒ val v → 𝒮 (id ≔ e) k E ef ↝ 𝒮 nop k (id ↦ val v , E) ef
    ↝-seq : ∀ { E k e } { s₁ s₂ : Statement }
      → 𝒮 (s₁ ； s₂) k E e ↝ 𝒮 s₁ (s₂ then k) E e
    ↝-decl : ∀ { E k e α } { f : Ref α → Statement }
      → ∃ λ (x : Ref α) → (x ∉nv E) × (𝒮 (decl α f) k E e ↝ 𝒮 (f x) k (x , E) e)
    ↝-nop : ∀ { E k e } { s : Statement } → 𝒮 nop (s then k) E e ↝ 𝒮 s k E e
    ↝-for : ∀ { E k e } { l u : Expr Int } { f : Ref Int → Statement } { x : Ref Int }
      → 𝒮 (for l to u then f) k E e
        ↝ 𝒮 (if (l < u) then (
                (decl Int λ i → i ≔ l ； f i) ；
                for (l + ⟨ + 1 ⟩) to u then f)
             else nop) k E e
    ↝-while : ∀ { E k ef } { e : Expr Bool } { s : Statement }
      → 𝒮 (while e then s) k E ef ↝ 𝒮 (if e then (s ； while e then s) else nop) k E ef
    ↝-putchar : ∀ { E k ef } { e : Expr Int } { v : ℤ }
      → E ⊢ e ⇒ val v → 𝒮 (putchar e) k E ef ↝ 𝒮 nop k E (v ∷ₗ ef)
    ↝-det : ∀ { S S₁ S₂ } → S ↝ S₁ → S ↝ S₂ → S₁ ≡ S₂

  infix 0 _≅ₑ_
  _≅ₑ_ : ∀ { α } → Rel (Expr α) 0ℓ
  _≅ₑ_ { α } x y = ∀ { E : Env } { v w : ⟦ α ⟧ }
    → (E ⊢ x ⇒ val v) → (E ⊢ y ⇒ val w) → (v ≡ w)

  _↝⁺_ : State → State → Set
  _↝⁺_ S₁ S₂ = S₁ ⟨ _↝_ ⟩⁺ S₂

  _↝*_ : State → State → Set
  _↝*_ = Star _↝_

  Stuck : State → Set
  Stuck S = ∀ S' → ¬ (S ↝ S')

  Terminating : State → Set
  Terminating S = ∃ λ S' → S ↝* S' × Stuck S'

  infix 0 _≅ₛ_
  _≅ₛ_ : Rel State 0ℓ
  X ≅ₛ Y = X ≅[ _↝_ ] Y

  field
    ≅ₛ-subst :
      ∀ { α E₁ E₂ k ef } { v w : ⟦ α ⟧ } { f : Expr α → Statement } { e₁ e₂ : Expr α }
      → E₁ ⊢ e₁ ⇒ val v → E₂ ⊢ e₂ ⇒ val w → v ≡ w
      → 𝒮 (f e₁) k E₁ ef ≅ₛ 𝒮 (f e₂) k E₂ ef
    ≅ₛ-decl : ∀ { α f k E e } → 𝒮 (decl α λ x → f) k E e ≅ₛ 𝒮 f k E e
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

  ↝*-trans : Transitive _↝*_
  ↝*-trans = _◅◅_

  ↝*-to-↝⁺ : ∀ { A B C } → A ↝ B → B ↝* C → A ↝⁺ C
  ↝*-to-↝⁺ A↝B ε = Plus′.[ A↝B ]
  ↝*-to-↝⁺ A↝B (B↝X ◅ X↝*C) = A↝B ∷ (↝*-to-↝⁺ B↝X X↝*C)

  ↝⁺-to-↝* : ∀ { A B } → A ↝⁺ B → A ↝* B
  ↝⁺-to-↝* Plus′.[ A↝B ] = A↝B ◅ ε
  ↝⁺-to-↝* (A↝X ∷ X↝⁺B) = A↝X ◅ (↝⁺-to-↝* X↝⁺B)

  ↝̸-transᵇ : ∀ { S S' : State }
    → S ↝* S' → Terminating S' → Terminating S
  ↝̸-transᵇ {S} {S'} S↝*S' (X , S'↝*X , X↝̸) = X , (S↝*S' ◅◅ S'↝*X) , X↝̸

  ↝̸-transᶠ : ∀ { S S' : State }
    → S ↝* S' → Terminating S → Terminating S'
  ↝̸-transᶠ ε S↝̸ = S↝̸
  ↝̸-transᶠ (S↝X ◅ X↝*S') (S , ε , S↝̸) = ⊥-elim (S↝̸ _ S↝X)
  ↝̸-transᶠ (S↝A ◅ A↝*S') (X , S↝Y ◅ Y↝*X , X↝̸)
    with ↝-det S↝A S↝Y
  ... | refl = ↝̸-transᶠ A↝*S' (X , Y↝*X , X↝̸)

  ↝ω-transᵇ : ∀ { X Y : State }
    → X ↝* Y → ¬ Terminating Y → ¬ Terminating X
  ↝ω-transᵇ {X} {Y} X↝*Y Y↝ω X↝̸ = Y↝ω (↝̸-transᶠ X↝*Y X↝̸)

  ↝ω-transᶠ : ∀ { X Y : State }
    → X ↝* Y → ¬ Terminating X → ¬ Terminating Y
  ↝ω-transᶠ {X} {Y} X↝*Y X↝ω Y↝̸ = X↝ω (↝̸-transᵇ X↝*Y Y↝̸)

  ↝*-det : ∀ { S S₁ S₂ }
    → Stuck S₁ → Stuck S₂ → S ↝* S₁ → S ↝* S₂ → S₁ ≡ S₂
  ↝*-det S₁↝̸ S₂↝̸ ε ε = refl
  ↝*-det S↝̸ S₂↝̸ ε (_◅_ {j = X} S↝X X↝*S₂) = ⊥-elim (S↝̸ X S↝X)
  ↝*-det S₁↝̸ S↝̸ (_◅_ {j = X} S↝X X↝*S₂) ε = ⊥-elim (S↝̸ X S↝X)
  ↝*-det S₁↝̸ S₂↝̸ (S↝X ◅ X↝*S₁) (S↝Y ◅ Y↝*S₂)
    rewrite ↝-det S↝X S↝Y = ↝*-det S₁↝̸ S₂↝̸ X↝*S₁ Y↝*S₂

  ↝*-det' : ∀ { S S₁ S₂ }
    → S ↝* S₁ → S ↝* S₂ → S₁ ↝* S₂ ⊎ S₂ ↝* S₁
  ↝*-det' ε S↝*S₂ = inj₁ S↝*S₂
  ↝*-det' S↝*S₁@(S↝X ◅ X↝*S₁) ε = inj₂ S↝*S₁
  ↝*-det' (S↝X ◅ X↝*S₁) (S↝Y ◅ Y↝*S₂)
    rewrite ↝-det S↝X S↝Y = ↝*-det' X↝*S₁ Y↝*S₂

  ≅ₛ-refl : Reflexive _≅ₛ_
  ≅ₛ-refl {x} = sem-refl

  ≅ₛ-sym : Symmetric _≅ₛ_
  ≅ₛ-sym sem-refl = sem-refl
  ≅ₛ-sym (sem-converge (A , B , i↝*A , j↝*B , A≅B)) =
    sem-converge (B , A , j↝*B , i↝*A , ≅ₛ-sym A≅B)
  ≅ₛ-sym (sem-loop w) = sem-loop x
    where
      x : SameEffects _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      SameEffects.left x = {!!}
      SameEffects.right x = {!!}
      SameEffects.eq x = {!!}

  ↝*⇒≅ₛ : ∀ { A B } → A ↝* B → A ≅ₛ B
  ↝*⇒≅ₛ A↝*B = sem-converge (_ , _ , A↝*B , ε , sem-refl)

  ↝*-pair⇒≅ₛ : ∀ { A B C } → A ↝* B → A ↝* C → B ≅ₛ C
  ↝*-pair⇒≅ₛ ε A↝*C = ↝*⇒≅ₛ A↝*C
  ↝*-pair⇒≅ₛ A↝*B@(_ ◅ _) ε = ≅ₛ-sym (↝*⇒≅ₛ A↝*B)
  ↝*-pair⇒≅ₛ (A↝X ◅ X↝*B) (A↝Y ◅ Y↝*C) rewrite ↝-det A↝X A↝Y = ↝*-pair⇒≅ₛ X↝*B Y↝*C

  normalise : ∀ { X Y } → X ≅ₛ Y → X ≅ₛ Y
  normalise sem-refl = sem-refl
  normalise (sem-converge (A , B , i↝*A , j↝*B , A≅B))
    with normalise A≅B
  ... | sem-refl = sem-converge (A , B , i↝*A , j↝*B , sem-refl)
  ... | sem-converge (C , D , A↝*C , B↝*D , C≅D) = sem-converge (C , D , i↝*A ◅◅ A↝*C , j↝*B ◅◅ B↝*D , C≅D)
  ... | p@(sem-loop _) = sem-converge (A , B , i↝*A , j↝*B , p)
  normalise (sem-loop w) = {!!}
  --   with normalise X'≅Y'
  -- ... | sem-refl = sem-loop X↝*X' Y↝*Y' sem-refl
  -- ... | p@(sem-converge _) = sem-loop X↝*X' Y↝*Y' p
  -- ... | sem-loop {f = f'} X'↝*X'' Y'↝*Y'' X''≅Y'' rewrite sym (++-assoc f' f e)
  --       = sem-loop (X↝*X' ◅◅ X'↝*X'') (Y↝*Y' ◅◅ Y'↝*Y'') X''≅Y''

  ≅ₛ-trans : Transitive _≅ₛ_
  ≅ₛ-trans sem-refl q = q
  ≅ₛ-trans p@(sem-converge _) sem-refl = p
  ≅ₛ-trans (sem-converge (A , B , i↝*A , ε , A≅B)) (sem-converge (C , D , B↝*C , k↝*D , C≅D)) =
    sem-converge (_ , _ , i↝*A , k↝*D , ≅ₛ-trans A≅B (sem-converge (_ , _ , B↝*C , ε , C≅D)))
  ≅ₛ-trans (sem-converge (A , B , i↝*A , j↝X ◅ X↝*B , A≅B)) (sem-converge (C , D , ε , k↝*D , C≅D)) =
    ≅ₛ-trans
      (sem-converge (A , B , i↝*A , X↝*B , A≅B))
      (sem-converge (_ , _ , ε , k↝*D , ≅ₛ-trans (sem-converge (_ , _ , ε , j↝X ◅ ε , sem-refl)) C≅D))
  ≅ₛ-trans (sem-converge (A , B , i↝*A , j↝*B@(_ ◅ _) , A≅B)) (sem-converge (C , D , x ◅ j↝*C , k↝*D , C≅D)) = {!!}
  ≅ₛ-trans (sem-converge x) (sem-loop w) = {!!}
  ≅ₛ-trans (sem-loop w) q = {!!}
  
  ≅ₛ-equiv : IsEquivalence _≅ₛ_
  ≅ₛ-equiv = record { refl = ≅ₛ-refl ; sym = ≅ₛ-sym ; trans = ≅ₛ-trans }
