-- Based in-part on "A formally verified compiler back-end" by Xavier Leroy

open import C
open import Function
open import Relation.Binary
open import Relation.Nullary.Decidable
open import Level using (0ℓ)
open import Data.Product using (Σ ; ∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Algebra.FunctionProperties
open import Data.Unit
open import Data.Empty
open import Data.Sum
open import Data.Integer as ℤ using (ℤ ; +_)
import Data.Integer.DivMod as ℤ÷
import Data.Integer.Properties as ℤₚ
import Data.Nat as ℕ
import Data.Nat.Properties as ℕₚ
open import Relation.Nullary
open import Data.Bool as 𝔹 using () renaming (Bool to 𝔹)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Construct.Closure.Transitive
  hiding (_++_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Data.Vec using (Vec ; [] ; _∷_)
open import C.Properties.FreeVariables as FV

open C.C ⦃ ... ⦄
open FV.FreeVariables ⦃ ... ⦄

module C.Properties.ReductionSemantics
  ⦃ _ : C ⦄
  { _⊑_ : Rel (∃ λ β → Ref β) Level.zero }
  { isStrictTotalOrder : IsStrictTotalOrder _≡_ _⊑_ }
  ⦃ _ : FV.FreeVariables isStrictTotalOrder ⦄ where

⟦_⟧ : c_type → Set
⟦ Int ⟧ = ℤ
⟦ Bool ⟧ = 𝔹
⟦ Array α n ⟧ = Vec ⟦ α ⟧ n

data Value : (α : c_type) → ⟦ α ⟧ → Set where
  val : ∀ { α } → (v : ⟦ α ⟧) → Value α v

data Env : Set where
  _↦_,_ : ∀ { α } → ∀ { v : ⟦ α ⟧ } → Ref α → Value α v → Env → Env
  _,_ : ∀ { α } → Ref α → Env → Env
  ε : Env

data _∈nv_ : ∀ { α } → Ref α → Env → Set where
  x∈x↦v,E : ∀ { α } { v : ⟦ α ⟧ } {x : Ref α} {E : Env}
    → x ∈nv (x ↦ val v , E)
  x∈x,E : ∀ { α } { x : Ref α } { E : Env }
    → x ∈nv (x , E)
  xα∈yβ↦w,E : ∀ { α β } { x : Ref α } { E : Env } { y : Ref β } { α≢β : α ≢ β } { w : ⟦ β ⟧ } { W : Value β w }
    → x ∈nv E → x ∈nv (y ↦ W , E)
  xα∈yβ,E : ∀ { α β } { x : Ref α } { E : Env } { y : Ref β } { α≢β : α ≢ β }
    → x ∈nv E → x ∈nv (y , E)
  xα∈yα↦w,E : ∀ { α } { x y : Ref α } { E : Env } { x≢y : x ≢ y } { w : ⟦ α ⟧ } { W : Value α w }
    → x ∈nv E → x ∈nv (y ↦ W , E)
  xα∈yα,E : ∀ { α } { x y : Ref α } { E : Env } { x≢y : x ≢ y }
    → x ∈nv E → x ∈nv (y , E)

data _↦_∈nv_ : ∀ { α } { v : ⟦ α ⟧ } → Ref α → Value α v → Env → Set where
  x↦v∈x↦v,E : ∀ { α } { v : ⟦ α ⟧ } {x : Ref α} {E : Env}
    → x ↦ val v ∈nv (x ↦ val v , E)
  xα↦v∈yβ↦w,E :
    ∀ { α β } { x : Ref α } { E : Env } { y : Ref β } { α≢β : α ≢ β }
    { v : ⟦ α ⟧ } { w : ⟦ β ⟧ }
    → x ↦ val v ∈nv E → x ↦ val v ∈nv (y ↦ val w , E)
  xα↦v∈yβ,E : ∀ { α β } { x : Ref α } { E : Env } { y : Ref β } { α≢β : α ≢ β } { v : ⟦ α ⟧ }
    → x ↦ val v ∈nv E → x ↦ val v ∈nv (y , E)
  xα↦v∈yα↦w,E : ∀ { α } { x y : Ref α } { E : Env } { x≢y : x ≢ y } { w : ⟦ α ⟧ } { v : ⟦ α ⟧ }
    → x ↦ val v ∈nv E → x ↦ val v ∈nv (y ↦ val w , E)
  xα↦v∈yα,E : ∀ { α } { x y : Ref α } { E : Env } { x≢y : x ≢ y } { v : ⟦ α ⟧ }
    → x ↦ val v ∈nv E → x ↦ val v ∈nv (y , E)

_∉nv_ : ∀ { α } → Ref α → Env → Set
x ∉nv E = ¬ (x ∈nv E)

infixr 4 _⊕_
_⊕_ : Env → Env → Env
(x ↦ v , E₁) ⊕ E₂ = x ↦ v , (E₁ ⊕ E₂)
(x , E₁) ⊕ E₂ = x , (E₁ ⊕ E₂)
ε ⊕ E₂ = E₂

data Continuation : Set where
  stop : Continuation
  _then_ : Statement → Continuation → Continuation

data SideEffects : Set where
  [] : SideEffects
  _∷_ : ℤ → SideEffects → SideEffects

data _covers_ : Env → FVSet → Set where
  nothing : ∀ { E } → E covers empty
  includes : ∀ { α t E } { x : Ref α } → x ∈nv E → E covers t → E covers (insert (α , x) t)

fvₖ : Continuation → FVSet
fvₖ stop = empty
fvₖ (s then k) = fvₛ s ∪ fvₖ k

data State : Set where
  state :
    Σ (Statement × Continuation × Env)
      (λ { (s , k , E) → E covers (fvₛ s ∪ fvₖ k) })
      → State
  -- TODO: Side effects

𝒮 : (s : Statement) → (k : Continuation) → (E : Env) → E covers (fvₛ s ∪ fvₖ k) → State
𝒮 s k E wf = state ((s , k , E) , wf)

Congruence : ∀ { a l } { A : Set a } → Rel A l → Set _
Congruence {A = A} _~_ = ∀ (f : A → A) x y → x ~ y → (f x) ~ (f y)

Clos : ∀ { n } → (Vec Set n) → Set → Set
Clos [] B = B
Clos (h ∷ t) B = h → Clos t B

lift : ∀ { n } { v : Vec Set n } { A : Set } { B : Set }
  → Clos v (A → B) → A → Clos v B
lift {v = []} clos = clos
lift {v = h ∷ t} clos a x = lift (clos x) a

Closure : ∀ { n } → (Vec Set n) → Set
Closure v = Clos v Statement

record Semantics : Set₁ where
  field
    _⊢_⇒_ : ∀ { α } → ∀ { v : ⟦ α ⟧ } → Env → Expr α → Value α v → Set
    ⊢-total : ∀ { α E } { e : Expr α } → ∃ λ v → (E ⊢ e ⇒ val v)
    ⊢-weakening : ∀ { E E' α β } { e : Expr α } { v : ⟦ α ⟧ } { x : Ref β } { w : ⟦ β ⟧ }
      → { _ : x ∉nv E × x ∉nv E' }
      → (E ⊕ E') ⊢ e ⇒ val v → (E ⊕ (x ↦ val w , ε) ⊕ E') ⊢ e ⇒ val v
    ⊢-exchange : ∀ { E E' α β γ } { x : Ref α } { y : Ref β }
      → { v : ⟦ α ⟧ } { w : ⟦ β ⟧ } { e : Expr γ } { ev : ⟦ γ ⟧ }
      → (E ⊕ (x ↦ val v , (y ↦ val w , ε)) ⊕ E') ⊢ e ⇒ val ev
      → (E ⊕ (y ↦ val w , (x ↦ val v , ε)) ⊕ E') ⊢ e ⇒ val ev
    -- TODO: variants on Env constructor
    nat : ∀ { E n } → E ⊢ ⟨ n ⟩ ⇒ val n
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

    _↝_ : Rel State 0ℓ
    ↝-if-true : ∀ { E k } { cond : Expr Bool } { s₁ s₂ : Statement } { wf }
      → E ⊢ cond ⇒ val 𝔹.true → 𝒮 (if cond then s₁ else s₂) k E wf ↝ 𝒮 s₁ k E ?
    ↝-if-false : ∀ { E k } { cond : Expr Bool } { s₁ s₂ : Statement } { wf }
      → E ⊢ cond ⇒ val 𝔹.false → 𝒮 (if cond then s₁ else s₂) k E wf ↝ 𝒮 s₂ k E ?
    ↝-assignment : ∀ { E k α } { id : Ref α } { e : Expr α } { v : ⟦ α ⟧ } { wf }
      → E ⊢ e ⇒ val v → 𝒮 (id ≔ e) k E wf ↝ 𝒮 nop k (id ↦ val v , E) ?
    ↝-seq : ∀ { E k } { s₁ s₂ : Statement } { wf }
      → 𝒮 (s₁ ； s₂) k E wf ↝ 𝒮 s₁ (s₂ then k) E ?
    ↝-decl : ∀ { E k α } { f : Ref α → Statement } { wf }
      → ∃ λ (x : Ref α) → (x ∉nv E) × (𝒮 (decl α f) k E wf ↝ 𝒮 (f x) k (x , E) ?)
    ↝-nop : ∀ { E k } { s : Statement } { wf }
      → 𝒮 nop (s then k) E wf ↝ 𝒮 s k E ?
    ↝-for : ∀ { E k } { l u : Expr Int } { f : Ref Int → Statement } { wf }
      → 𝒮 (for l to u then f) k E wf
        ↝ 𝒮 (if (l < u) then (
                (decl Int λ i → i ≔ l ； f i) ；
                for (l + ⟨ + 1 ⟩) to u then f)
             else nop) k E ?
    ↝-while : ∀ { E k } { e : Expr Bool } { s : Statement } { wf }
      → 𝒮 (while e then s) k E wf ↝ 𝒮 (if e then (s ； while e then s) else nop) k E ?
    ↝-det : ∀ { S S₁ S₂ } → S ↝ S₁ → S ↝ S₂ → S₁ ≡ S₂

  infix 0 _≅ₑ_
  _≅ₑ_ : ∀ { α } → Rel (Expr α) 0ℓ
  _≅ₑ_ { α } x y = ∀ { E : Env } → ∀ { v w : ⟦ α ⟧ }
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
  X ≅ₛ Y = ∀ { S₁ S₂ : State }
    → (¬ Terminating X × ¬ Terminating Y)
      ⊎ (X ↝* S₁ → Y ↝* S₂ → Stuck S₁ → Stuck S₂ → S₁ ≡ S₂)

  field
    ≅ₑ-equiv : ∀ { α } → IsEquivalence (_≅ₑ_ { α })
    ≅ₛ-equiv : IsEquivalence _≅ₛ_
    ≅ₛ-subst : ∀ { α E₁ E₂ k } { v w : ⟦ α ⟧ } { f : Expr α → Statement } { e₁ e₂ : Expr α }
      → E₁ ⊢ e₁ ⇒ val v → E₂ ⊢ e₂ ⇒ val w → v ≡ w
      → 𝒮 (f e₁) k E₁ ? ≅ₛ 𝒮 (f e₂) k E₂ ?
    ≅ₛ-cong : Congruence _≅ₛ_

