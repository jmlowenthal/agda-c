open import C
import C.Properties.FreeVariables as FV
open import Relation.Binary
open import Data.Product using (Σ ; ∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality
import Level
open import Data.Integer as ℤ using (ℤ ; +_)
open import Data.Bool as 𝔹 using () renaming (Bool to 𝔹)
open import Data.Vec using (Vec ; [] ; _∷_)
open import Relation.Nullary
open import Data.Unit using (⊤ ; tt)

open C.C ⦃ ... ⦄

module C.Properties.State
  ⦃ _ : C ⦄
  { _~_ : Rel (∃ λ β → Ref β) Level.zero }
  { isStrictTotalOrder : IsStrictTotalOrder _≡_ _~_ }
  ⦃ _ : FV.FreeVariables isStrictTotalOrder ⦄ where

open FV.FreeVariables ⦃ ... ⦄
open FV isStrictTotalOrder

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
  includes : ∀ { α t E } { x : Ref α } → x ∈nv E → E covers t → E covers (insert x t)

fvₖ : Continuation → FVSet
fvₖ stop = empty
fvₖ (s then k) = fvₛ s ∪ fvₖ k

postulate ∈-to-∈nv : ∀ { α } { x : Ref α } { A E } → x ∈ A → E covers A → x ∈nv E

⊆-covers : ∀ { E A B } → E covers A → B ⊆ A → E covers B
⊆-covers E/A nothing = nothing
⊆-covers E/A (includes B⊆A x∈A) = includes (∈-to-∈nv x∈A E/A) (⊆-covers E/A B⊆A)

postulate grow-env : ∀ { E A α } { x : Ref α } { v : ⟦ α ⟧ } → E covers A → (x ↦ val v , E) covers A

data State : Set where
  state :
    Σ (Statement × Continuation × Env)
      (λ { (s , k , E) → E covers (fvₛ s ∪ fvₖ k) })
      → State
  -- TODO: Side effects

𝒮 : (s : Statement) → (k : Continuation) → (E : Env) → E covers (fvₛ s ∪ fvₖ k) → State
𝒮 s k E wf = state ((s , k , E) , wf)
