open import C

open import Data.Bool as 𝔹 using () renaming (Bool to 𝔹)
open import Data.Integer as ℤ using (ℤ ; +_)
open import Data.Product using (Σ ; ∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (⊤ ; tt)
open import Data.Vec using (Vec ; [] ; _∷_)
open import Data.List using (List)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

import Level

open C.C ⦃ ... ⦄

module C.Properties.State ⦃ _ : C ⦄ where

⟦_⟧ : c_type → Set
⟦ Int ⟧ = ℤ
⟦ Bool ⟧ = 𝔹
⟦ Array α n ⟧ = Vec ⟦ α ⟧ n

data Env : Set where
  _↦_,_ : ∀ { α } → Ref α → ⟦ α ⟧ → Env → Env
  _,_ : ∀ { α } → Ref α → Env → Env
  ε : Env

data _∈nv_ : ∀ { α } → Ref α → Env → Set where
  x∈x↦v,E : ∀ { α } { v : ⟦ α ⟧ } {x : Ref α} {E : Env}
    → x ∈nv (x ↦ v , E)
  x∈x,E : ∀ { α } { x : Ref α } { E : Env }
    → x ∈nv (x , E)
  xα∈yβ↦w,E : ∀ { α β } { x : Ref α } { E : Env } { y : Ref β } { α≢β : α ≢ β } { w : ⟦ β ⟧ }
    → x ∈nv E → x ∈nv (y ↦ w , E)
  xα∈yβ,E : ∀ { α β } { x : Ref α } { E : Env } { y : Ref β } { α≢β : α ≢ β }
    → x ∈nv E → x ∈nv (y , E)
  xα∈yα↦w,E : ∀ { α } { x y : Ref α } { E : Env } { x≢y : x ≢ y } { w : ⟦ α ⟧ }
    → x ∈nv E → x ∈nv (y ↦ w , E)
  xα∈yα,E : ∀ { α } { x y : Ref α } { E : Env } { x≢y : x ≢ y }
    → x ∈nv E → x ∈nv (y , E)

data _↦_∈nv_ : ∀ { α } → Ref α → ⟦ α ⟧ → Env → Set where
  x↦v∈x↦v,E : ∀ { α } { v : ⟦ α ⟧ } {x : Ref α} {E : Env}
    → x ↦ v ∈nv (x ↦ v , E)
  xα↦v∈yβ↦w,E :
    ∀ { α β } { x : Ref α } { E : Env } { y : Ref β } { α≢β : α ≢ β }
    { v : ⟦ α ⟧ } { w : ⟦ β ⟧ }
    → x ↦ v ∈nv E → x ↦ v ∈nv (y ↦ w , E)
  xα↦v∈yβ,E : ∀ { α β } { x : Ref α } { E : Env } { y : Ref β } { α≢β : α ≢ β } { v : ⟦ α ⟧ }
    → x ↦ v ∈nv E → x ↦ v ∈nv (y , E)
  xα↦v∈yα↦w,E : ∀ { α } { x y : Ref α } { E : Env } { x≢y : x ≢ y } { w : ⟦ α ⟧ } { v : ⟦ α ⟧ }
    → x ↦ v ∈nv E → x ↦ v ∈nv (y ↦ w , E)
  xα↦v∈yα,E : ∀ { α } { x y : Ref α } { E : Env } { x≢y : x ≢ y } { v : ⟦ α ⟧ }
    → x ↦ v ∈nv E → x ↦ v ∈nv (y , E)

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

data State : Set where
  Ω : State
  𝒮 : Statement → Continuation → Env → State
