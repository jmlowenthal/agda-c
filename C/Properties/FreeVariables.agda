open import C
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Bool using (T)
open import Data.List
open import Data.Unit
import Level

open C.C ⦃ ... ⦄

module C.Properties.FreeVariables
  ⦃ _ : C ⦄
  { _⊑_ : Rel (∃ λ β → Ref β) Level.zero }
  ( isStrictTotalOrder : IsStrictTotalOrder _≡_ _⊑_ ) where

strictTotalOrder : StrictTotalOrder _ _ _
strictTotalOrder =
  record {
    Carrier = ∃ λ β → Ref β ;
    _≈_ = _≡_ ;
    _<_ = _⊑_ ;
    isStrictTotalOrder = isStrictTotalOrder
  }

open import Data.AVL.Sets strictTotalOrder as Sets using (⟨Set⟩)
open import Data.AVL strictTotalOrder using (union ; _∈?_)

record FreeVariables : Set₁ where

  infixr 8 _∪_
  _∪_ : ⟨Set⟩ → ⟨Set⟩ → ⟨Set⟩
  _∪_ = union

  infix 8 _∈_
  _∈_ : ∀ { α } → Ref α → ⟨Set⟩ → Set
  x ∈ A = T ((_ , x) ∈? A)

  FVSet : Set
  FVSet = ⟨Set⟩

  empty = Sets.empty
  insert = Sets.insert
  delete = Sets.delete

  field    
    fvᵣ : ∀ { α } → Ref α → ⟨Set⟩
    fvₑ : ∀ { α } → Expr α → ⟨Set⟩
    fvₛ : Statement → ⟨Set⟩
    
    fv-ref : ∀ { α } { x : Ref α } → x ∈ fvᵣ x
    fv-index : ∀ { α n } { e : Ref (Array α n) } { i }
      → fvᵣ e ∪ fvₑ i ≡ fvᵣ (_[_] e i)
    
    fv-nat : ∀ { n } → fvₑ ⟨ n ⟩ ≡ empty
    fv-+ : ∀ { x y } → fvₑ x ∪ fvₑ y ≡ fvₑ (x + y)
    fv-* : ∀ { x y } → fvₑ x ∪ fvₑ y ≡ fvₑ (x * y)
    fv-∸ : ∀ { x y } → fvₑ x ∪ fvₑ y ≡ fvₑ (x - y)
    fv-/ : ∀ { x y } → fvₑ x ∪ fvₑ y ≡ fvₑ (x / y)
    fv-< : ∀ { x y : Expr Int } → fvₑ x ∪ fvₑ y ≡ fvₑ (x < y)
    fv-<= : ∀ { x y } → fvₑ x ∪ fvₑ y ≡ fvₑ (x <= y)
    fv-> : ∀ { x y } → fvₑ x ∪ fvₑ y ≡ fvₑ (x > y)
    fv->= : ∀ { x y } → fvₑ x ∪ fvₑ y ≡ fvₑ (x >= y)
    fv-== : ∀ { x y } → fvₑ x ∪ fvₑ y ≡ fvₑ (x == y)
    fv-true : fvₑ true ≡ empty
    fv-false : fvₑ false ≡ empty
    fv-|| : ∀ { x y } → fvₑ x ∪ fvₑ y ≡ fvₑ (x || y)
    fv-&& : ∀ { x y } → fvₑ x ∪ fvₑ y ≡ fvₑ (x && y)
    fv-! : ∀ { x } → fvₑ (! x) ≡ fvₑ x
    fv-deref : ∀ { α } { x : Ref α } → fvᵣ x ≡ fvₑ (★ x)
    
    fv-if : ∀ { e x y } → fvₑ e ∪ fvₛ x ∪ fvₛ y ≡ fvₛ (if e then x else y)
    fv-assignment : ∀ { α } { x : Ref α } { e : Expr α }
      → fvᵣ x ∪ fvₑ e ≡ fvₛ (x ≔ e)
    fv-seq : ∀ { x y } → fvₛ x ∪ fvₛ y ≡ fvₛ (x ； y)
    fv-decl : ∀ { α } { f : Ref α → Statement } { x : Ref α }
      → delete (α , x) (fvₛ (f x)) ≡ fvₛ (decl α f)
    fv-nop : fvₛ nop ≡ empty
    fv-for : ∀ { l u } { f : Ref Int → Statement } { x : Ref Int }
      → fvₑ l ∪ fvₑ u ∪ delete (Int , x) (fvₛ (f x)) ≡ fvₛ (for l to u then f)
    fv-while : ∀ { e s } → fvₑ e ∪ fvₛ s ≡ fvₛ (while e then s)
