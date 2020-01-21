open import C
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.List
open import Data.Unit using (⊤ ; tt)
open import Algebra.FunctionProperties
open import Data.Integer using (+_)
import Data.List.Relation.Binary.Subset.Setoid.Properties as Setoidₚ
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
open import Data.AVL strictTotalOrder using (const ; union ; _∈?_ ; tree)
open import Data.AVL.Height using (_∼_⊔_)
open import Data.AVL.Indexed strictTotalOrder using (Tree ; leaf ; node)

module _ where
  abstract
    FVSet : Set
    FVSet = ⟨Set⟩
    
    infixr 8 _∪_
    _∪_ : FVSet → FVSet → FVSet
    _∪_ = union

    insert : ∀ { α } → Ref α → FVSet → FVSet
    insert x = Sets.insert (_ , x)

    empty : FVSet
    empty = Sets.empty

    delete : ∀ { α } → Ref α → FVSet → FVSet
    delete {α} x = Sets.delete (α , x)
    
    postulate _∈_ : ∀ { α } → Ref α → FVSet → Set

    delete-all : FVSet → FVSet → FVSet
    delete-all remove from = helper (Sets.toList remove) from
      where helper : List (∃ λ β → Ref β) → FVSet → FVSet
            helper [] s = s
            helper ((_ , h) ∷ t) s = delete h (helper t s)
    
  infix 4 _⊆_
  data _⊆_ : FVSet → FVSet → Set where
    nothing : ∀ { A : FVSet } → empty ⊆ A
    includes : ∀ { A B : FVSet } { α } { x : Ref α }
      → A ⊆ B → x ∈ B → insert x A ⊆ B

  abstract
    postulate ∪-assoc : Associative _≡_ _∪_
    postulate ∪-comm : Commutative _≡_ _∪_
    postulate ∪-cong : Congruent₂ _≡_ _∪_
    postulate ∪-id : Identity _≡_ empty _∪_
    postulate ∪-idem : Idempotent _≡_ _∪_
    postulate delall-dist : ∀ { X A B } → delete-all X (A ∪ B) ≡ (delete-all X A) ∪ (delete-all X B)
    postulate delall-elim : ∀ { A } → delete-all A A ≡ empty
    postulate delall-absorb : ∀ { A X } → A ∪ delete-all X A ≡ A
    postulate delall-reinsert : ∀ { A X } → X ∪ delete-all X A ≡ X ∪ A
    postulate ⊆-refl : Reflexive _⊆_
    postulate ∪~⊆ : ∀ { A B } → A ⊆ A ∪ B
    postulate ⊆-cong : Congruent₂ _⊆_ _∪_
    postulate ⊆-trans : ∀ { A B C : FVSet } → A ⊆ B → B ⊆ C → A ⊆ C

≡⇒⊆ : ∀ { A B } → A ≡ B → A ⊆ B × B ⊆ A
≡⇒⊆ refl = ⊆-refl , ⊆-refl

record FreeVariables : Set₁ where
  field    
    fvᵣ : ∀ { α } → Ref α → FVSet
    fvₑ : ∀ { α } → Expr α → FVSet
    fvₛ : Statement → FVSet
    
    -- fv-ref : ∀ { α } { x : Ref α } → x ∈ fvᵣ x
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
      → delete-all (fvᵣ x) (fvₛ (f x)) ≡ fvₛ (decl α f)
    fv-nop : fvₛ nop ≡ empty
    fv-for : ∀ { l u } { f : Ref Int → Statement } { x : Ref Int }
      → fvₑ l ∪ fvₑ u ∪ delete-all (fvᵣ x) (fvₛ (f x)) ≡ fvₛ (for l to u then f)
    fv-while : ∀ { e s } → fvₑ e ∪ fvₛ s ≡ fvₛ (while e then s)

open FreeVariables ⦃ ... ⦄
open ≡-Reasoning

module _ ⦃ _ : FreeVariables ⦄ where

  fv-if₁ : ∀ { e } { x y : Statement } → fvₑ e ⊆ fvₛ (if e then x else y)
  fv-if₁ {e} {x} {y} rewrite sym (fv-if {e} {x} {y}) = ∪~⊆

  fv-if₂ : ∀ { e } { x y : Statement } → fvₛ x ⊆ fvₛ (if e then x else y)
  fv-if₂ {e} {x} {y}
    rewrite
      begin
        fvₛ (if e then x else y)
        ≡˘⟨ fv-if ⟩
        fvₑ e ∪ fvₛ x ∪ fvₛ y
        ≡˘⟨ ∪-assoc (fvₑ e) (fvₛ x) (fvₛ y) ⟩
        (fvₑ e ∪ fvₛ x) ∪ fvₛ y
        ≡⟨ ∪-cong (∪-comm (fvₑ e) (fvₛ x)) refl ⟩
        (fvₛ x ∪ fvₑ e) ∪ fvₛ y
        ≡⟨ ∪-assoc (fvₛ x) (fvₑ e) (fvₛ y) ⟩
        fvₛ x ∪ fvₑ e ∪ fvₛ y
      ∎
      = ∪~⊆

  fv-if₃ : ∀ { e } { x y : Statement } → fvₛ y ⊆ fvₛ (if e then x else y)
  fv-if₃ {e} {x} {y}
    rewrite
      begin
        fvₛ (if e then x else y)
        ≡˘⟨ fv-if ⟩
        fvₑ e ∪ fvₛ x ∪ fvₛ y
        ≡˘⟨ ∪-assoc (fvₑ e) (fvₛ x) (fvₛ y) ⟩
        (fvₑ e ∪ fvₛ x) ∪ fvₛ y
        ≡⟨ ∪-comm (fvₑ e ∪ fvₛ x) (fvₛ y) ⟩
        fvₛ y ∪ fvₑ e ∪ fvₛ x
      ∎
      = ∪~⊆

  fv-nop₁ : ∀ { A : FVSet } → fvₛ nop ⊆ A
  fv-nop₁ {A}
    with fvₛ nop | sym fv-nop
  ... | _ | refl = nothing

  fv-nop₂ : ∀ { A } → A ⊆ fvₛ nop ∪ A
  fv-nop₂ {A}
    rewrite
      begin
        fvₛ nop ∪ A
        ≡⟨ cong (λ ‿ → ‿ ∪ A) fv-nop ⟩
        empty ∪ A
        ≡⟨ (proj₁ ∪-id) _ ⟩
        A
      ∎
      = ⊆-refl

  fv-seq₁ : ∀ { s₁ s₂ X } → fvₛ s₁ ∪ fvₛ s₂ ∪ X ⊆ fvₛ (s₁ ； s₂) ∪ X
  fv-seq₁ {s₁} {s₂} {X}
    rewrite sym (fv-seq {s₁} {s₂}) | (∪-assoc (fvₛ s₁) (fvₛ s₂) X) =
      ⊆-refl

  fv-for₁ : ∀ { l u : Expr Int } { f : Ref Int → Statement } { x : Ref Int }
    → fvₛ (for l to u then f) ≡ fvₛ (
      if l < u then
        (decl Int λ i → i ≔ l ； f i) ；
        for (l + ⟨ + 1 ⟩) to u then f
      else nop)
  fv-for₁ {l} {u} {f} {x} =
    begin
      fvₛ (for l to u then f)
      ≡˘⟨ fv-for ⟩
      fvₑ l ∪ fvₑ u ∪ delete-all (fvᵣ x) (fvₛ (f x))
      ≡˘⟨ ∪-idem _ ⟩
      (fvₑ l ∪ fvₑ u ∪ delete-all (fvᵣ x) (fvₛ (f x))) ∪ (fvₑ l ∪ fvₑ u ∪ delete-all (fvᵣ x) (fvₛ (f x)))
      ≡⟨ ∪-assoc _ _ _ ⟩
      fvₑ l ∪ (fvₑ u ∪ delete-all (fvᵣ x) (fvₛ (f x))) ∪ (fvₑ l ∪ fvₑ u ∪ delete-all (fvᵣ x) (fvₛ (f x)))
      ≡⟨ cong (λ ○ → _ ∪ ○) (∪-assoc _ _ _) ⟩
      fvₑ l ∪ fvₑ u ∪ delete-all (fvᵣ x) (fvₛ (f x)) ∪ fvₑ l ∪ fvₑ u ∪ delete-all (fvᵣ x) (fvₛ (f x))
      ≡˘⟨ cong (λ ○ → _ ∪ _ ∪ _ ∪ ○ ∪ _ ∪ _) ((proj₂ ∪-id) _) ⟩
      fvₑ l ∪ fvₑ u ∪ delete-all (fvᵣ x) (fvₛ (f x)) ∪ (fvₑ l ∪ empty) ∪ fvₑ u ∪ delete-all (fvᵣ x) (fvₛ (f x))
      ≡˘⟨ cong (λ ○ → _ ∪ _ ∪ _ ∪ (_ ∪ ○) ∪ _ ∪ _) fv-nat ⟩
      fvₑ l ∪ fvₑ u ∪ delete-all (fvᵣ x) (fvₛ (f x)) ∪ (fvₑ l ∪ fvₑ ⟨ + 1 ⟩) ∪ fvₑ u ∪ delete-all (fvᵣ x) (fvₛ (f x))
      ≡⟨ cong (λ ○ → _ ∪ _ ∪ _ ∪ ○ ∪ _ ∪ _) fv-+ ⟩
      fvₑ l ∪ fvₑ u ∪ delete-all (fvᵣ x) (fvₛ (f x)) ∪ fvₑ (l + ⟨ + 1 ⟩) ∪ fvₑ u ∪ delete-all (fvᵣ x) (fvₛ (f x))
      ≡⟨ cong (λ ○ → _ ∪ _ ∪ _ ∪ ○) fv-for ⟩
      fvₑ l ∪ fvₑ u ∪ delete-all (fvᵣ x) (fvₛ (f x)) ∪ fvₛ (for (l + ⟨ + 1 ⟩) to u then f)
      ≡˘⟨ ∪-assoc _ _ _ ⟩
      (fvₑ l ∪ fvₑ u) ∪ delete-all (fvᵣ x) (fvₛ (f x)) ∪ fvₛ (for (l + ⟨ + 1 ⟩) to u then f)
      ≡⟨ cong (λ ○ → ○ ∪ _ ∪ _) (∪-comm _ _) ⟩
      (fvₑ u ∪ fvₑ l) ∪ delete-all (fvᵣ x) (fvₛ (f x)) ∪ fvₛ (for (l + ⟨ + 1 ⟩) to u then f)
      ≡⟨ ∪-assoc _ _ _ ⟩
      fvₑ u ∪ fvₑ l ∪ delete-all (fvᵣ x) (fvₛ (f x)) ∪ fvₛ (for (l + ⟨ + 1 ⟩) to u then f)
      ≡˘⟨ cong (λ ○ → _ ∪ ○ ∪ _) delall-absorb ⟩
      fvₑ u ∪ (fvₑ l ∪ delete-all (fvᵣ x) (fvₑ l)) ∪ delete-all (fvᵣ x) (fvₛ (f x)) ∪ fvₛ (for (l + ⟨ + 1 ⟩) to u then f)
      ≡⟨ cong (λ ○ → _ ∪ ○) (∪-assoc _ _ _) ⟩
      fvₑ u ∪ fvₑ l ∪ delete-all (fvᵣ x) (fvₑ l) ∪ delete-all (fvᵣ x) (fvₛ (f x)) ∪ fvₛ (for (l + ⟨ + 1 ⟩) to u then f)
      ≡˘⟨ cong (λ ○ → _ ∪ _ ∪ ○) (∪-assoc _ _ _) ⟩
      fvₑ u ∪ fvₑ l ∪ (delete-all (fvᵣ x) (fvₑ l) ∪ delete-all (fvᵣ x) (fvₛ (f x))) ∪ fvₛ (for (l + ⟨ + 1 ⟩) to u then f)
      ≡˘⟨ ∪-assoc _ _ _ ⟩
      (fvₑ u ∪ fvₑ l) ∪ (delete-all (fvᵣ x) (fvₑ l) ∪ delete-all (fvᵣ x) (fvₛ (f x))) ∪ fvₛ (for (l + ⟨ + 1 ⟩) to u then f)
      ≡⟨ cong (λ ○ → ○ ∪ (_ ∪ _) ∪ _) (∪-comm _ _) ⟩
      (fvₑ l ∪ fvₑ u) ∪ (delete-all (fvᵣ x) (fvₑ l) ∪ delete-all (fvᵣ x) (fvₛ (f x))) ∪ fvₛ (for (l + ⟨ + 1 ⟩) to u then f)
      ≡⟨ cong (λ ○ → ○ ∪ (_ ∪ _) ∪ _) fv-< ⟩
      fvₑ (l < u) ∪ (delete-all (fvᵣ x) (fvₑ l) ∪ delete-all (fvᵣ x) (fvₛ (f x))) ∪ fvₛ (for (l + ⟨ + 1 ⟩) to u then f)
      ≡˘⟨ cong (λ ○ → _ ∪ (○ ∪ _) ∪ _) ((proj₁ ∪-id) _) ⟩
      fvₑ (l < u) ∪ ((empty ∪ delete-all (fvᵣ x) (fvₑ l)) ∪ delete-all (fvᵣ x) (fvₛ (f x))) ∪ fvₛ (for (l + ⟨ + 1 ⟩) to u then f)
      ≡˘⟨ cong (λ ○ → _ ∪ ((○ ∪ delete-all _ _) ∪ delete-all _ _) ∪ _) delall-elim ⟩
      fvₑ (l < u) ∪ ((delete-all (fvᵣ x) (fvᵣ x) ∪ delete-all (fvᵣ x) (fvₑ l)) ∪ delete-all (fvᵣ x) (fvₛ (f x))) ∪ fvₛ (for (l + ⟨ + 1 ⟩) to u then f)
      ≡˘⟨ cong (λ ○ → _ ∪ (○ ∪ _) ∪ _) delall-dist ⟩
      fvₑ (l < u) ∪ (delete-all (fvᵣ x) (fvᵣ x ∪ fvₑ l) ∪ delete-all (fvᵣ x) (fvₛ (f x))) ∪ fvₛ (for (l + ⟨ + 1 ⟩) to u then f)
      ≡⟨ cong (λ ○ → _ ∪ (delete-all _ ○ ∪ _) ∪ _) fv-assignment ⟩
      fvₑ (l < u) ∪ (delete-all (fvᵣ x) (fvₛ (x ≔ l)) ∪ delete-all (fvᵣ x) (fvₛ (f x))) ∪ fvₛ (for (l + ⟨ + 1 ⟩) to u then f)
      ≡˘⟨ cong (λ ○ → _ ∪ ○ ∪ _) delall-dist ⟩
      fvₑ (l < u) ∪ delete-all (fvᵣ x) (fvₛ (x ≔ l) ∪ fvₛ (f x)) ∪ fvₛ (for (l + ⟨ + 1 ⟩) to u then f)
      ≡⟨ cong (λ ○ → _ ∪ delete-all _ ○ ∪ _) fv-seq ⟩
      fvₑ (l < u) ∪ delete-all (fvᵣ x) (fvₛ (x ≔ l ； f x)) ∪ fvₛ (for (l + ⟨ + 1 ⟩) to u then f)
      ≡⟨ cong (λ ○ → _ ∪ ○ ∪ _) fv-decl ⟩
      fvₑ (l < u) ∪ fvₛ (decl Int λ i → i ≔ l ； f i) ∪ fvₛ (for (l + ⟨ + 1 ⟩) to u then f)
      ≡⟨ cong (λ ○ → _ ∪ ○) fv-seq ⟩
      fvₑ (l < u) ∪ fvₛ ((decl Int λ i → i ≔ l ； f i) ； for (l + ⟨ + 1 ⟩) to u then f)
      ≡˘⟨ cong (λ ○ → _ ∪ ○) ((proj₂ ∪-id) _) ⟩
      fvₑ (l < u) ∪ fvₛ ((decl Int λ i → i ≔ l ； f i) ； for (l + ⟨ + 1 ⟩) to u then f) ∪ empty
      ≡˘⟨ cong (λ ○ → _ ∪ _ ∪ ○) fv-nop ⟩
      fvₑ (l < u) ∪ fvₛ ((decl Int λ i → i ≔ l ； f i) ； for (l + ⟨ + 1 ⟩) to u then f) ∪ fvₛ nop
      ≡⟨ fv-if ⟩
      fvₛ (if (l < u) then (decl Int λ i → i ≔ l ； f i) ； for (l + ⟨ + 1 ⟩) to u then f else nop) 
    ∎

  fv-while₁ : ∀ { e : Expr Bool } { s : Statement }
    → fvₛ (while e then s) ≡ fvₛ (if e then (s ； while e then s) else nop)
  fv-while₁ {e} {s} =
    begin
      fvₛ (while e then s)
      ≡˘⟨ fv-while ⟩
      fvₑ e ∪ fvₛ s
      ≡˘⟨ ∪-idem _ ⟩
      (fvₑ e ∪ fvₛ s) ∪ (fvₑ e ∪ fvₛ s)
      ≡⟨ ∪-assoc _ _ _ ⟩
      fvₑ e ∪ fvₛ s ∪ fvₑ e ∪ fvₛ s
      ≡⟨ cong (λ ○ → _ ∪ _ ∪ ○) fv-while ⟩
      fvₑ e ∪ fvₛ s ∪ fvₛ (while e then s)
      ≡˘⟨ cong (λ ○ → _ ∪ ○) (proj₂ ∪-id (fvₛ s ∪ fvₛ (while e then s))) ⟩
      fvₑ e ∪ (fvₛ s ∪ fvₛ (while e then s)) ∪ empty
      ≡˘⟨ cong (λ ○ → _ ∪ (_ ∪ _) ∪ ○) fv-nop ⟩
      fvₑ e ∪ (fvₛ s ∪ fvₛ (while e then s)) ∪ fvₛ nop
      ≡⟨ cong (λ ○ → _ ∪ ○ ∪ _) fv-seq ⟩
      fvₑ e ∪ fvₛ (s ； while e then s) ∪ fvₛ nop
      ≡⟨ fv-if ⟩
      fvₛ (if e then (s ； while e then s) else nop)
    ∎

  fv-decl₁ : ∀ { α } { x : Ref α } { f : Ref α → Statement } { A }
    → fvₛ (f x) ∪ A ⊆ fvᵣ x ∪ fvₛ (decl α f) ∪ A
  fv-decl₁ {α} {x} {f} {A}
    rewrite
      begin
        fvᵣ x ∪ fvₛ (decl α f) ∪ A
        ≡˘⟨ cong (λ ○ → _ ∪ ○ ∪ _) fv-decl ⟩
        fvᵣ x ∪ delete-all (fvᵣ x) (fvₛ (f x)) ∪ A
        ≡˘⟨ ∪-assoc _ _ _ ⟩
        (fvᵣ x ∪ delete-all (fvᵣ x) (fvₛ (f x))) ∪ A
        ≡⟨ cong (λ ○ → ○ ∪ _) delall-reinsert ⟩
        (fvᵣ x ∪ fvₛ (f x)) ∪ A
        ≡⟨ cong (λ ○ → ○ ∪ _) (∪-comm _ _) ⟩
        (fvₛ (f x) ∪ fvᵣ x) ∪ A 
        ≡⟨ ∪-assoc _ _ _ ⟩
        fvₛ (f x) ∪ fvᵣ x ∪ A
        ≡⟨ cong (λ ○ → _ ∪ ○) (∪-comm _ _) ⟩
        fvₛ (f x) ∪ A ∪ fvᵣ x
        ≡˘⟨ ∪-assoc _ _ _ ⟩
        (fvₛ (f x) ∪ A) ∪ fvᵣ x
      ∎
    = ∪~⊆
