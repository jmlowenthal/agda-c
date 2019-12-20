open import Streams.Base
open import C
open import C.Properties.ReductionSemantics
open import Function
open import Relation.Binary
open import Level using (0ℓ)
open import Data.Unit
open import Data.Product using (_×_ ; _,_)
open import Relation.Binary.PropositionalEquality

module Streams.Properties ⦃ _ : C ⦄ ⦃ _ : Semantics ⦄ where

open C.C ⦃ ... ⦄
open Semantics ⦃ ... ⦄

_≅_ : ∀ { α } → Rel (Stream α) 0ℓ
_≅_ {α} s t = ∀ { β } → (f : Expr β → Expr α → Expr β) → ∀ { z x }
  → fold f z s x ≅ₚ fold f z t x

≅-equiv : ∀ { α } → IsEquivalence (_≅_ {α})
≅-equiv {α} = record {
  refl = λ _ → IsEquivalence.refl ≅ₚ-equiv ;
  trans = λ A B {_} f → IsEquivalence.trans ≅ₚ-equiv (A f) (B f) ;
  sym = λ A {_} f → IsEquivalence.sym ≅ₚ-equiv (A f) }

≅-setoid : ∀ { α : c_type } → Setoid _ _
≅-setoid {α} = record {
  Carrier = Stream α ;
  _≈_ = _≅_ {α} ;
  isEquivalence = ≅-equiv {α} }

import Relation.Binary.Reasoning.Setoid as Reasoning
open module ≅-Reasoning {α} = Reasoning (≅-setoid {α})
  renaming (_≈⟨_⟩_ to _≅⟨_⟩_ ; _≈˘⟨_⟩_ to _≅˘⟨_⟩_) public

map-map : ∀ { α β γ }
  → ∀ { s : Stream α } → ∀ { f : Expr β → Expr γ } → ∀ { g : Expr α → Expr β }
  → map f (map g s) ≅ map (f ∘ g) s
map-map = {!!}

≅-cong : ∀ { α } (β : Set) { a b : β → Statement } → (F : (β → Statement) → Stream α) → ((i : β) → a i ≅ₚ b i) → F a ≅ F b
≅-cong {α} β {a} {b} F a≅b f {z} {x} = {!!}

decl-cong : ∀ { α } { f g : Ref α → Statement }
  → (∀ (r : Ref α) → f r ≅ₚ g r) → (decl α f) ≅ₚ (decl α g)

decl-elim : ∀ { α } { f : Statement } → (decl α λ x → f) ≅ₚ f

map-id : ∀ { α } → ∀ { s : Stream α } → map id s ≅ s
map-id {α} {s@(linear (producer (init , for (bound , index))))} =
  let wrap : (_ → Expr Int → (Expr α → Statement) → Statement) → Stream α
      wrap index = linear (producer (init , for (bound , index)))
      index' f s i k = index s i (f k)
  in
  begin
    map id s
    ≡⟨⟩
    wrap (index' (λ k e → decl α λ t → t ≔ id e ； k (★ t)))
    ≡⟨⟩
    wrap (index' (λ k e → decl α λ t → t ≔ e ； k (★ t)))
    ≅⟨ ≅-cong
      ((Expr α → Statement) × Expr α)
      (λ a → wrap (index' (λ k e → a (k , e))))
      (λ { (k , e) → decl-cong (λ r → ≔-subst {x = r} {e = e} {f = k}) })
    ⟩
    wrap (index' (λ k e → decl α λ t → k e))
    ≅⟨ ≅-cong
      (((Expr α → Statement) × Expr α))
      (λ a → wrap (index' (λ k e → a (k , e))))
      (λ { (k , e) → decl-elim {α = α} {f = k e} })
    ⟩
    wrap (index' (λ k e → k e))
    ≡⟨⟩
    wrap index
    ≡⟨⟩
    s
  ∎

filter-filter : ∀ { α }
  → ∀ { s : Stream α } → ∀ { f : Expr α → Expr Bool } → ∀ { g : Expr α → Expr Bool }
  → filter f (filter g s) ≅ filter (λ x → f x && g x) s
filter-filter = {!!}

filter-true : ∀ { α } → ∀ { s : Stream α } → filter (λ x → true) s ≅ s
filter-true = {!!}

filter-false : ∀ { α } → ∀ { s : Stream α }
  → filter (λ x → false) s ≅ {!nil!}
filter-false = {!!}

filter-map : ∀ { α β }
  → ∀ { s : Stream α } → ∀ { f : Expr β → Expr Bool } → ∀ { g : Expr α → Expr β }
  → filter f (map g s) ≅ map g (filter (f ∘ g) s)
filter-map = {!!}

-- TODO: zipWith

flatmap-assoc : ∀ { α β }
  → ∀ { s : Stream α } → ∀ { f : Expr β → Stream α } → ∀ { g : Expr α → Stream β }
  → flatmap (λ x → flatmap f (g x)) s ≅ flatmap f (flatmap g s)
flatmap-assoc = {!!}

flatmap-map : ∀ { α β γ }
  → ∀ { s : Stream α } → ∀ { f : Expr β → Stream γ } → ∀ { g : Expr α → Expr β }
  → flatmap f (map g s) ≅ flatmap (f ∘ g) s
flatmap-map = {!!}

map-flatmap : ∀ { α β γ }
  → ∀ { s : Stream α } → ∀ { f : Expr β → Expr γ } → ∀ { g : Expr α → Stream β }
  → map f (flatmap g s) ≅ flatmap ((map f) ∘ g) s

--flatmap-filter : ∀ { α β }
--  → ∀ { s : Stream α } → ∀ { f : Code α → Stream β } → ∀ { g : Code α → Code Bool }
--  → flatmap f (filter g s) ≅ flatmap (λ x → if g x then f x else nil) s

filter-flatmap : ∀ { α β }
  → ∀ { s : Stream α } → ∀ { f : Expr β → Expr Bool } → ∀ { g : Expr α → Stream β }
  → filter f (flatmap g s) ≅ flatmap ((filter f) ∘ g) s
