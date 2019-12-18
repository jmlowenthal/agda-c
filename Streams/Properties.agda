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
s ≅ t = ∀ { β } { z : Expr β } { f x } → fold f z s x ≅ₚ fold f z t x

≅-trans : ∀ { α } → Transitive (_≅_ {α})
≅-trans {α} A B = IsEquivalence.trans ≅ₚ-equiv A B

≅-equiv : ∀ { α } → IsEquivalence (_≅_ { α })
≅-equiv {α} = record {
  refl = IsEquivalence.refl ≅ₚ-equiv ;
  trans = ≅-trans {α} ;
  sym = {!!} }

≅-setoid : ∀ { α : c_type } → Setoid _ _
≅-setoid { α } = record {
  Carrier = Stream α ;
  _≈_ = _≅_ ;
  isEquivalence = ≅-equiv }

import Relation.Binary.Reasoning.Setoid as Reasoning
open module ≅-Reasoning {α : c_type} = Reasoning (≅-setoid {α})
  renaming (_≈⟨_⟩_ to _≅⟨_⟩_ ; _≈˘⟨_⟩_ to _≅˘⟨_⟩_) public

infix 1 begin⟨_⟩_
begin⟨_⟩_ : (α : c_type) → ∀ {x y} → _IsRelatedTo_ {α} x y → x ≅ y
begin⟨_⟩_ α {x} {y} = begin_ {α} {x} {y}

map-map : ∀ { α β γ }
  → ∀ { s : Stream α } → ∀ { f : Expr β → Expr γ } → ∀ { g : Expr α → Expr β }
  → map f (map g s) ≅ map (f ∘ g) s
map-map = {!!}

map-id : ∀ { α } → ∀ { s : Stream α } → map id s ≅ s
map-id {α} {s@(linear (producer (init , for (bound , index))))} = {!!}
  -- begin
  --   map id s
  --   ≡⟨⟩
  --   linear (producer (init , for (bound , λ s i k → index s i (λ e → decl α λ t → t ≔ id e ； k (★ t)))))
  --   ≡⟨⟩
  --   linear (producer (init , for (bound , λ s i k → index s i (λ e → decl α λ t → t ≔ e ； k (★ t)))))
  --   ≅⟨ {!cong!} ⟩
  --   linear (producer (init , for (bound , λ s i k → index s i (λ e → decl α λ t → k e))))
  --   ≅⟨ {!!} ⟩
  --   linear (producer (init , for (bound , λ s i k → index s i (λ e → k e))))
  --   ≡⟨⟩
  --   linear (producer (init , for (bound , index)))
  --   ≡⟨⟩
  --   s
  -- ∎

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
