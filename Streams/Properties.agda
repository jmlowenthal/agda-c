open import Streams.Base
open import C.Properties
open import Function
open import Relation.Binary
open import Level using (0ℓ)
open import Data.Unit
open import Data.Product using (_×_ ; _,_)

module Streams.Properties where

open C.C ⦃ ... ⦄

_≡_ : ∀ ⦃ _ : C ⦄ → ∀ { α } → Rel (Stream α) 0ℓ
_≡_ = {!!}

map-map : ∀ ⦃ _ : C ⦄ → ∀ ⦃ _ : Equivalence ⦄ → ∀ { α β γ }
  → ∀ { s : Stream α } → ∀ { f : Expr β → Expr γ } → ∀ { g : Expr α → Expr β }
  → map f (map g s) ≡ map (f ∘ g) s
map-map = {!!}

map-id : ∀ ⦃ _ : C ⦄ → ∀ { α } → ∀ { s : Stream α } → map id s ≡ s
map-id = {!!}

filter-filter : ∀ ⦃ _ : C ⦄ → ∀ { α }
  → ∀ { s : Stream α } → ∀ { f : Expr α → Expr Bool } → ∀ { g : Expr α → Expr Bool }
  → filter f (filter g s) ≡ filter (λ x → f x && g x) s
filter-filter = {!!}

filter-true : ∀ ⦃ _ : C ⦄ → ∀ { α } → ∀ { s : Stream α } → filter (λ x → true) s ≡ s
filter-true = {!!}

filter-false : ∀ ⦃ _ : C ⦄ → ∀ { α } → ∀ { s : Stream α }
  → filter (λ x → false) s ≡ {!nil!}
filter-false = {!!}

filter-map : ∀ ⦃ _ : C ⦄ → ∀ { α β }
  → ∀ { s : Stream α } → ∀ { f : Expr β → Expr Bool } → ∀ { g : Expr α → Expr β }
  → filter f (map g s) ≡ map g (filter (f ∘ g) s)
filter-map = {!!}

-- TODO: zipWith

flatmap-assoc : ∀ ⦃ _ : C ⦄ → ∀ { α β }
  → ∀ { s : Stream α } → ∀ { f : Expr β → Stream α } → ∀ { g : Expr α → Stream β }
  → flatmap (λ x → flatmap f (g x)) s ≡ flatmap f (flatmap g s)
flatmap-assoc = {!!}

flatmap-map : ∀ ⦃ _ : C ⦄ → ∀ { α β γ }
  → ∀ { s : Stream α } → ∀ { f : Expr β → Stream γ } → ∀ { g : Expr α → Expr β }
  → flatmap f (map g s) ≡ flatmap (f ∘ g) s
flatmap-map = {!!}

map-flatmap : ∀ ⦃ _ : C ⦄ → ∀ { α β γ }
  → ∀ { s : Stream α } → ∀ { f : Expr β → Expr γ } → ∀ { g : Expr α → Stream β }
  → map f (flatmap g s) ≡ flatmap ((map f) ∘ g) s

--flatmap-filter : ∀ ⦃ _ : C ⦄ → ∀ { α β }
--  → ∀ { s : Stream α } → ∀ { f : Code α → Stream β } → ∀ { g : Code α → Code Bool }
--  → flatmap f (filter g s) ≅ flatmap (λ x → if g x then f x else nil) s

filter-flatmap : ∀ ⦃ _ : C ⦄ → ∀ { α β }
  → ∀ { s : Stream α } → ∀ { f : Expr β → Expr Bool } → ∀ { g : Expr α → Stream β }
  → filter f (flatmap g s) ≡ flatmap ((filter f) ∘ g) s
