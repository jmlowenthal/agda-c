open import Streams
open import C
open import Function
open import Relation.Binary
open import Level using (0ℓ)
open import Data.Unit
open import Data.Product using (_×_ ; _,_)

module Properties where

-- TODO: refactor into C.Properties and Streams.Properties

_≅ᶜ_ : ∀ ⦃ impl : C ⦄ → ∀ { α β } → C.Code impl α → C.Code impl β → Set
_≅ᶜ_ = {!!}

_≅_ : ∀ ⦃ _ : C ⦄ → ∀ { α } → Stream α → Stream α → Set
_≅_ ⦃ impl ⦄ s t = ∀ { β f } → ∀ { u : C.Code impl β } → (fold f u s) ≅ᶜ (fold f u t)

open C.C ⦃ ... ⦄

map-map : ∀ ⦃ _ : C ⦄ → ∀ { α β γ }
  → ∀ { s : Stream α } → ∀ { f : Code β → Code γ } → ∀ { g : Code α → Code β }
  → map f (map g s) ≅ map (f ∘ g) s
map-map = {!!}

map-id : ∀ ⦃ _ : C ⦄ → ∀ { α } → ∀ { s : Stream α } → map id s ≅ s
map-id = {!!}

filter-filter : ∀ ⦃ _ : C ⦄ → ∀ { α }
  → ∀ { s : Stream α } → ∀ { f : Code α → Code Bool } → ∀ { g : Code α → Code Bool }
  → filter f (filter g s) ≅ filter (λ x → f x && g x) s
filter-filter = {!!}

filter-true : ∀ ⦃ _ : C ⦄ → ∀ { α } → ∀ { s : Stream α } → filter (λ x → true) s ≅ s
filter-true = {!!}

filter-false : ∀ ⦃ _ : C ⦄ → ∀ { α } → ∀ { s : Stream α }
  → filter (λ x → false) s ≅ {!nil!}
filter-false = {!!}

filter-map : ∀ ⦃ _ : C ⦄ → ∀ { α β }
  → ∀ { s : Stream α } → ∀ { f : Code β → Code Bool } → ∀ { g : Code α → Code β }
  → filter f (map g s) ≅ map g (filter (f ∘ g) s)
filter-map = {!!}

-- TODO: zipWith

flatmap-assoc : ∀ ⦃ _ : C ⦄ → ∀ { α β }
  → ∀ { s : Stream α } → ∀ { f : Code β → Stream α } → ∀ { g : Code α → Stream β }
  → flatmap (λ x → flatmap f (g x)) s ≅ flatmap f (flatmap g s)
flatmap-assoc = {!!}
