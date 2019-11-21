open import Streams
open import C
open import Function
open import Relation.Binary
open import Level using (0ℓ)
open import Data.Unit
open import Data.Product using (_×_ ; _,_)

module Properties where

-- TODO: refactor into C.Properties and Streams.Properties

open C.C ⦃ ... ⦄

_≅_ : ∀ ⦃ _ : C ⦄ → ∀ { α } → Stream α → Stream α → Set
--_≅_ ⦃ impl ⦄ s t = ∀ { β f } → ∀ { u : C.Code impl β } → (fold f u s) ≅ᶜ (fold f u t)
infix 0 _≅_

-- C properties

β-if-true : ∀ ⦃ _ : C ⦄ → ∀ { x y : Code Void } → if true then x else y ≡ x
β-if-true = {!!}

β-if-false : ∀ ⦃ _ : C ⦄ → ∀ { x y : Code Void } → if false then x else y ≡ y
β-if-false = {!!}

η-if : ∀ ⦃ _ : C ⦄ → ∀ { cond : Code Bool } → ∀ { e : Code Void }
  → if cond then e else e ≡ e
η-if = {!!}

β-while : ∀ ⦃ _ : C ⦄ → ∀ { e₁ : Code Bool } → ∀ { e₂ : Code Void }
  → while e₁ then e₂ ≡ if e₁ then (e₂ ； while e₁ then e₂) else nop

-- Stream properties

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

flatmap-map : ∀ ⦃ _ : C ⦄ → ∀ { α β γ }
  → ∀ { s : Stream α } → ∀ { f : Code β → Stream γ } → ∀ { g : Code α → Code β }
  → flatmap f (map g s) ≅ flatmap (f ∘ g) s
flatmap-map = {!!}

map-flatmap : ∀ ⦃ _ : C ⦄ → ∀ { α β γ }
  → ∀ { s : Stream α } → ∀ { f : Code β → Code γ } → ∀ { g : Code α → Stream β }
  → map f (flatmap g s) ≅ flatmap ((map f) ∘ g) s

--flatmap-filter : ∀ ⦃ _ : C ⦄ → ∀ { α β }
--  → ∀ { s : Stream α } → ∀ { f : Code α → Stream β } → ∀ { g : Code α → Code Bool }
--  → flatmap f (filter g s) ≅ flatmap (λ x → if g x then f x else nil) s

filter-flatmap : ∀ ⦃ _ : C ⦄ → ∀ { α β }
  → ∀ { s : Stream α } → ∀ { f : Code β → Code Bool } → ∀ { g : Code α → Stream β }
  → filter f (flatmap g s) ≅ flatmap ((filter f) ∘ g) s
