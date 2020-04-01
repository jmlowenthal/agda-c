open import C.Base
open import Streams.Base 
open import Data.Product using (_×_ ; _,_)
open import Function
open import Function.Nary.NonDependent
open import Relation.Binary.PropositionalEquality
open import Data.Nat as ℕ using (ℕ)
open import Data.Nat.Properties

module Streams.Claims ⦃ _ : C ⦄ where

open C ⦃ ... ⦄

-- Claim that two streams are equivalent
Claim : Set → Set₁
Claim α = SStream α × SStream α 

-- Claim that two programs are equivalent
Claimₚ : ∀ { n } { l : Levels n } { v : Sets n l } → Set (⨆ n l)
Claimₚ {v = v} = (v ⇉ Statement) × (v ⇉ Statement)

map'≅map : ∀ { α β } → (α → Expr β) → SStream α → Claim (Expr β)
map'≅map f s = map' f s , map f s

-- TODO: generalise map properties and use map'≅map to conclude any specialisations.

map-map : ∀ { α β γ } → SStream α → (Expr β → Expr γ) → (α → Expr β) → Claim (Expr γ)
map-map s f g = map f (map g s) , map (f ∘ g) s

map-id : ∀ { α } → Stream α → Claim (Expr α)
map-id s = map id s , s

filter-filter : ∀ { α } → SStream α → (α → Expr Bool) → (α → Expr Bool) → Claim α
filter-filter s f g = filter f (filter g s) , filter (λ x → f x && g x) s

filter-true : ∀ { α } → SStream α → Claim α
filter-true s = filter (λ x → true) s , s

filter-false : ∀ { α } → SStream α → Claim α
filter-false s = filter (λ x → false) s , nil

filter-map : ∀ { α β } → SStream α → (Expr β → Expr Bool) → (α → Expr β) → Claim (Expr β)
filter-map s f g = filter f (map g s) , map g (filter (f ∘ g) s)

-- TODO: zipWith

flatmap-assoc : ∀ { α β γ } → SStream α → (β → SStream γ) → (α → SStream β) → Claim γ
flatmap-assoc s f g = flatmap (λ x → flatmap f (g x)) s , flatmap f (flatmap g s)

flatmap-map : ∀ { α β γ } → SStream α → (Expr β → SStream γ) → (α → Expr β) → Claim γ
flatmap-map s f g = flatmap f (map g s) , flatmap (f ∘ g) s

map-flatmap : ∀ { α β γ } → SStream α → (β → Expr γ) → (α → SStream β) → Claim (Expr γ)
map-flatmap s f g = map f (flatmap g s) , flatmap ((map f) ∘ g) s

flatmap-filter : ∀ { α β } → Stream α → (Expr α → Stream β) → (Expr α → Expr Bool)
  → Claim (Expr β)
flatmap-filter s f g = flatmap f (filter g s) , flatmap (λ x → filter (λ _ → g x) (f x)) s

filter-flatmap : ∀ { α β } → SStream α → (β → Expr Bool) → (α → SStream β) → Claim β
filter-flatmap s f g = filter f (flatmap g s) , flatmap ((filter f) ∘ g) s

-- _ : ∀ { α ζ } { f : Expr ζ → Expr α → Expr ζ } { z : Expr ζ }
--   → (fold f z nil ≅ₚ (λ r → r ≔ z))
--     × (∀ s → ¬ (s ≅ nil) → fold f z s ≅ₚ
--          (λ r → r ← fold f z {!tail s!} ； r ≔ f  (★ r) {!head s!}))

fold-map : ∀ { α ζ β } → (Expr ζ → Expr α → Expr ζ) → Expr ζ
  → (Expr β → Expr α) → Stream β → Claimₚ
fold-map f z g s = fold f z (map g s) , fold (λ x y → f x (g y)) z s

fold-filter : ∀ { α ζ } → (Expr ζ → Expr α → Expr ζ) → Expr ζ → (Expr α → Expr Bool)
  → Stream α → Claimₚ
fold-filter f z g s = fold f z (filter g s) , fold (λ x y → g y ⁇ f x y ∷ x) z s

-- fold-flatmap : ∀ { α ζ β } → (Expr ζ → α → Expr ζ) → Expr ζ → (β → SStream α)
--   → SStream β → Claimₚ
-- fold-flatmap f z g s = fold f z (flatmap g s) , {!!}

-- fold-unfold : ∀ { α ζ ξ } → (Expr ζ → Expr α → Expr ζ) → Expr ζ → (Expr ξ → (Expr Bool × Expr α × Expr ξ)) → Expr ξ → Claimₚ
-- fold-unfold f z g x = fold f z (unfold g x) , {!!}

-- fold-take : ∀ { α ζ } → (Expr ζ → Expr α → Expr ζ) → Expr ζ → Expr Int → Stream α → Claimₚ
-- fold-take f z n s = fold f z (take n s) , fold {!λ { (x , m) y → {!with m < n | true = (f x y , m + 1) | false = (y , m + 1)!} }!} z s

map-preserves-size : ∀ { α β } (s : SStream α) (f : α → β) → ∥ map' f s ∥ₛ ≡ ∥ s ∥ₛ
map-preserves-size (linear (producer (_ , for _))) _ = refl
map-preserves-size (linear (producer (_ , unfolder _))) _ = refl
map-preserves-size (nested _) _ = refl

maps-can-zip : ∀ { α β α' β' } (s : SStream α) (t : SStream β) (f : α → α') (g : β → β')
  → ∥ s ∥ₛ ℕ.+ ∥ t ∥ₛ ℕ.≤ 1 → ∥ map' f s ∥ₛ ℕ.+ ∥ map' g t ∥ₛ ℕ.≤ 1
maps-can-zip s t f g p =
  ≤-trans
    (+-mono-≤
      (≤-reflexive (map-preserves-size s f))
      (≤-reflexive (map-preserves-size t g)))
    p
    
zip-map : ∀ { α β α' β' } (s : SStream α) (t : SStream β) → (α → α') → (β → β')
  → ∥ s ∥ₛ ℕ.+ ∥ t ∥ₛ ℕ.≤ 1 → Claim (α' × β')
zip-map s t f g p = zip (map' f s) (map' g t) {maps-can-zip s t f g p} , map' (λ { (x , y) → f x , g y }) (zip s t {p})

