open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable
import Level

module Print.FV where

open import C

c : C
C.Ref c _ = ℕ

toℕ : c_type → ℕ
toℕ Int = 0
toℕ Bool = 1
toℕ (Array α n) = (toℕ α) * (10 ^ n)

_⊑_ : Rel (∃ λ β → C.Ref c β) Level.zero
(α , x) ⊑ (β , y) = x < y ⊎ (x ≡ y × (toℕ α) < (toℕ β))

⊑-cmp : Trichotomous _≡_ _⊑_
⊑-cmp (α , x) (β , y) with <-cmp x y
... | tri< x+1≤y x≢y ¬y+1≤x =
  tri< (inj₁ x+1≤y) (λ { refl → x≢y refl })
    λ { (inj₁ y+1≤x) → ¬y+1≤x y+1≤x ; (inj₂ (y≡x , _)) → x≢y (sym y≡x) }
... | tri> ¬x+1≤y x≢y y+1≤x =
  tri> (λ { (inj₁ x+1≤y) → ¬x+1≤y x+1≤y ; (inj₂ (x≡y , _)) → x≢y x≡y })
    (λ { refl → x≢y refl }) (inj₁ y+1≤x)
... | tri≈ ¬x+1≤x refl ¬x+1≤x' with <-cmp (toℕ α) (toℕ β)
...     | tri< α+1≤β α≢β ¬β+1≤α = {!!}
...     | tri> ¬α+1≤β α≢β β+1≤α = {!!}
...     | tri≈ ¬α+1≤β α≡β ¬β+1≤α =
  tri≈
    (λ { (inj₁ x+1≤x) → ¬x+1≤x x+1≤x ; (inj₂ (_ , α+1≤β)) → ¬α+1≤β α+1≤β })
    {!!}
    λ { (inj₁ x+1≤x) → ¬x+1≤x x+1≤x ; (inj₂ (_ , β+1≤α)) → ¬β+1≤α β+1≤α }

isStrictTotalOrder : IsStrictTotalOrder _≡_ _⊑_
isStrictTotalOrder = record {
  isEquivalence = isEquivalence ;
  trans = {!<-trans!} ;
  compare = ⊑-cmp }

-- open import C.Properties.FreeVariables ⦃ c ⦄ isStrictTotalOrder

-- fv : FreeVariables
