module _ where

open import Codata.Musical.Notation
open import Codata.Musical.Colist
open import Codata.Musical.Conat
open import Data.Maybe
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Data.BoundedVec.Inefficient
import Level

data Empty { a } { A : Set a } : Colist (Maybe A) → Set where
  [] : Empty []
  step : ∀ { t } → ∞ (Empty (♭ t)) → Empty (nothing ∷ t)

data BoundedAny {a} {A : Set a} : ∀ { n } → BoundedVec (Maybe A) n → Set a where
  here : ∀ { n } { xs : BoundedVec _ n } (x : A) → BoundedAny (just x ∷ xs)
  there : ∀ { n } { xs : BoundedVec _ n } → BoundedAny xs → BoundedAny (nothing ∷ xs)

drop : ∀ {a} {A : Set a} → ℕ → Colist A → Colist A
drop zero l = l
drop (suc n) [] = []
drop (suc n) (x ∷ xs) = drop n (♭ xs)

data Filterable { a } { A : Set a } : Colist (Maybe A) → Set a where
  empty : ∀ { l } → Empty l → Filterable l
  _⊢_∷_ : ∀ { l } n → BoundedAny (take n l) → ∞ (Filterable (drop n l)) → Filterable l

filter : ∀ { a } { A : Set a } (l : Colist (Maybe A)) → Filterable l → Colist A
filter _ (empty _) = []
filter l (suc n ⊢ x ∷ xs) = get x ∷ ♯ (filter (drop (suc n) l) (♭ xs))
  where
    get : ∀ { a n } { A : Set a } { l : BoundedVec (Maybe A) n } → BoundedAny l → A
    get (here x) = x
    get (there l) = get l

Finite⇒Filterable : ∀ {a} {A : Set a} {l : Colist (Maybe A)} → Finite l → Filterable l
Finite⇒Filterable [] = empty []
Finite⇒Filterable (just x ∷ p) = 1 ⊢ here x ∷ (♯ Finite⇒Filterable p)
Finite⇒Filterable (nothing ∷ p) with Finite⇒Filterable p
... | empty x = empty (step (♯ x))
... | n ⊢ h ∷ t = (suc n) ⊢ there h ∷ t

filter' : ∀ { a } { A : Set a } (l : Colist (Maybe A)) → Finite l → Colist A
filter' l p = filter l (Finite⇒Filterable p)
