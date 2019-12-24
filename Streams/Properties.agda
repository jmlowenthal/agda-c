open import Streams.Base
open import C
open import C.Properties.ReductionSemantics
open import Function
open import Function.Nary.NonDependent
open import Relation.Binary
open import Level using (0ℓ)
open import Data.Unit
open import Data.Vec using (Vec ; _∷_ ; [])
open import Data.Product using (_×_ ; _,_)
open import Relation.Binary.PropositionalEquality
import Data.Integer as ℤ

module Streams.Properties ⦃ _ : C ⦄ ⦃ _ : Semantics ⦄ where

open C.C ⦃ ... ⦄
open Semantics ⦃ ... ⦄

infix 0 _≅_
_≅_ : ∀ { α } → Rel (Stream α) 0ℓ
_≅_ {α} s t = ∀ { β } → (f : Expr β → Expr α → Expr β) → ∀ { z x }
  → fold f z s x ≅ₚ fold f z t x

≅-equiv : ∀ { α } → IsEquivalence (_≅_ {α})
≅-equiv {α} = record {
  refl = λ {s} f {z} {x} {k} {E} → IsEquivalence.refl ≅ₚ-equiv {fold f z s x} {k} {E} ;
  trans = λ A B f → IsEquivalence.trans (≅ₚ-equiv {v = []}) (A f) (B f) ;
  sym = λ A f → IsEquivalence.sym (≅ₚ-equiv {v = []}) (A f) }

≅ₚ-setoid : ∀ { n } { v : Vec Set n } → Setoid _ _
≅ₚ-setoid {v = v} = record {
  Carrier = Closure v ;
  _≈_ = _≅ₚ_ ;
  isEquivalence = ≅ₚ-equiv }

import Relation.Binary.Reasoning.Setoid as Reasoning
open module ≅-Reasoning = Reasoning (≅ₚ-setoid {v = []})
  renaming (_≈⟨_⟩_ to _≅⟨_⟩_ ; _≈˘⟨_⟩_ to _≅˘⟨_⟩_) public

decl-elim : ∀ { α } { f : Statement } → (decl α λ x → f) ≅ₚ f

map-map : ∀ { α β γ }
  → ∀ { s : Stream α } → ∀ { f : Expr β → Expr γ } → ∀ { g : Expr α → Expr β }
  → map f (map g s) ≅ map (f ∘ g) s
map-map = {!!}

≅-cong : ∀ { α } (β : Set) { a b : β → Statement } → (F : (β → Statement) → Stream α) → ((i : β) → a i ≅ₚ b i) → F a ≅ F b
≅-cong {α} β {a} {b} F a≅b f {z} {x} = {!!}

decl-cong : ∀ { α } { f g : Ref α → Statement }
  → (∀ (r : Ref α) → f r ≅ₚ g r) → (decl α f) ≅ₚ (decl α g)

postulate ≅-cong : ∀ { α } { A : Set } (f : (A → Stream α) → Stream α) (x y : A → Stream α) → (∀ i → x i ≅ y i) → f x ≅ f y

map-id : ∀ { α } → ∀ { s : Stream α } → map id s ≅ s
map-id {α} {s@(linear (producer (init , for (bound , index))))} F {z} {x} =
  let wrap : (_ → Expr Int → (Expr α → Statement) → Statement) → Statement
      wrap index = fold F z (linear (producer (init , for (bound , index)))) x
      index' f s i k = index s i (f k)
  in
  begin
    fold F z (map id s) x
    ≡⟨⟩
    wrap (index' (λ k e → decl α λ t → t ≔ id e ； k (★ t)))
    ≡⟨⟩
    wrap (index' (λ k e → decl α λ t → t ≔ e ； k (★ t)))
    ≅⟨
      ≅ₚ-cong
      {v = (Expr α → Statement) ∷ Expr α ∷ Ref α ∷ []}
      {w = []}
      (λ s → wrap (index' (λ k e → decl α λ t → s k e t)))
      (λ k e t → t ≔ e ； k (★ t))
      (λ k e t → k e)
      ≔-subst
    ⟩
    wrap (index' (λ k e → decl α λ t → k e))
    ≅⟨
      ≅ₚ-cong
      {v = (Expr α → Statement) ∷ Expr α ∷ []}
      {w = []}
      (λ s → wrap (index' (λ k e → s k e)))
      (λ k e → decl α λ t → k e)
      (λ k e → k e)
      decl-elim
    ⟩
    wrap (index' (λ k e → k e))
    ≡⟨⟩
    wrap index
    ≡⟨⟩
    fold F z s x
  ∎
map-id {α} {s@(linear (producer (init , unfolder (term , card , step))))} F {z} {x} =
  let wrap : (_ → (Expr α → Statement) → Statement) → Statement
      wrap step = fold F z (linear (producer (init , unfolder (term , card , step)))) x
      step' f s k = step s (f k)
  in    
    begin
      fold F z (map id s) x
      ≡⟨⟩
      wrap (step' (λ k e → decl α λ t → t ≔ id e ； k (★ t)))
      ≡⟨⟩
      wrap (step' (λ k e → decl α λ t → t ≔ e ； k (★ t)))
      ≅⟨ 
        ≅ₚ-cong
        {v = (Expr α → Statement) ∷ Expr α ∷ Ref α ∷ []}
        {w = []}
        (λ s → wrap (step' (λ k e → decl α λ t → s k e t)))
        (λ k e t → t ≔ e ； k (★ t))
        (λ k e t → k e)
        ≔-subst
      ⟩
      wrap (step' (λ k e → decl α λ t → k e))
      ≅⟨
        ≅ₚ-cong
        {v = (Expr α → Statement) ∷ Expr α ∷ []}
        {w = []}
        (λ s → wrap (step' (λ k e → s k e)))
        (λ k e → decl α λ t → k e)
        (λ k e → k e)
        decl-elim
      ⟩
      wrap (step' (λ k e → k e))
      ≡⟨⟩
      wrap step
      ≡⟨⟩
      fold F z s x
    ∎
map-id {α} {s@(nested (p , f))} F {z} {x} =
  begin
    fold F z (map id s) x
    ≡⟨⟩
    fold F z (nested (p , (λ a → map id (f a)))) x
    ≅⟨
      ≅-cong
      (λ s → nested (p , (λ a → s a)))
      (λ a → map id (f a))
      (λ a → f a)
      (λ i → map-id {s = f i})
      F
    ⟩
    fold F z (nested (p , (λ a → f a))) x
    ≡⟨⟩
    fold F z s x
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
