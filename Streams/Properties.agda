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

postulate ≅-cong : ∀ { α } { A : Set } (f : (A → Stream α) → Stream α) (x y : A → Stream α) → (∀ i → x i ≅ y i) → f x ≅ f y

map-map : ∀ { α β γ }
  → ∀ { s : Stream α } → ∀ { f : Expr β → Expr γ } → ∀ { g : Expr α → Expr β }
  → map f (map g s) ≅ map (f ∘ g) s
map-map {α} {β} {γ} {s@(linear (producer (init , for (bound , index))))} {f} {g} F {z} {x} =
  let wrap : ∀ {τ} → (_ → Expr Int → (Expr τ → Statement) → Statement) → Stream τ
      wrap index = linear (producer (init , for (bound , index)))
  in
  begin
    fold F z (map f (map g s)) x
    ≡⟨⟩
    fold F z (
      map f (wrap λ s i k →
        index s i (λ e →
          decl β λ t →
          t ≔ g e ；
          k (★ t)))
    ) x
    ≡⟨⟩
    fold F z (
      wrap λ s i k →
        (λ s i k →
          index s i (λ e →
            decl β λ t →
            t ≔ g e ；
            k (★ t))
        )
        s
        i
        (λ e →
          decl γ λ t →
          t ≔ f e ；
          k (★ t))
    ) x
    ≡⟨⟩
    fold F z (
      wrap λ s i k →
        index s i (λ e →
          decl β λ t₁ →
          t₁ ≔ g e ；
          decl γ λ t₂ →
          t₂ ≔ f (★ t₁) ；
          k (★ t₂))
    ) x
    ≅⟨
      ≅ₚ-cong
      {v = (Expr γ → Statement) ∷ Expr α ∷ Ref β ∷ []}
      {w = []}
      (λ c → fold F z (wrap λ s i k → index s i (λ e → decl β λ t₁ → c k e t₁)) x)
      (λ k e t₁ → t₁ ≔ g e ； decl γ λ t₂ → t₂ ≔ f (★ t₁) ； k (★ t₂))
      (λ k e t₁ → decl γ λ t₂ → t₂ ≔ f (g e) ； k (★ t₂))
      (≔-subst {f = (λ ★t₁ → decl γ λ t₂ → t₂ ≔ f ★t₁ ； _)})
    ⟩
    fold F z (
      wrap λ s i k →
        index s i (λ e →
          decl β λ t₁ →
          decl γ λ t₂ →
          t₂ ≔ f (g e) ；
          k (★ t₂))
    ) x
    ≅⟨
      ≅ₚ-cong
      {v = (Expr γ → Statement) ∷ Expr α ∷ []}
      {w = []}
      (λ c → fold F z (wrap (λ s i k → index s i (λ e → c k e))) x)
      (λ k e → decl β λ t₁ → decl γ λ t₂ → t₂ ≔ f (g e) ； k (★ t₂))
      (λ k e → decl γ λ t → t ≔ f (g e) ； k (★ t))
      decl-elim
    ⟩
    fold F z (
      wrap λ s i k →
        index s i (λ e →
          decl γ λ t →
          t ≔ f (g e) ；
          k (★ t))
    ) x
    ≡⟨⟩
    fold F z (map (f ∘ g) s) x
  ∎
map-map {α} {β} {γ} {s@(linear (producer (init , unfolder (term , card , step))))} {f} {g} F {z} {x} =
  let wrap : ∀ {τ} → (_ → (Expr τ → Statement) → Statement) → Stream τ
      wrap step = linear (producer (init , unfolder (term , card , step)))
  in
  begin
    fold F z (map f (map g s)) x
    ≡⟨⟩
    fold F z (
      map f (wrap λ s k →
        step s (λ e →
          decl β λ t →
          t ≔ g e ；
          k (★ t)))
    ) x
    ≡⟨⟩
    fold F z (
      wrap λ s k →
        (λ s k →
          step s (λ e →
            decl β λ t →
            t ≔ g e ；
            k (★ t))
        )
        s
        (λ e →
          decl γ λ t →
          t ≔ f e ；
          k (★ t))
    ) x
    ≡⟨⟩
    fold F z (
      wrap λ s k →
        step s (λ e →
          decl β λ t₁ →
          t₁ ≔ g e ；
          decl γ λ t₂ →
          t₂ ≔ f (★ t₁) ；
          k (★ t₂))
    ) x
    ≅⟨
      ≅ₚ-cong
      {v = (Expr γ → Statement) ∷ Expr α ∷ Ref β ∷ []}
      {w = []}
      (λ c → fold F z (wrap λ s k → step s (λ e → decl β λ t₁ → c k e t₁)) x)
      (λ k e t₁ → t₁ ≔ g e ； decl γ λ t₂ → t₂ ≔ f (★ t₁) ； k (★ t₂))
      (λ k e t₁ → decl γ λ t₂ → t₂ ≔ f (g e) ； k (★ t₂))
      (≔-subst {f = (λ ★t₁ → decl γ λ t₂ → t₂ ≔ f ★t₁ ； _)})
    ⟩
    fold F z (
      wrap λ s k →
        step s (λ e →
          decl β λ t₁ →
          decl γ λ t₂ →
          t₂ ≔ f (g e) ；
          k (★ t₂))
    ) x
    ≅⟨
      ≅ₚ-cong
      {v = (Expr γ → Statement) ∷ Expr α ∷ []}
      {w = []}
      (λ c → fold F z (wrap (λ s k → step s (λ e → c k e))) x)
      (λ k e → decl β λ t₁ → decl γ λ t₂ → t₂ ≔ f (g e) ； k (★ t₂))
      (λ k e → decl γ λ t → t ≔ f (g e) ； k (★ t))
      decl-elim
    ⟩
    fold F z (
      wrap λ s k →
        step s (λ e →
          decl γ λ t →
          t ≔ f (g e) ；
          k (★ t))
    ) x
    ≡⟨⟩
    fold F z (map (f ∘ g) s) x
  ∎
map-map {α} {β} {γ} {s@(nested (p , gen))} {f} {g} F {z} {x} =
  begin
    fold F z (map f (map g s)) x
    ≡⟨⟩
    fold F z (map f (nested (p , (λ a → map g (gen a))))) x
    ≡⟨⟩
    fold F z (nested (p , λ a → map f (map g (gen a)))) x
    ≅⟨
      ≅-cong
      (λ s → nested (p , λ a → s a))
      (λ a → map f (map g (gen a)))
      (λ a → map (f ∘ g) (gen a))
      (λ i → map-map {α} {β} {γ} {gen _} {f} {g})
      F
    ⟩
    fold F z (nested (p , λ a → map (f ∘ g) (gen a))) x
    ≡⟨⟩
    fold F z (map (f ∘ g) s) x
  ∎

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
filter-true {α} {s@(linear prod)} F {z} {x} =
  begin
    fold F z (filter (λ _ → true) s) x
    ≡⟨⟩ -- by definition of filter
    fold F z (
      nested (
        prod ,
        λ x →
          linear (
            producer (
              (λ k → k x) ,
              unfolder (
                (λ a r → r ≔ (λ _ → true) a) ,
                atMost1 ,
                λ a k → k a))))) x
    ≡⟨⟩ -- by definition of fold
    (
    x ≔ z ；
    fold' (λ e →
      fold'
        (λ a → x ≔ F (★ x) a)
        (linear (
          producer (
            (λ k → k e) ,
            unfolder (
              (λ a r → r ≔ true) ,
              atMost1 ,
              λ a k → k a)))))
      s
    )
    ≡⟨⟩ -- by definition of fold'
    (
    x ≔ z ；
    fold' (λ e →
      (λ k → k e) λ sp →
        decl Bool λ cond →
        (λ a r → r ≔ true) sp cond ；
        if ★ cond then
          (λ a k → k a) sp (λ a → x ≔ F (★ x) a)
        else
          nop) s
    )
    ≡⟨⟩ -- by function application
    (
    x ≔ z ；
    fold' (λ e →
      decl Bool λ cond →
      cond ≔ true ；
      if ★ cond then
        x ≔ F (★ x) e
      else
        nop) s
    )
    ≅⟨
      ≅ₚ-cong
      {v = Ref Bool ∷ Expr α ∷ []}
      {w = []}
      (λ S → x ≔ z ； fold' (λ e → decl Bool λ cond → S cond e) s)
      (λ cond e → cond ≔ true ； if ★ cond then x ≔ F (★ x) e else nop)
      (λ cond e → if true then x ≔ F (★ x) e else nop)
      (≔-subst {f = λ ★cond → if ★cond then _ else _})
    ⟩
    (
    x ≔ z ；
    fold' (λ e →
      decl Bool λ cond →
      if true then
        x ≔ F (★ x) e
      else
        nop) s
    )
    ≅⟨
      ≅ₚ-cong
      {v = Ref Bool ∷ Expr α ∷ []}
      {w = []}
      (λ S → x ≔ z ； fold' (λ e → decl Bool λ cond → S cond e) s)
      (λ cond e → if true then x ≔ F (★ x) e else _)
      (λ cond e → x ≔ F (★ x) e)
      β-if-true
    ⟩
    (
    x ≔ z ；
    fold' (λ e →
      decl Bool λ cond →
      x ≔ F (★ x) e) s
    )
    ≅⟨
      ≅ₚ-cong
      {v = Expr α ∷ []}
      {w = []}
      (λ S → x ≔ z ； fold' S s)
      (λ e → decl Bool λ cond → x ≔ F (★ x) e)
      (λ e → x ≔ F (★ x) e)
      decl-elim
    ⟩
    (
    x ≔ z ；
    fold' (λ a → x ≔ F (★ x) a) s
    )
    ≡⟨⟩ -- by definition of fold
    fold F z s x
  ∎
filter-true {α} {s@(nested (prod , f))} F {z} {x} =
  begin
    fold F z (filter (λ _ → true) s) x
    ≡⟨⟩ -- by definition of filter
    fold F z (
      nested (
        prod ,
        λ a → filter (λ _ → true) (f a))) x
    ≅⟨
      ≅-cong
      (λ S → nested (prod , λ a → S a))
      (λ a → filter (λ _ → true) (f a))
      (λ a → f a)
      (λ a → filter-true {s = f a})
      F
    ⟩
    fold F z (nested (prod , λ a → f a)) x
    ≡⟨⟩ -- by (λ a → f a) ≡ f
    fold F z s x
  ∎

filter-false : ∀ { α } → ∀ { s : Stream α }
  → filter (λ x → false) s ≅ {!!}
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
