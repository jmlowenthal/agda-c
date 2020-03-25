open import C
open import C.Properties.Properties
open import C.Properties.Musical

open import Data.Integer as ℤ using (ℤ)
open import Data.Nat as ℕ using (ℕ)
open import Data.Nat.Properties
open import Data.Product using (_×_ ; _,_)
open import Data.Unit
open import Data.Vec using (Vec ; _∷_ ; [])
open import Function
open import Function.Nary.NonDependent
open import Level using (0ℓ)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Streams.Base

import Data.Bool.Properties as BoolP

module Streams.Properties ⦃ _ : C ⦄ ⦃ _ : Semantics ⦄ where

open C.C ⦃ ... ⦄
open Semantics ⦃ ... ⦄
open ≅-Reasoning

infix 0 _≅_
_≅_ : ∀ { α } { n } { V : Sets n L0 } → Rel (V ⇉ SStream α) 0ℓ
_≅_ {α} {0} s t = ∀ { β } → (f : Expr β → α → Expr β) → ∀ { z x }
  → fold f z s x ≅ₚ fold f z t x
_≅_ {α} {ℕ.suc n} {H , T} s t = ∀ { h : H } → _≅_ {α} {n} {T} (s h) (t h)

≅-equiv : ∀ { α } → IsEquivalence (_≅_ {α} {0})
≅-equiv {α} = record {
  refl = λ {s} f {z} {x} {k} {E} → IsEquivalence.refl ≅ₚ-equiv {fold f z s x} {k} {E} ;
  trans = λ A B f → IsEquivalence.trans (≅ₚ-equiv {0}) (A f) (B f) ;
  sym = λ A f → IsEquivalence.sym (≅ₚ-equiv {0}) (A f) }

postulate ≅-cong : ∀ { n } { V : Sets n L0 } { α } (f : (V ⇉ SStream α) → SStream α) (x y : V ⇉ SStream α) → x ≅ y → f x ≅ f y

-- Both maps are equivalent, map is just a more efficient specialisation
map'≅map : ∀ { α β } { f : α → Expr β } { s : SStream α } → map' f s ≅ map f s
map'≅map {α} {β} {f} {s} F {z} {x} =
  begin
    fold F z (map' f s) x
    ≡⟨⟩
    fold F z (mapRaw (λ a k → k (f a)) s) x
    ≅˘⟨ 
      ≅ₚ-cong
        {2}
        {α , (Expr β → Statement) , _}
        (λ body → fold F z (mapRaw (λ a k → body a k) s) x)
        (λ a k → decl β λ t → k (f a))
        (λ a k → k (f a))
        decl-elim ⟩
    fold F z (mapRaw (λ a k → decl β λ t → k (f a)) s) x
    ≅˘⟨
      ≅ₚ-cong
        {3}
        {α , (Expr β → Statement) , Ref β , _}
        (λ body → fold F z (mapRaw (λ a k → decl β λ t → body a k t) s) x)
        (λ a k t → t ≔ f a ； k (★ t))
        (λ a k t → k (f a))
        (λ {a} {k} {t} → ≔-subst {f = λ e → k e})
    ⟩
    fold F z (mapRaw (λ a k → decl β λ t → t ≔ f a ； k (★ t)) s) x
    ≡⟨⟩
    fold F z (map f s) x
  ∎

-- TODO: generalise map properties and use map'≅map to conclude this specialisations

map-map : ∀ { α β γ } { s : SStream α } { f : Expr β → Expr γ } { g : α → Expr β }
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
      {3}
      {(Expr γ → Statement) , α , Ref β , _}
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
      {2}
      {(Expr γ → Statement) , α , _}
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
      {3}
      {(Expr γ → Statement) , α , Ref β , _}
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
      {2}
      {(Expr γ → Statement) , α , _}
      (λ c → fold F z (wrap (λ s k → step s (λ e → c k e))) x)
      (λ k e → decl β λ t₁ → decl γ λ t₂ → t₂ ≔ f (g e) ； k (★ t₂))
      (λ k e → decl γ λ t → t ≔ f (g e) ； k (★ t))
      (decl-elim)
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
      (map-map {α} {β} {γ} {gen _} {f} {g})
      F
    ⟩
    fold F z (nested (p , λ a → map (f ∘ g) (gen a))) x
    ≡⟨⟩
    fold F z (map (f ∘ g) s) x
  ∎

map-id : ∀ { α } { s : Stream α } → map id s ≅ s
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
      {3}
      {(Expr α → Statement) , Expr α , Ref α , _}
      (λ s → wrap (index' (λ k e → decl α λ t → s k e t)))
      (λ k e t → t ≔ e ； k (★ t))
      (λ k e t → k e)
      ≔-subst
    ⟩
    wrap (index' (λ k e → decl α λ t → k e))
    ≅⟨
      ≅ₚ-cong
      {2}
      {(Expr α → Statement) , Expr α , _}
      (λ s → wrap (index' (λ k e → s k e)))
      (λ k e → decl α λ t → k e)
      (λ k e → k e)
      (decl-elim)
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
        {3}
        {(Expr α → Statement) , Expr α , Ref α , _}
        (λ s → wrap (step' (λ k e → decl α λ t → s k e t)))
        (λ k e t → t ≔ e ； k (★ t))
        (λ k e t → k e)
        ≔-subst
      ⟩
      wrap (step' (λ k e → decl α λ t → k e))
      ≅⟨
        ≅ₚ-cong
        {2}
        {(Expr α → Statement) , Expr α , _}
        (λ s → wrap (step' (λ k e → s k e)))
        (λ k e → decl α λ t → k e)
        (λ k e → k e)
        (decl-elim)
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
      (λ {i} → map-id {s = f i})
      F
    ⟩
    fold F z (nested (p , (λ a → f a))) x
    ≡⟨⟩
    fold F z s x
  ∎

filter-filter : ∀ { α } { s : SStream α } { f : α → Expr Bool } { g : α → Expr Bool }
  → filter f (filter g s) ≅ filter (λ x → f x && g x) s
filter-filter {α} {s@(linear prod)} {f} {g} F {z} {acc} =
  begin
    fold F z (filter f (filter g s)) acc
    ≡⟨⟩ -- by definition of filter
    fold F z (
      filter f (
        nested (
          prod ,
          λ x →
            linear (
              producer (
                (λ k → k x) ,
                unfolder (
                  (λ a r → r ≔ g a) ,
                  atMost1 ,
                  (λ a k → k a))))))) acc
    ≡⟨⟩ -- by definition of filter
    fold F z (
      nested (
        prod ,
        λ x →
          nested (
            producer (
                (λ k → k x) ,
                unfolder (
                  (λ a r → r ≔ g a) ,
                  atMost1 ,
                  (λ a k → k a))) ,
            λ y →
              linear (
                producer (
                  (λ k → k y) ,
                  unfolder (
                    (λ a r → r ≔ f a) ,
                    atMost1 ,
                    (λ a k → k a))))))) acc
    ≡⟨⟩ -- by definition of fold
    (
    acc ≔ z ；
    iter
      (λ e →
        iter
          (λ e' →
            iter
              (λ a → acc ≔ F (★ acc) a)
              (linear (
                producer (
                  (λ k → k e') ,
                  unfolder (
                    (λ a r → r ≔ f a) ,
                    atMost1 ,
                    (λ a k → k a))))))
          (linear (
            producer (
              (λ k → k e) ,
              unfolder (
                (λ a r → r ≔ g a) ,
                atMost1 ,
                (λ a k → k a))))))
      (linear prod)
    )
    ≡⟨⟩ -- by definition of iter    
    (
    acc ≔ z ；
    iter
      (λ e →
        iter
          (λ e' →
            decl Bool λ cond →
            cond ≔ f e' ；
            if ★ cond then
              acc ≔ F (★ acc) e'
            else nop)
          (linear (
            producer (
              (λ k → k e) ,
              unfolder (
                (λ a r → r ≔ g a) ,
                atMost1 ,
                (λ a k → k a))))))
      (linear prod)
    )
    ≡⟨⟩ -- by definition of iter
    (
    acc ≔ z ；
    iter
      (λ e →
        decl Bool λ cond' →
        cond' ≔ g e ；
        if ★ cond' then (
           decl Bool λ cond →
           cond ≔ f e ；
           if ★ cond then
             acc ≔ F (★ acc) e
           else nop
        )
        else nop)
      (linear prod)
    )
    ≅⟨
      ≅ₚ-cong
        {2}
        {Ref Bool , α , _}
        (λ body →
          acc ≔ z ；
          iter
            (λ e →
              decl Bool λ cond' →
              cond' ≔ g e ；
              if ★ cond' then (
                decl Bool λ cond →
                body cond e
              )
              else nop)
            (linear prod))
        (λ cond e → cond ≔ f e ； if ★ cond then _ else nop)
        (λ cond e → if (f e) then _ else nop)
        (≔-subst {f = λ e → if e then acc ≔ _ else nop})
    ⟩
    (
    acc ≔ z ；
    iter
      (λ e →
        decl Bool λ cond' →
        cond' ≔ g e ；
        if ★ cond' then (
           decl Bool λ cond →
           if (f e) then
             acc ≔ F (★ acc) e
           else nop
        )
        else nop)
      (linear prod)
    )
    ≅⟨
      ≅ₚ-cong
        {2}
        {Ref Bool , α , _}
        (λ body → acc ≔ z ； iter (λ e → decl Bool λ cond' → body cond' e) (linear prod))
        (λ cond' e → cond' ≔ g e ； if ★ cond' then _ else nop)
        (λ cond' e → if g e then _ else nop)
        (≔-subst {f = λ e → if e then _ else nop})
    ⟩
    (
    acc ≔ z ；
    iter
      (λ e →
        decl Bool λ cond' →
        if g e then (
           decl Bool λ cond →
           if (f e) then
             acc ≔ F (★ acc) e
           else nop
        )
        else nop)
      (linear prod)
    )
    ≅⟨
      ≅ₚ-cong
        {1}
        {α , _}
        (λ body →
          acc ≔ z ；
          iter (λ e →
            decl Bool λ cond' →
            if g e then body e else nop)
          (linear prod))
        (λ e → decl Bool λ cond → if (f e) then _ else nop)
        (λ e → if (f e) then _ else nop)
        decl-elim
    ⟩
    (
    acc ≔ z ；
    iter
      (λ e →
        decl Bool λ cond' →
        if g e then (
           if (f e) then
             acc ≔ F (★ acc) e
           else nop
        )
        else nop)
      (linear prod)
    )
    ≅⟨
      ≅ₚ-cong
      {1}
      {α , _}
      (λ body → acc ≔ z ； iter body (linear prod))
      (λ e → decl Bool λ cond' → if g e then _ else nop)
      (λ e → if g e then _ else nop)
      decl-elim
    ⟩
    (
    acc ≔ z ；
    iter
      (λ e →
        if g e then (
           if (f e) then
             acc ≔ F (★ acc) e
           else nop
        )
        else nop)
      (linear prod)
    )
    ≅⟨
      ≅ₚ-cong
      {1}
      {α , _}
      (λ body → acc ≔ z ； iter body (linear prod))
      (λ e → if g e then (if f e then _ else nop) else nop)
      (λ e → if (g e && f e) then _ else nop)
      nested-if
    ⟩
    (
    acc ≔ z ；
    iter
      (λ e →
        if (g e && f e) then
          acc ≔ F (★ acc) e
        else nop)
      (linear prod)
    )
    ≅⟨
      ≅ₚ-cong
      {1}
      {α , _}
      (λ body → acc ≔ z ； iter body (linear prod))
      (λ e → if (g e && f e) then _ else nop)
      (λ e → if (f e && g e) then _ else nop)
      (λ {e} →
        let v , ⇒v = ⊢-total {Bool} {_} {f e} in
        let w , ⇒w = ⊢-total {Bool} {_} {g e} in
          ≅ₛ-subst
            {f = λ e → if e then _ else nop}
            (&&-eval ⇒w ⇒v)
            (&&-eval ⇒v ⇒w)
            (BoolP.∧-comm w v)
      )
    ⟩
    (
    acc ≔ z ；
    iter
      (λ e →
        if (f e && g e) then
          acc ≔ F (★ acc) e
        else nop)
      (linear prod)
    )
    ≅˘⟨
      ≅ₚ-cong
        {1}
        {α , _}
        (λ body → acc ≔ z ； iter body (linear prod) )
        (λ e → decl Bool λ cond → if _ then _ else nop)
        (λ e → if _ then _ else nop)
        decl-elim
    ⟩
    (
    acc ≔ z ；
    iter
      (λ e →
        decl Bool λ cond →
        if (f e && g e) then
          acc ≔ F (★ acc) e
        else nop)
      (linear prod)
    )
    ≅˘⟨
      ≅ₚ-cong
        {2}
        {Ref Bool , α , _}
        (λ body → acc ≔ z ； iter (λ e → decl Bool λ cond → body cond e) (linear prod))
        (λ cond e → cond ≔ f e && g e ； if ★ cond then _ else nop)
        (λ cond e → if (f e && g e) then _ else nop)
        (≔-subst {f = λ e → if e then _ else nop})
    ⟩
    (
    acc ≔ z ；
    iter
      (λ e →
        decl Bool λ cond →
        cond ≔ f e && g e ；
        if ★ cond then
          acc ≔ F (★ acc) e
        else nop)
      (linear prod)
    )
    ≡⟨⟩
    fold F z (filter (λ x → f x && g x) s) acc
  ∎
filter-filter {α} {s@(nested (prod , nf))} {f} {g} F {z} {acc} =
  begin
    fold F z (filter f (filter g s)) acc
    ≡⟨⟩ -- by definiton of filter
    fold F z (filter f (nested (prod , λ a → filter g (nf a)))) acc
    ≡⟨⟩ -- by definition of filter
    fold F z (nested (prod , λ a → filter f (filter g (nf a)))) acc
    ≅⟨
      ≅-cong
        (λ body → nested (prod , body))
        (λ a → filter f (filter g (nf a)))
        (λ a → filter (λ x → f x && g x) (nf a))
        (λ {a} → filter-filter {s = nf a})
        F
    ⟩ -- by induction
    fold F z (nested (prod , λ a → filter (λ x → f x && g x) (nf a))) acc
    ≡⟨⟩ -- by definition of filter
    fold F z (filter (λ x → f x && g x) s) acc
  ∎

filter-true : ∀ { α } { s : SStream α } → filter (λ x → true) s ≅ s
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
    iter (λ e →
      iter
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
    ≡⟨⟩ -- by definition of iter
    (
    x ≔ z ；
    iter (λ e →
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
    iter (λ e →
      decl Bool λ cond →
      cond ≔ true ；
      if ★ cond then
        x ≔ F (★ x) e
      else
        nop) s
    )
    ≅⟨
      ≅ₚ-cong
      {2}
      {Ref Bool , α , _}
      (λ S → x ≔ z ； iter (λ e → decl Bool λ cond → S cond e) s)
      (λ cond e → cond ≔ true ； if ★ cond then x ≔ F (★ x) e else nop)
      (λ cond e → if true then x ≔ F (★ x) e else nop)
      (≔-subst {f = λ ★cond → if ★cond then _ else _})
    ⟩
    (
    x ≔ z ；
    iter (λ e →
      decl Bool λ cond →
      if true then
        x ≔ F (★ x) e
      else
        nop) s
    )
    ≅⟨
      ≅ₚ-cong
      {2}
      {Ref Bool , α , _}
      (λ S → x ≔ z ； iter (λ e → decl Bool λ cond → S cond e) s)
      (λ cond e → if true then x ≔ F (★ x) e else _)
      (λ cond e → x ≔ F (★ x) e)
      (β-if-true)
    ⟩
    (
    x ≔ z ；
    iter (λ e →
      decl Bool λ cond →
      x ≔ F (★ x) e) s
    )
    ≅⟨
      ≅ₚ-cong
      {1}
      {α , _}
      (λ S → x ≔ z ； iter S s)
      (λ e → decl Bool λ cond → x ≔ F (★ x) e)
      (λ e → x ≔ F (★ x) e)
      (decl-elim)
    ⟩
    (
    x ≔ z ；
    iter (λ a → x ≔ F (★ x) a) s
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
      (λ {a} → filter-true {s = f a})
      F
    ⟩
    fold F z (nested (prod , λ a → f a)) x
    ≡⟨⟩ -- by (λ a → f a) ≡ f
    fold F z s x
  ∎

filter-false : ∀ { α } { s : SStream α } → filter (λ x → false) s ≅ nil

filter-map : ∀ { α β } { s : SStream α } { f : Expr β → Expr Bool } { g : α → Expr β }
  → filter f (map g s) ≅ map g (filter (f ∘ g) s)

-- TODO: zipWith

flatmap-assoc : ∀ { α β γ } { s : SStream α } { f : β → SStream γ } { g : α → SStream β }
  → flatmap (λ x → flatmap f (g x)) s ≅ flatmap f (flatmap g s)

flatmap-map : ∀ { α β γ } { s : SStream α } { f : Expr β → SStream γ } { g : α → Expr β }
  → flatmap f (map g s) ≅ flatmap (f ∘ g) s

map-flatmap : ∀ { α β γ } { s : SStream α } { f : β → Expr γ } { g : α → SStream β }
  → map f (flatmap g s) ≅ flatmap ((map f) ∘ g) s

--flatmap-filter : ∀ { α β }
--  → ∀ { s : Stream α } → ∀ { f : Code α → Stream β } → ∀ { g : Code α → Code Bool }
--  → flatmap f (filter g s) ≅ flatmap (λ x → if g x then f x else nil) s

filter-flatmap : ∀ { α β } { s : SStream α } { f : β → Expr Bool } { g : α → SStream β }
  → filter f (flatmap g s) ≅ flatmap ((filter f) ∘ g) s

-- _ : ∀ { α ζ } { f : Expr ζ → Expr α → Expr ζ } { z : Expr ζ }
--   → (fold f z nil ≅ₚ (λ r → r ≔ z))
--     × (∀ s → ¬ (s ≅ nil) → fold f z s ≅ₚ
--          (λ r → r ← fold f z {!tail s!} ； r ≔ f  (★ r) {!head s!}))

fold-map : ∀ { α ζ β }
  { f : Expr ζ → Expr α → Expr ζ } { z : Expr ζ } { g : Expr β → Expr α } { s : Stream β }
  → fold f z (map g s) ≅ₚ fold (λ x y → f x (g y)) z s

fold-filter : ∀ { α ζ }
  { f : Expr ζ → Expr α → Expr ζ } { z : Expr ζ } { g : Expr α → Expr Bool } { s : Stream α }
  → fold f z (filter g s) ≅ₚ fold (λ x y → g y ⁇ f x y ∷ x) z s

-- fold-flatmap : ∀ { α ζ β }
--   { f : Expr ζ → α → Expr ζ } { z : Expr ζ } { g : β → SStream α } { s : SStream β }
--   → fold f z (flatmap g s) ≅ₚ {!!}

-- fold-unfold : ∀ { α ζ ξ }
--   { f : Expr ζ → Expr α → Expr ζ } { z : Expr ζ }
--   { g : (Expr ξ → (Expr Bool × Expr α × Expr ξ)) } { x : Expr ξ }
--   → fold f z (unfold g x) ≅ₚ {!!}

-- fold-take : ∀ { α ζ }
--   { f : Expr ζ → Expr α → Expr ζ } { z : Expr ζ } { n : Expr Int } { s : Stream α }
--   → fold f z (take n s) ≅ₚ fold {!λ { (x , m) y → {!with m < n | true = (f x y , m + 1) | false = (y , m + 1)!} }!} z s

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

zip-map : ∀ { α β α' β' } (s : SStream α) (t : SStream β) (f : α → α') (g : β → β') (p : ∥ s ∥ₛ ℕ.+ ∥ t ∥ₛ ℕ.≤ 1)
  → zip (map' f s) (map' g t) {maps-can-zip s t f g p} ≅ map' (λ { (x , y) → f x , g y }) (zip s t {p})
zip-map s@(linear (producer (i₁ , for (b₁ , ix₁)))) t@(linear (producer (i₂ , for (b₂ , ix₂)))) f g p F {z} {x} =
  let q = maps-can-zip s t f g p in
  begin
    fold F z (zip (map' f s) (map' g t) {q}) x
    ≡⟨⟩
    fold F z (
      zip
        (linear (producer (i₁ , for (b₁ , λ s i k → ix₁ s i (λ e → k (f e))))))
        (linear (producer (i₂ , for (b₂ , λ s i k → ix₂ s i (λ e → k (g e)))))) {q}) x
    ≡⟨⟩
    fold F z (
      linear (
        producer (
          (λ k → i₁ (λ a → i₂ (λ b → k (a , b)))) ,
          for (
            (λ { (a , b) r →
              decl Int λ x →
              decl Int λ y →
              x ← b₁ a ；
              y ← b₂ b ；
              if (★ x) < (★ y) then
                r ≔ ★ x
              else
                r ≔ ★ y
            }) ,
            λ { (a , b) i k →
              ix₁ a i (λ n → ix₂ b i (λ m → k (f n , g m)))
            })))) x
    ≅⟨ {!!} ⟩
    {!!}
        -- (linear (
        --   producer (
        --     (λ k → i₁ (λ a → i₂ (λ b → k (a , b)))) ,
        --     for (
        --       (λ { (a , b) r →
        --         decl Int λ x →
        --         decl Int λ y →
        --         x ← b₁ a ；
        --         y ← b₂ b ；
        --         if (★ x) < (★ y) then
        --           r ≔ ★ x
        --         else
        --           r ≔ ★ y }) ,
        --       λ { (a , b) i k →
        --         ix₁ a i (λ n → ix₂ b i (λ m → k (n , m))) }
        --     ))))) x
    ≡⟨⟩
    fold F z (map' (λ { (x , y) → f x , g y }) (zip s t {p})) x
  ∎

module Monad where

  -- Cannot use RawMonad because Set f -> Set f
  module StreamMonad where

    ReturnBindLeftId :
      (∀ { A } → A → SStream A) -- return
      → (∀ { A B } → SStream A → (A → SStream B) → SStream B) -- bind
      → Set₁
    ReturnBindLeftId return _>>=_ =
      ∀ { A B } { a : Expr A } { f : Expr A → Stream B }
      → (return a >>= λ x → f x) ≅ f a
    ReturnBindRightId : 
      (∀ { A } → A → SStream A) -- return
      → (∀ { A B } → SStream A → (A → SStream B) → SStream B) -- bind
      → Set₁
    ReturnBindRightId return _>>=_ =
      ∀ { A } { ma : SStream A }
      → (ma >>= λ x → return x) ≅ ma
    BindAssoc : 
      (∀ { A B } → SStream A → (A → SStream B) → SStream B) -- bind
      → Set₁
    BindAssoc _>>=_ =
      ∀ { A B C } { ma : SStream A } { f : A → SStream B } { g : B → SStream C }
      → (ma >>= λ x → (f x >>= λ y → g y)) ≅ ((ma >>= λ x → f x) >>= λ y → g y)

  -- return₁ x gives a singleton stream of x, much like monad intepretation of lists
  return₁ : ∀ { A } → A → SStream A
  return₁ x = linear (producer ((λ k → k x) , (unfolder ((λ a r → r ≔ true) , atMost1 , (λ a k → k a)))))

  -- return₂ x gives an infinite stream of x
  return₂ : ∀ { A } → A → SStream A
  return₂ x = linear (producer ((λ k → k x) , unfolder ((λ _ r → r ≔ true) , many , (λ a k → k a))))
  
  -- could give two id elements for bind

  infix 4 _>>=_
  _>>=_ : ∀ { A B } → SStream A → (A → SStream B) → SStream B
  s >>= f = flatmap f s
  
  return-bind-left-id₁ : StreamMonad.ReturnBindLeftId return₁ _>>=_
  return-bind-left-id₁ {a = a} {f} F {z} {x} =
    begin
      fold F z (return₁ a >>= λ x → f x) x
      ≡⟨⟩
      fold F z (return₁ a >>= f) x
      ≡⟨⟩
      fold F z
        (flatmap f (
          linear (
            producer (
              (λ k → k a) ,
              (unfolder (
                (λ a r → r ≔ true) ,
                atMost1 ,
                λ a k → k a)))))) x
      ≡⟨⟩
      fold F z
        (nested (
          producer (
            (λ k → k a) ,
            (unfolder (
              (λ _ r → r ≔ true) ,
              atMost1 ,
              (λ a k → k a)))) ,
          f)) x
      ≡⟨⟩
      (x ≔ z ；
      iter
        (λ e → iter (λ a → x ≔ F (★ x) a) (f e))
        (linear (
          producer (
            (λ k → k a) ,
            (unfolder (
              (λ a r → r ≔ true) ,
              atMost1 ,
              λ a k → k a))))))
      ≡⟨⟩
      (x ≔ z ；
      decl Bool λ cond →
      cond ≔ true ；
      if ★ cond then
         iter (λ a → x ≔ F (★ x) a) (f a)
      else
        nop)
      ≅⟨
        ≅ₚ-cong
          {1}
          {Ref Bool , _}
          (λ body → x ≔ z ； decl Bool body)
          (λ cond → cond ≔ true ； _)
          (λ cond → _)
          (≔-subst {f = λ e → if e then iter (λ a → x ≔ F (★ x) a) (f a) else nop})
      ⟩
      (x ≔ z ；
      decl Bool λ cond →
      if true then
         iter (λ a → x ≔ F (★ x) a) (f a)
      else
        nop)
      ≅⟨
        ≅ₚ-cong
          {1}
          {Ref Bool , _}
          (λ body → x ≔ z ； decl Bool body)
          (λ cond → if true then iter (λ a → x ≔ F (★ x) a) (f a) else nop)
          _
          β-if-true
      ⟩
      (x ≔ z ；
      decl Bool λ cond →
      iter (λ a → x ≔ F (★ x) a) (f a))
      ≅⟨ ≅ₚ-cong {0} (λ body → x ≔ z ； body) _ _ decl-elim ⟩
      (x ≔ z ；
      iter (λ a → x ≔ F (★ x) a) (f a))
      ≡⟨⟩
      fold F z (f a) x
    ∎

  return-bind-left-id₂ : StreamMonad.ReturnBindLeftId return₂ _>>=_
  return-bind-left-id₂ {a = a} {f} F {z} {x} =
    begin
      fold F z (return₂ a >>= λ x → f x) x
      ≡⟨⟩
      fold F z (return₂ a >>= f) x
      ≡⟨⟩
      fold F z
        (flatmap f (
          linear (
            producer (
              (λ k → k a) ,
              (unfolder (
                (λ _ r → r ≔ true) ,
                many ,
                λ a k → k a)))))) x
      ≡⟨⟩
      fold F z
        (nested (
          producer (
            (λ k → k a) ,
            (unfolder (
              (λ _ r → r ≔ true) ,
              many ,
              (λ a k → k a)))) ,
          f)) x
      ≡⟨⟩
      (x ≔ z ；
      iter
        (λ e → iter (λ a → x ≔ F (★ x) a) (f e))
        (linear (
          producer (
            (λ k → k a) ,
            (unfolder (
              (λ a r → r ≔ true) ,
              many ,
              λ a k → k a))))))
      ≡⟨⟩
      (x ≔ z ；
      decl Bool λ cond →
      cond ≔ true ；
      while ★ cond then (
         iter (λ a → x ≔ F (★ x) a) (f a) ；
         cond ≔ true
      ))
      ≅⟨ {!!} ⟩
      (x ≔ z ；
      decl Bool λ cond →
      cond ≔ true ；
      while ★ cond then (
         iter (λ a → x ≔ F (★ x) a) (f a)
      ))
      ≅⟨
        ≅ₚ-cong
          {1}
          {Ref Bool , _}
          (λ body → x ≔ z ； decl Bool body)
          (λ cond → cond ≔ true ； while ★ cond then _)
          (λ cond → while true then _)
          (≔-subst {f = λ e → while e then iter (λ a → x ≔ F (★ x) a) (f a)})
      ⟩
      (x ≔ z ；
      decl Bool λ cond →
      while true then 
         iter (λ a → x ≔ F (★ x) a) (f a)
      )
      ≅⟨ ≅ₚ-cong {0} (λ body → x ≔ z ； body) _ _ decl-elim ⟩
      (x ≔ z ；
      while true then 
         iter (λ a → x ≔ F (★ x) a) (f a)
      )
      ≅⟨ {!nested-while-loop!} ⟩
      (x ≔ z ；
      iter (λ a → x ≔ F (★ x) a) (f a))
      ≡⟨⟩
      fold F z (f a) x
    ∎

  return-bind-right-id₁ : StreamMonad.ReturnBindRightId return₁ _>>=_
  return-bind-right-id₁ {ma = ma@(linear p)} F {z} {x} =
    begin
      fold F z (ma >>= λ x → return₁ x) x
      ≡⟨⟩
      fold F z (flatmap return₁ ma) x
      ≡⟨⟩
      fold F z (nested (p , return₁)) x
      ≡⟨⟩
      (x ≔ z ；
      iter (λ a → x ≔ F (★ x) a) (nested (p , return₁)))
      ≡⟨⟩
      (x ≔ z ；
      iter (λ e → iter (λ a → x ≔ F (★ x) a) (return₁ e)) (linear p))
      ≡⟨⟩
      (x ≔ z ；
      iter
        (λ e →
          decl Bool λ cond →
          cond ≔ true ；
          if ★ cond then
            x ≔ F (★ x) e
          else nop)
        (linear p))
      ≅⟨
        ≅ₚ-cong
          {2}
          {Ref Bool , _ , _}
          (λ body → x ≔ z ； iter (λ e → decl Bool λ cond → body cond e) (linear p))
          _
          _
          (λ {_} {e} → ≔-subst {f = λ c → if c then x ≔ F (★ x) e else nop})
      ⟩
      (x ≔ z ；
      iter
        (λ e →
          decl Bool λ cond →
          if true then
            x ≔ F (★ x) e
          else nop)
        (linear p))
      ≅⟨
        ≅ₚ-cong
          {1}
          (λ body → x ≔ z ； iter body (linear p))
          (λ e → decl Bool _)
          (λ e → if true then x ≔ F (★ x) e else nop)
          decl-elim
      ⟩
      (x ≔ z ；
      iter
        (λ e →
          if true then
            x ≔ F (★ x) e
          else nop)
        (linear p))
      ≅⟨
        ≅ₚ-cong
          {1}
          (λ body → x ≔ z ； iter body (linear p))
          (λ e → if true then x ≔ F (★ x) e else nop)
          (λ e → x ≔ F (★ x) e)
          β-if-true
      ⟩
      (x ≔ z ；
      iter
        (λ e → x ≔ F (★ x) e)
        (linear p))
      ≡⟨⟩
      (x ≔ z ；
      iter (λ a → x ≔ F (★ x) a) ma)
      ≡⟨⟩
      fold F z ma x
    ∎
  return-bind-right-id₁ {ma = ma@(nested (p , f))} F {z} {x} =
    begin
      fold F z (ma >>= λ x → return₁ x) x
      ≡⟨⟩
      fold F z (flatmap return₁ ma) x
      ≡⟨⟩
      fold F z (nested (p , λ a → flatmap return₁ (f a))) x
      ≡⟨⟩
      (x ≔ z ；
      iter (λ a → x ≔ F (★ x) a) (nested (p , λ a → flatmap return₁ (f a))))
      ≡⟨⟩
      (x ≔ z ；
      iter (λ e → iter (λ a → x ≔ F (★ x) a) (flatmap return₁ (f e))) (linear p))
      ≡⟨⟩
      (x ≔ z ；
      iter (λ e → iter (λ a → x ≔ F (★ x) a) ((f e) >>= λ x → return₁ x)) (linear p))
      ≅⟨ 
        ≅ₚ-cong
          {!λ body → x ≔ z ； iter (λ e → iter (λ a → x ≔ F (★ x) a) (body e)) (linear p)!}
          {!!}
          {!!}
          {!return-bind-right-id₁!}
      ⟩
      (x ≔ z ；
      iter (λ e → iter (λ a → x ≔ F (★ x) a) (f e)) (linear p))
      ≅⟨ {!!} ⟩
      (x ≔ z ；
      iter
        (λ e → x ≔ F (★ x) e)
        (nested (p , f)))
      ≡⟨⟩
      (x ≔ z ；
      iter (λ a → x ≔ F (★ x) a) ma)
      ≡⟨⟩
      fold F z ma x
    ∎
  

  bind-assoc : StreamMonad.BindAssoc _>>=_
  bind-assoc {ma = ma} {f} {g} = flatmap-assoc {s = ma} {f = g} {g = f}
