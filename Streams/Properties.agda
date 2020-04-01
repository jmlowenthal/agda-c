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
open import Streams.Claims as Claims using (Claim)

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

ProofOf : ∀ { α } → Claim α → Set
ProofOf (s ≈ t) = s ≅ t

-- Both maps are equivalent, map is just a more efficient specialisation
map'≅map : ∀ { α β } { f : α → Expr β } { s : SStream α } → ProofOf (Claims.map'≅map f s)
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

map-map : ∀ { α β γ } { s : SStream α } { f : Expr β → Expr γ } { g : α → Expr β }
  → ProofOf (Claims.map-map s f g)
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

map-id : ∀ { α } { s : Stream α } → ProofOf (Claims.map-id s)
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
  → ProofOf (Claims.filter-filter s f g)
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

filter-true : ∀ { α } { s : SStream α } → ProofOf (Claims.filter-true s)
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

-- zip-map : ∀ { α β α' β' } (s : SStream α) (t : SStream β) (f : α → α') (g : β → β') (p : ∥ s ∥ₛ ℕ.+ ∥ t ∥ₛ ℕ.≤ 1)
--   → ProofOf (Claims.zip-map s t f g p)
-- zip-map s@(linear (producer (i₁ , for (b₁ , ix₁)))) t@(linear (producer (i₂ , for (b₂ , ix₂)))) f g p F {z} {x} =
--   let q = maps-can-zip s t f g p in
--   begin
--     fold F z (zip (map' f s) (map' g t) {q}) x
--     ≡⟨⟩
--     fold F z (
--       zip
--         (linear (producer (i₁ , for (b₁ , λ s i k → ix₁ s i (λ e → k (f e))))))
--         (linear (producer (i₂ , for (b₂ , λ s i k → ix₂ s i (λ e → k (g e)))))) {q}) x
--     ≡⟨⟩
--     fold F z (
--       linear (
--         producer (
--           (λ k → i₁ (λ a → i₂ (λ b → k (a , b)))) ,
--           for (
--             (λ { (a , b) r →
--               decl Int λ x →
--               decl Int λ y →
--               x ← b₁ a ；
--               y ← b₂ b ；
--               if (★ x) < (★ y) then
--                 r ≔ ★ x
--               else
--                 r ≔ ★ y
--             }) ,
--             λ { (a , b) i k →
--               ix₁ a i (λ n → ix₂ b i (λ m → k (f n , g m)))
--             })))) x
--     ≅⟨ {!!} ⟩
--     {!!}
--         -- (linear (
--         --   producer (
--         --     (λ k → i₁ (λ a → i₂ (λ b → k (a , b)))) ,
--         --     for (
--         --       (λ { (a , b) r →
--         --         decl Int λ x →
--         --         decl Int λ y →
--         --         x ← b₁ a ；
--         --         y ← b₂ b ；
--         --         if (★ x) < (★ y) then
--         --           r ≔ ★ x
--         --         else
--         --           r ≔ ★ y }) ,
--         --       λ { (a , b) i k →
--         --         ix₁ a i (λ n → ix₂ b i (λ m → k (n , m))) }
--         --     ))))) x
--     ≡⟨⟩
--     fold F z (map' (λ { (x , y) → f x , g y }) (zip s t {p})) x
--   ∎
