open import C.Base
open import C.Properties.Properties
open import C.Properties.Musical
open import Streams.Properties
open import Streams.Base
open import Data.Product using (_×_ ; _,_)

module Streams.Monad ⦃ _ : C ⦄ ⦃ _ : Semantics ⦄ where

open C ⦃ ... ⦄
open Semantics ⦃ ... ⦄
open ≅-Reasoning

-- Cannot use RawMonad because Set f -> Set f
record StreamMonad : Set₁ where
  field
    return : ∀ { A } → A → SStream A
    _>>=_ : ∀ { A B } → SStream A → (A → SStream B) → SStream B
    
    return-bind-left-id : ∀ { A B } { a : Expr A } { f : Expr A → Stream B }
      → (return a >>= λ x → f x) ≅ f a
    return-bind-right-id : ∀ { A } { ma : SStream A }
      → (ma >>= λ x → return x) ≅ ma
    bind-assoc : ∀ { A B C } { ma : SStream A } { f : A → SStream B } { g : B → SStream C }
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

monad₁ : StreamMonad
StreamMonad.return monad₁ = return₁
StreamMonad._>>=_ monad₁ = _>>=_
StreamMonad.return-bind-left-id monad₁ {a = a} {f} F {z} {x} =
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
StreamMonad.return-bind-right-id monad₁ {ma = ma@(linear p)} F {z} {x} =
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
StreamMonad.return-bind-right-id monad₁ {ma = ma@(nested (p , f))} F {z} {x} =
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
StreamMonad.bind-assoc monad₁ {ma = ma} {f} {g} =
  {!flatmap-assoc {s = ma} {f = g} {g = f}!}

monad₂ : StreamMonad
StreamMonad.return monad₂ = return₂
StreamMonad._>>=_ monad₂ = _>>=_
StreamMonad.return-bind-left-id monad₂ {a = a} {f} F {z} {x} =
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
StreamMonad.return-bind-right-id monad₂ = {!!}
StreamMonad.bind-assoc monad₂ {ma = ma} {f} {g} =
  StreamMonad.bind-assoc monad₁ {ma = ma} {f} {g}
