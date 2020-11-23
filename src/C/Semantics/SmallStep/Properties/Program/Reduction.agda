{-# OPTIONS --safe --exact-split --without-K --sized-types #-}

open import Size

open import C.Lang
open import C.Semantics.SmallStep.Model
open import Codata.Thunk
open import Codata.Delay
open import Codata.Colist as Colist hiding ([_] ; _++_)
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding (setoid)
open import Relation.Nullary

open Lang ⦃ ... ⦄
open Semantics ⦃ ... ⦄

module C.Semantics.SmallStep.Properties.Program.Reduction ⦃ _ : Lang ⦄ ⦃ _ : Semantics ⦄ where

-- See also ◅◅ in the semantics
↝*-trans : ∀ { e f i } → Trans (_~[ e ]↝*_) (_~[ f ]↝*_) (λ x y → _~[_]↝*_ {i} x (e ++ f) y)
↝*-trans ε ε = ε
↝*-trans ε (x ↓◅ j↝*k) = x ↓◅ ↝*-trans ε j↝*k -- weird size laundering again
↝*-trans ε (x ↗◅ j↝*k) = x ↗◅ j↝*k
↝*-trans (i↝X ↗◅ X↝*j) j↝*k = i↝X ↗◅ λ where .force → ↝*-trans (force X↝*j) j↝*k
↝*-trans (i↝X ↓◅ X↝*j) j↝*k = i↝X ↓◅ ↝*-trans X↝*j j↝*k

thunk-ind-run : ∀ { A B C e es i } → A ~[ e ↓ ]↝ B → _~[_]↝*_ {i} B es C → Thunk (λ i → _~[_]↝*_ {i} A (e ↓∷ es) C) i
thunk-ind-run A↝B ε           = λ where .force → A↝B ↓◅ ε
thunk-ind-run A↝B (x ↗◅ B↝*C) = λ where .force → A↝B ↓◅ x ↗◅ B↝*C
thunk-ind-run A↝B (x ↓◅ B↝*C) = λ where .force → A↝B ↓◅ force (thunk-ind-run x B↝*C)

↝*-to-↝⁺ : ∀ { A B C e es i } → A ~[ e ]↝ B → _~[_]↝*_ {i} B es C → _~[_]↝⁺_ {i} A (e ↝∷ next e es) C
↝*-to-↝⁺ {e = _ ↓} A↝B B↝*C        = _ , A↝B , B↝*C
↝*-to-↝⁺ {e = _ ↗} A↝B ε           = _ , A↝B , λ where .force → ε
↝*-to-↝⁺ {e = _ ↗} A↝B (x ↗◅ B↝*C) = _ , A↝B , λ where .force → x ↗◅ B↝*C
↝*-to-↝⁺ {e = _ ↗} A↝B (x ↓◅ B↝*C) = _ , A↝B , thunk-ind-run x B↝*C

↝⁺-to-↝* : ∀ { A B es i } → _~[_]↝⁺_ {i} A es B → _~[_]↝*_ {i} A es B
↝⁺-to-↝* {A} {B} {[]} ()
↝⁺-to-↝* {es = _ ↗∷ _} (X , A↝X , X↝*B) = A↝X ↗◅ X↝*B
↝⁺-to-↝* {es = _ ↓∷ _} (X , A↝X , X↝*B) = A↝X ↓◅ X↝*B

↝̸-transᵇ : ∀ { S S' : State } { e }
  → S ~[ e ]↝* S' → Finite e → Terminating S' → Terminating S
↝̸-transᵇ ε _ S'↝ = S'↝
↝̸-transᵇ (S↝X ↗◅ X↝*S') (_ ↗∷ p) S'↝ = S↝X ∷ ↝̸-transᵇ (force X↝*S') p S'↝
↝̸-transᵇ (S↝X ↓◅ X↝*S') (_ ↓∷ p) S'↝ = S↝X ∷ ↝̸-transᵇ X↝*S' p S'↝

↝̸-transᶠ : ∀ { S S' : State } { e }
  → S ~[ e ]↝* S' → Finite e → Terminating S → Terminating S'
↝̸-transᶠ ε _ S↝ = S↝
↝̸-transᶠ (S↝X ↗◅ X↝*S') (_ ↗∷ p) ([ S↝̸ ]) = ⊥-elim (S↝̸ _ _ S↝X)
↝̸-transᶠ (S↝X ↗◅ X↝*S') (_ ↗∷ p) (S↝Y ∷ Y↝)
  rewrite proj₂ (↝-det S↝X S↝Y) = ↝̸-transᶠ (force X↝*S') p Y↝
↝̸-transᶠ (S↝X ↓◅ X↝*S') (_ ↓∷ p) ([ S↝̸ ]) = ⊥-elim (S↝̸ _ _ S↝X)
↝̸-transᶠ (S↝X ↓◅ X↝*S') (_ ↓∷ p) (S↝Y ∷ Y↝)
  rewrite proj₂ (↝-det S↝X S↝Y) = ↝̸-transᶠ X↝*S' p Y↝

↝ω-transᵇ : ∀ { X Y : State } { e }
  → X ~[ e ]↝* Y → Finite e → ¬ Terminating Y → ¬ Terminating X
↝ω-transᵇ X↝*Y p Y↝ω X↝̸ = Y↝ω (↝̸-transᶠ X↝*Y p X↝̸)

↝ω-transᶠ : ∀ { X Y : State } { e }
  → X ~[ e ]↝* Y → Finite e → ¬ Terminating X → ¬ Terminating Y
↝ω-transᶠ X↝*Y p X↝ω Y↝̸ = X↝ω (↝̸-transᵇ X↝*Y p Y↝̸)

↝*-det : ∀ { S S₁ S₂ x y i }
  → Stuck S₁ → Stuck S₂ → S ~[ x ]↝* S₁ → S ~[ y ]↝* S₂ → Delay (S₁ ≡ S₂) i
↝*-det _   _   ε              ε              = now refl
↝*-det S↝̸  _   ε              (S↝X ↗◅ _)     = ⊥-elim (S↝̸ _ _ S↝X)
↝*-det _   S↝̸  (S↝X ↗◅ _)     ε              = ⊥-elim (S↝̸ _ _ S↝X)
↝*-det S₁↝̸ S₂↝̸ (S↝X ↗◅ X↝*S₁) (S↝Y ↗◅ Y↝*S₂)
  rewrite proj₂ (↝-det S↝X S↝Y) = later λ where .force → ↝*-det S₁↝̸ S₂↝̸ (force X↝*S₁) (force Y↝*S₂)
↝*-det S↝̸  _   ε              (S↝X ↓◅ _)     = ⊥-elim (S↝̸ _ _ S↝X)
↝*-det _   S↝̸  (S↝X ↓◅ _)     ε              = ⊥-elim (S↝̸ _ _ S↝X)
↝*-det S₁↝̸ S₂↝̸ (S↝X ↓◅ X↝*S₁) (S↝Y ↓◅ Y↝*S₂)
  rewrite proj₂ (↝-det S↝X S↝Y) = later λ where .force → ↝*-det S₁↝̸ S₂↝̸ X↝*S₁         Y↝*S₂
↝*-det S₁↝̸ S₂↝̸ (S↝X ↓◅ X↝*S₁) (S↝Y ↗◅ Y↝*S₂)
  rewrite proj₂ (↝-det S↝X S↝Y) = later λ where .force → ↝*-det S₁↝̸ S₂↝̸ X↝*S₁         (force Y↝*S₂)
↝*-det S₁↝̸ S₂↝̸ (S↝X ↗◅ X↝*S₁) (S↝Y ↓◅ Y↝*S₂)
  rewrite proj₂ (↝-det S↝X S↝Y) = later λ where .force → ↝*-det S₁↝̸ S₂↝̸ (force X↝*S₁) Y↝*S₂

↝*-det' : ∀ { S S₁ S₂ x y i }
  → S ~[ x ]↝* S₁ → S ~[ y ]↝* S₂ → Delay (∃[ z ] (S₁ ~[ z ]↝* S₂ ⊎ S₂ ~[ z ]↝* S₁)) i
↝*-det' {x = []}     {_}      ε              S↝*S₂ = now (_ , inj₁ S↝*S₂)
↝*-det' {x = _ ↗∷ _} {[]}     S↝*S₁@(_ ↗◅ _) ε     = now (_ , inj₂ S↝*S₁)
↝*-det' {x = _ ↓∷ _} {[]}     S↝*S₁@(_ ↓◅ _) ε     = now (_ , inj₂ S↝*S₁)
↝*-det' {x = _ ↗∷ _} {_ ↗∷ _} (S↝X ↗◅ X↝*S₁) (S↝Y ↗◅ Y↝*S₂)
  rewrite proj₂ (↝-det S↝X S↝Y) = later λ where .force → ↝*-det' (force X↝*S₁) (force Y↝*S₂)
↝*-det' {x = _ ↗∷ _} {_ ↓∷ _} (S↝X ↗◅ X↝*S₁) (S↝Y ↓◅ Y↝*S₂)
  rewrite proj₂ (↝-det S↝X S↝Y) = later λ where .force → ↝*-det' (force X↝*S₁) Y↝*S₂
↝*-det' {x = _ ↓∷ _} {_ ↗∷ _} (S↝X ↓◅ X↝*S₁) (S↝Y ↗◅ Y↝*S₂)
  rewrite proj₂ (↝-det S↝X S↝Y) = later λ where .force → ↝*-det' X↝*S₁         (force Y↝*S₂)
↝*-det' {x = _ ↓∷ _} {_ ↓∷ _} (S↝X ↓◅ X↝*S₁) (S↝Y ↓◅ Y↝*S₂)
  rewrite proj₂ (↝-det S↝X S↝Y) = later λ where .force → ↝*-det' X↝*S₁         Y↝*S₂

reduce-[] : ∀ { A } → labels A ≈ [] → Stuck A
reduce-[] {A} r with ↝-reduce A
reduce-[] {A} [] | [] = λ _ _ → ↝-Ω

reduce-det : ∀ { A i } (x y : Reduction _~[_]↝_ A ∞) → [ i ]_≈_ (labels-of x) (labels-of y)
reduce-det []          []          = []
reduce-det []          (Ω↝Y ↗∷ _)  = ⊥-elim (↝-Ω Ω↝Y)
reduce-det (Ω↝X ↗∷ _)  []          = ⊥-elim (↝-Ω Ω↝X)
reduce-det (A↝X ↗∷ X↝) (A↝Y ↗∷ Y↝) with ↝-det A↝X A↝Y
... | refl , refl = _ ↗∷ λ where .force → reduce-det (force X↝) (force Y↝)
reduce-det []          (Ω↝Y ↓∷ _)  = ⊥-elim (↝-Ω Ω↝Y)
reduce-det (Ω↝X ↓∷ _)  []          = ⊥-elim (↝-Ω Ω↝X)
reduce-det (A↝X ↓∷ X↝) (A↝Y ↓∷ Y↝) with ↝-det A↝X A↝Y
... | refl , refl = _ ↓∷ reduce-det X↝ Y↝
reduce-det (A↝X ↓∷ X↝) (A↝Y ↗∷ Y↝) with ↝-det A↝X A↝Y
... | ()
reduce-det (A↝X ↗∷ X↝) (A↝Y ↓∷ Y↝) with ↝-det A↝X A↝Y
... | ()

reduction-of : ∀ { A B e i } → A ~[ e ]↝* B → Reduction _~[_]↝_ A i
reduction-of {A} ε = ↝-reduce A
reduction-of (A↝X ↗◅ X↝*B) = A↝X ↗∷ λ where .force → reduction-of (force X↝*B)
reduction-of (A↝X ↓◅ X↝*B) = A↝X ↓∷ reduction-of X↝*B
