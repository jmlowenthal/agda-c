open import C.Lang
open import C.Semantics.SmallStep.Model
open import Codata.Musical.Colist as Colist hiding ([_])
open import Codata.Musical.Notation
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open Lang ⦃ ... ⦄
open Semantics ⦃ ... ⦄

module C.Semantics.SmallStep.Properties.Program.Reduction ⦃ _ : Lang ⦄ ⦃ _ : Semantics ⦄ where

↝*-trans : ∀ { e f } → Trans (_~[ e ]↝*_) (_~[ f ]↝*_) (_~[ e ++ f ]↝*_)
↝*-trans ε j↝*k = j↝*k
↝*-trans (i↝X ◅ X↝*j) j↝*k = i↝X ◅ ♯ (↝*-trans (♭ X↝*j) j↝*k)

↝*-to-↝⁺ : ∀ { A B C e es } → A ~[ e ]↝ B → B ~[ es ]↝* C → A ~[ e ∷ ♯ es ]↝⁺ C
↝*-to-↝⁺ A↝B B↝*C = _ , A↝B , B↝*C

↝⁺-to-↝* : ∀ { A B es } → A ~[ es ]↝⁺ B → A ~[ es ]↝* B
↝⁺-to-↝* {A} {B} {[]} ()
↝⁺-to-↝* {es = _ ∷ _} (X , A↝X , X↝*B) = A↝X ◅ ♯ X↝*B

↝̸-transᵇ : ∀ { S S' : State } { e }
  → S ~[ e ]↝* S' → Finite e → Terminating S' → Terminating S
↝̸-transᵇ ε _ S'↝ = S'↝
↝̸-transᵇ (S↝X ◅ X↝*S') (_ ∷ p) S'↝ = S↝X ∷ ↝̸-transᵇ (♭ X↝*S') p S'↝

↝̸-transᶠ : ∀ { S S' : State } { e }
  → S ~[ e ]↝* S' → Finite e → Terminating S → Terminating S'
↝̸-transᶠ ε _ S↝ = S↝
↝̸-transᶠ (S↝X ◅ X↝*S') (_ ∷ p) ([ S↝̸ ]) = ⊥-elim (S↝̸ _ _ S↝X)
↝̸-transᶠ (S↝X ◅ X↝*S') (_ ∷ p) (S↝Y ∷ Y↝)
  rewrite proj₂ (↝-det S↝X S↝Y) = ↝̸-transᶠ (♭ X↝*S') p Y↝

↝ω-transᵇ : ∀ { X Y : State } { e }
  → X ~[ e ]↝* Y → Finite e → ¬ Terminating Y → ¬ Terminating X
↝ω-transᵇ X↝*Y p Y↝ω X↝̸ = Y↝ω (↝̸-transᶠ X↝*Y p X↝̸)

↝ω-transᶠ : ∀ { X Y : State } { e }
  → X ~[ e ]↝* Y → Finite e → ¬ Terminating X → ¬ Terminating Y
↝ω-transᶠ X↝*Y p X↝ω Y↝̸ = X↝ω (↝̸-transᵇ X↝*Y p Y↝̸)

{-# NON_TERMINATING #-} -- Either reduction could be infinite
↝*-det : ∀ { S S₁ S₂ x y }
  → Stuck S₁ → Stuck S₂ → S ~[ x ]↝* S₁ → S ~[ y ]↝* S₂ → S₁ ≡ S₂
↝*-det _ _ ε ε = refl
↝*-det S↝̸ _ ε (S↝X ◅ _) = ⊥-elim (S↝̸ _ _ S↝X)
↝*-det _ S↝̸ (S↝X ◅ _) ε = ⊥-elim (S↝̸ _ _ S↝X)
↝*-det S₁↝̸ S₂↝̸ (S↝X ◅ X↝*S₁) (S↝Y ◅ Y↝*S₂)
  rewrite proj₂ (↝-det S↝X S↝Y) = ↝*-det S₁↝̸ S₂↝̸ (♭ X↝*S₁) (♭ Y↝*S₂)

{-# NON_TERMINATING #-} -- Could be two infinite reductions
↝*-det' : ∀ { S S₁ S₂ x y }
  → S ~[ x ]↝* S₁ → S ~[ y ]↝* S₂ → ∃[ z ] (S₁ ~[ z ]↝* S₂ ⊎ S₂ ~[ z ]↝* S₁)
↝*-det' {x = []} {y} ε S↝*S₂ = _ , inj₁ S↝*S₂
↝*-det' {x = x ∷ xs} {[]} S↝*S₁@(_ ◅ _) ε = _ , inj₂ S↝*S₁
↝*-det' {x = x ∷ xs} {x₁ ∷ xs₁} (S↝X ◅ X↝*S₁) (S↝Y ◅ Y↝*S₂)
  rewrite proj₂ (↝-det S↝X S↝Y) = ↝*-det' (♭ X↝*S₁) (♭ Y↝*S₂)

Colist-refl : ∀ {a} {A : Set a} → Reflexive (_≈_ {a} {A})
Colist-refl = Setoid.refl (Colist.setoid _)

Colist-sym : ∀ {a} {A : Set a} → Symmetric (_≈_ {a} {A})
Colist-sym = Setoid.sym (Colist.setoid _)

Colist-trans : ∀ {a} {A : Set a} → Transitive (_≈_ {a} {A})
Colist-trans = Setoid.trans (Colist.setoid _)

reduce-[] : ∀ { A } → labels A ≈ [] → Stuck A
reduce-[] {A} r with reduce A
reduce-[] {A} [] | [] = λ _ _ → ↝-Ω

reduce-det : ∀ { A } (x y : Reduction _~[_]↝_ A) → labels-of x ≈ labels-of y
reduce-det [] [] = []
reduce-det [] (Ω↝Y ∷ _) = ⊥-elim (↝-Ω Ω↝Y)
reduce-det (Ω↝X ∷ _) [] = ⊥-elim (↝-Ω Ω↝X)
reduce-det (A↝X ∷ X↝) (A↝Y ∷ Y↝) with (↝-det A↝X A↝Y)
... | refl , refl = _ ∷ ♯ reduce-det (♭ X↝) (♭ Y↝)

reduction-of : ∀ { A B e } → A ~[ e ]↝* B → Reduction _~[_]↝_ A
reduction-of {A} ε = reduce A
reduction-of (A↝X ◅ X↝*B) = A↝X ∷ ♯ reduction-of (♭ X↝*B)
