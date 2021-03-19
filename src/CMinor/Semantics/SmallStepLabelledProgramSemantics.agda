open import CMinor.Lang.Lang
open import CMinor.Semantics.NaturalExpressionSemantics

open import Level using (Level ; _⊔_)
open import Data.List as List using (List ; [] ; _∷_)
open import Data.Product as Product using (∃-syntax ; _×_ ; Σ) renaming (_,_ to _,'_)
open import Data.Sum as Sum using (_⊎_)
open import Data.Maybe as Maybe using (Maybe ; just ; nothing)
open import Data.Vec as Vec using (Vec)
open import Data.Nat as ℕ using (ℕ)
open import Data.Nat.Binary as ℕᵇ using (ℕᵇ)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

open import CMinor.Semantics.SmallStepLabelledProgramSemantics.Definitions

module CMinor.Semantics.SmallStepLabelledProgramSemantics where

record SmallStepLabelledProgramSemantics
  {langLevels exprLevels}
  {e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ : Level}
  (i s k l t : Level)
  (𝓛 : Lang langLevels)
  (𝓔 : NaturalExpressionSemantics exprLevels 𝓛)
  : Set (Level.suc (i ⊔ s ⊔ k ⊔ l ⊔ t ⊔ LangLevels.SuperLevel langLevels ⊔ NaturalExpressionSemanticsLevels.SuperLevel exprLevels))
  where

  open Lang 𝓛
  open NaturalExpressionSemantics 𝓔

  field
    definitions : Definitions i k s l t 𝓛 𝓔

  open Definitions definitions

  field
    -- callcont
    callcont : Continuation → Continuation
    callcont-cons : ∀ s k → callcont (cons s k) ≡ callcont k
    callcont-endblock : ∀ k → callcont (endblock k) ≡ callcont k
    callcont-stop : callcont stop ≡ stop
    callcont-returnto : ∀ { n params ret } id (F : Function n params ret) σ E k →
      callcont (returnto id F σ E k) ≡ returnto id F σ E k

    -- findlabel
    findlabel : Label → Statement → Continuation → Maybe (Statement × Continuation)
    findlabel-skip : ∀ l k → findlabel l skip k ≡ nothing
    findlabel-assignment : ∀ l k τ v e → findlabel l (assignment {τ} v e) k ≡ nothing
    findlabel-mem-write : ∀ l k τ a e → findlabel l (mem-write {τ} a e) k ≡ nothing
    findlabel-func-call-unit : ∀ l k β v F → findlabel l (func-call {0} {_} {β} v F) k ≡ nothing
    findlabel-func-call-args : ∀ l k n h t β v F Args → findlabel l (func-call {ℕ.suc n} {h Vec.∷ t} {β} v F Args) k ≡ nothing
    findlabel-tailcall-unit : ∀ l k β F → findlabel l (tailcall {0} {_} {β} F) k ≡ nothing
    findlabel-tailcall-args : ∀ l k n h t β F Args → findlabel l (tailcall {ℕ.suc n} {h Vec.∷ t} {β} F Args) k ≡ nothing
    findlabel-return : ∀ l k τ e → findlabel l (return {τ} e) k ≡ nothing
    findlabel-sequence₁ : ∀ l k s₁ s₂ → ¬ (findlabel l s₁ (cons s₂ k) ≡ nothing) → findlabel l (sequence s₁ s₂) k ≡ findlabel l s₁ (cons s₂ k)
    findlabel-sequence₂ : ∀ l k s₁ s₂ → findlabel l s₁ (cons s₂ k) ≡ nothing → findlabel l (sequence s₁ s₂) k ≡ findlabel l s₂ k
    findlabel-if-else₁ : ∀ l k a s₁ s₂ → ¬ (findlabel l s₁ k ≡ nothing) → findlabel l (if-else a s₁ s₂) k ≡ findlabel l s₁ k
    findlabel-if-else₂ : ∀ l k a s₁ s₂ → findlabel l s₁ k ≡ nothing → findlabel l (if-else a s₁ s₂) k ≡ findlabel l s₂ k
    findlabel-loop : ∀ l k s → findlabel l (loop s) k ≡ findlabel l s (cons (loop s) k)
    findlabel-block : ∀ l k s → findlabel l (block s) k ≡ findlabel l s (endblock k)
    findlabel-exit : ∀ l k n → findlabel l (exit n) k ≡ nothing
    findlabel-switch : ∀ l k e L → findlabel l (switch e L) k ≡ nothing
    findlabel-label-eq : ∀ l k l' s → l ≡ l' → findlabel l (label l' s) k ≡ just (s ,' k)
    findlabel-label-neq : ∀ l k l' s → ¬ (l ≡ l') → findlabel l (label l' s) k ≡ findlabel l s k

    -- Environment extension
    extend : ∀ { α } → Environment → Variable α → Value α → Environment
    extend-assignment : ∀ { α } (id : Variable α) v E →
      id ↦ v ∈ extend E id v
    extend-superset : ∀ { α β } (x : Variable α) v (y : Variable β) w E →
      x ↦ v ∈ E → (¬ α ≡ β) ⊎ Σ (α ≡ β) (λ { _≡_.refl → ¬ x ≡ y }) → x ↦ v ∈ extend E y w

    -- Memory extension
    store : ∀ { τ } → MemoryState → Stack → ℕᵇ → Value τ → MemoryState
    store-assignment : ∀ { α } ptr (v : Value α) M b →
      ptr ↦ v ∈ (store M b ptr v) , b
    store-superset : ∀ { α β } x (v : Value α) y (w : Value β) M b →
      x ↦ v ∈ M , b → (¬ α ≡ β) ⊎ Σ (α ≡ β) (λ { _≡_.refl → ¬ x ≡ y }) →
      x ↦ v ∈ (store M b y w) , b
    

    -- Transition semantics, part 1: statements
    ↝-skip-cons : ∀ G {n p r} (F : Function n p r) s k σ E M →
      G ⊢ 𝓢 F skip (cons s k) σ E M ~[ ε ]↝ 𝓢 F s k σ E M
    ↝-skip-endblock : ∀ G {n p r} (F : Function n p r) k σ E M →
      G ⊢ 𝓢 F skip (endblock k) σ E M ~[ ε ]↝ 𝓢 F skip k σ E M
    ↝-assignment : ∀ G σ E M {α} (a : Expr α) v {n p r} (F : Function n p r) id k →
      G , σ , E , M ⊢ a ⇒ v →
      -------------------------------------------------------------------------
      G ⊢ 𝓢 F (assignment id a) k σ E M ~[ ε ]↝ 𝓢 F skip k σ (extend E id v) M
    ↝-mem-write : ∀ G σ E M a₁ b δ {α} a₂ (v : Value α) {n p r} (F : Function n p r) k →
      G , σ , E , M ⊢ a₁ ⇒ ⌊ptr b , δ ⌋ →
      G , σ , E , M ⊢ a₂ ⇒ v →
      -------------------------------------------------------------------------
      G ⊢ 𝓢 F (mem-write a₁ a₂) k σ E M ~[ ε ]↝ 𝓢 F skip k σ E (store M b δ v)
