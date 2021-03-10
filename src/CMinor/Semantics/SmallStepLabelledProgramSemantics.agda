open import CMinor.Lang.Lang
open import CMinor.Semantics.NaturalExpressionSemantics

open import Level using (Level ; _⊔_)
open import Data.List as List using (List ; [] ; _∷_)
open import Data.Product as Product using (∃-syntax ; _×_ ; _,_)
open import Data.Maybe as Maybe using (Maybe ; just ; nothing)
open import Data.Vec as Vec using (Vec)
open import Data.Nat as ℕ using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

module CMinor.Semantics.SmallStepLabelledProgramSemantics where

record SmallStepLabelledProgramSemantics (l₁ l₂ l₃ l₄ l₅ l₆ l₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ s k l t : Level) (𝓛 : Lang l₁ l₂ l₃ l₄ l₅ l₆ l₇) (𝓔 : NaturalExpressionSemantics _ _ _ _ _ _ _ e₁ e₂ e₃  e₄ e₅ e₆ e₇ e₈ e₉ 𝓛) : Set (Level.suc {!!}) where

  open Lang 𝓛
  open NaturalExpressionSemantics 𝓔

  field
    Id? : Set -- TODO
    StackData : Set -- TODO

    -- CONTINUATIONS
    Continuation : Set k
    stop : Continuation  -- initial continuation
    cons : Statement → Continuation → Continuation  -- continue with s, then do as k
    endblock : Continuation → Continuation  -- leave a block, then do as k
    returnto : ∀ { n params ret } → Id? → Function n params ret → StackData → Environment → Continuation → Continuation  -- return to caller

    -- STATES
    ProgramState : Set s
    𝓢 : ∀ { n params ret } → Function n params ret → Statement → Continuation → StackData → Environment → MemoryState → ProgramState
    𝓒 : {!Fd!} → List (∃[ α ] (Value α)) → Continuation → MemoryState → ProgramState
    𝓡 : ∀ { α } → Value α → Continuation → MemoryState → ProgramState

    -- TRANSITION LABELS
    TransitionLabel : Set l
    ε : TransitionLabel

    -- TRANSITIONS
    _⊢_~[_]↝_ : GlobalEnvironment → ProgramState → TransitionLabel → ProgramState → Set t

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
    findlabel-label-eq : ∀ l k l' s → l ≡ l' → findlabel l (label l' s) k ≡ just (s , k)
    findlabel-label-neq : ∀ l k l' s → ¬ (l ≡ l') → findlabel l (label l' s) k ≡ findlabel l s k

