open import Level
open import Data.List using (List)
open import Data.Product using (∃-syntax)

open import CMinor.Lang.Lang
open import CMinor.Semantics.NaturalExpressionSemantics

module CMinor.Semantics.SmallStepLabelledProgramSemantics.Definitions where

record Definitions
  {langLevels exprLevels}
  (i k s l t : Level)
  (𝓛 : Lang langLevels)
  (𝓔 : NaturalExpressionSemantics exprLevels 𝓛)
  : Set (suc (i ⊔ k ⊔ s ⊔ l ⊔ t ⊔ LangLevels.SuperLevel langLevels ⊔ NaturalExpressionSemanticsLevels.SuperLevel exprLevels))
  where

  open Lang 𝓛
  open NaturalExpressionSemantics 𝓔

  field
    Id? : Set i -- TODO
    Fd : Set

    -- CONTINUATIONS
    Continuation : Set k
    stop : Continuation  -- initial continuation
    cons : Statement → Continuation → Continuation  -- continue with s, then do as k
    endblock : Continuation → Continuation  -- leave a block, then do as k
    returnto : ∀ { n params ret } → Id? → Function n params ret → Stack → Environment → Continuation → Continuation  -- return to caller

    -- STATES
    ProgramState : Set s
    𝓢 : ∀ { n params ret } → Function n params ret → Statement → Continuation → Stack → Environment → MemoryState → ProgramState
    𝓒 : Fd → List (∃[ α ] (Value α)) → Continuation → MemoryState → ProgramState
    𝓡 : ∀ { α } → Value α → Continuation → MemoryState → ProgramState

    -- TRANSITION LABELS
    TransitionLabel : Set l
    ε : TransitionLabel

    -- TRANSITIONS
    _⊢_~[_]↝_ : GlobalEnvironment → ProgramState → TransitionLabel → ProgramState → Set t
