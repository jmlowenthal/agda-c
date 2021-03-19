open import Level
open import Data.List using (List)
open import Data.Product using (∃-syntax)

open import CMinor.Lang.Lang
open import CMinor.Semantics.NaturalExpressionSemantics

module CMinor.Semantics.SmallStepLabelledProgramSemantics.Definitions where

record DefinitionsLevels : Set where
  field
    IdLevel FdLevel ContinuationLevel ProgramStateLevel TransitionLabelLevel
      TransitionLevel : Level
  SuperLevel =
    IdLevel ⊔ FdLevel ⊔ ContinuationLevel ⊔ ProgramStateLevel ⊔ TransitionLabelLevel
      ⊔ TransitionLevel

record Definitions
  {langLevels exprLevels}
  (definitionsLevels : DefinitionsLevels)
  (𝓛 : Lang langLevels)
  (𝓔 : NaturalExpressionSemantics exprLevels 𝓛)
  : Set (suc (DefinitionsLevels.SuperLevel definitionsLevels ⊔ LangLevels.SuperLevel langLevels ⊔ NaturalExpressionSemanticsLevels.SuperLevel exprLevels))
  where

  open Lang 𝓛
  open NaturalExpressionSemantics 𝓔
  open DefinitionsLevels definitionsLevels

  field
    Id? : Set IdLevel -- TODO
    Fd : Set

    -- CONTINUATIONS
    Continuation : Set ContinuationLevel
    stop : Continuation  -- initial continuation
    cons : Statement → Continuation → Continuation  -- continue with s, then do as k
    endblock : Continuation → Continuation  -- leave a block, then do as k
    returnto : ∀ { n params ret } → Id? → Function n params ret → Stack → Environment → Continuation → Continuation  -- return to caller

    -- STATES
    ProgramState : Set ProgramStateLevel
    𝓢 : ∀ { n params ret } → Function n params ret → Statement → Continuation → Stack → Environment → MemoryState → ProgramState
    𝓒 : Fd → List (∃[ α ] (Value α)) → Continuation → MemoryState → ProgramState
    𝓡 : ∀ { α } → Value α → Continuation → MemoryState → ProgramState

    -- TRANSITION LABELS
    TransitionLabel : Set TransitionLabelLevel
    ε : TransitionLabel

    -- TRANSITIONS
    _⊢_~[_]↝_ : GlobalEnvironment → ProgramState → TransitionLabel → ProgramState → Set TransitionLevel
