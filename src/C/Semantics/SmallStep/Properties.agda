open import C.Lang
open import C.Semantics.SmallStep.Model

module C.Semantics.SmallStep.Properties ⦃ _ : Lang ⦄ ⦃ _ : Semantics ⦄ where

open import C.Semantics.SmallStep.Properties.Expression public
open import C.Semantics.SmallStep.Properties.Properties public
