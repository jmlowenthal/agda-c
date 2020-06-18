open import C.Lang
open import C.Semantics.SmallStep.Model

module C.Semantics.SmallStep.Properties ⦃ _ : Lang ⦄ ⦃ _ : Semantics ⦄ where


-- Expression properties
open import C.Semantics.SmallStep.Properties.Expression public

-- Program properties
open import C.Semantics.SmallStep.Properties.Equivalence public
open import C.Semantics.SmallStep.Properties.Properties public
open import C.Semantics.SmallStep.Properties.Nested public
open import C.Semantics.SmallStep.Properties.Congruence public
