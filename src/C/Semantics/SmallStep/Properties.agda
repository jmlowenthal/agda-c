open import C.Lang
open import C.Semantics.SmallStep.Model

module C.Semantics.SmallStep.Properties ⦃ _ : Lang ⦄ ⦃ _ : Semantics ⦄ where


-- Expression properties
open import C.Semantics.SmallStep.Properties.Expression.Equivalence public
open import C.Semantics.SmallStep.Properties.Expression.Properties public

-- Program properties
open import C.Semantics.SmallStep.Properties.Program.Reduction public
open import C.Semantics.SmallStep.Properties.Program.Equivalence public
open import C.Semantics.SmallStep.Properties.Program.Properties public
open import C.Semantics.SmallStep.Properties.Program.Nested public
open import C.Semantics.SmallStep.Properties.Program.Congruence public
