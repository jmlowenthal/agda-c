open import C.Base
open import Data.List
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality

open C ⦃ ... ⦄

module Streams.Theorem1 ⦃ _ : C ⦄ where

-- THEOREM 1 (Stream Fusion to Completeness, Kiselyov et al.)
-- Any well-typed pipeline generator — built by composing a stream producer (ofArr or unfold) with an arbitrary combination of transformers (map, filter, take, flatmap, zipWith) followed by a reducer (fold) — terminates, provided the user-generators do. The resulting code — with the sole exception of pipelines zipping two flat-mapped streams (excluded in our library) — constructs no data structures beyond those constructed by the user-generators.

-- QED.

-- THEOREM 2
-- TODO: check in Kiselyov et al. for claim to the effect of:
-- Any well-typed pipeline generate produces code with a single outermost loop. (and only one branch of loops)


data StreamProducer : Set where

data StreamTransformer : Set where

data StreamReducer : Set where

build : StreamProducer → List StreamTransformer → StreamReducer → Statement

data NoAllocations : Statement → Set where
  ifthenelse : ∀ { c s₁ s₂ }
    → NoAllocations s₁ → NoAllocations s₂
    → NoAllocations (if c then s₁ else s₂)
  assignment : ∀ { x e } → NoAllocations (x ≔ e)
  seq : ∀ { s₁ s₂ }
    → NoAllocations s₁ → NoAllocations s₂
    → NoAllocations (s₁ ； s₂)
  
    

theorem-1 : ∀ { p ts r } → {!Terminating (build p ts r)!} × NoAllocations (build p ts r)
