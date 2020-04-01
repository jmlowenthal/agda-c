open import C.Base
open import Data.Nat as ℕ
open import Data.Product using (_×_ ; _,_)
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Streams.Base

open import Data.Vec as Vec using (Vec ; _∷_ ; [])

open C ⦃ ... ⦄

module Streams.Theorem1 ⦃ _ : C ⦄ where

-- THEOREM 1 (Stream Fusion to Completeness, Kiselyov et al.)
-- Any well-typed pipeline generator — built by composing a stream producer (ofArr or unfold) with an arbitrary combination of transformers (map, filter, take, flatmap, zipWith) followed by a reducer (fold) — terminates, provided the user-generators do. The resulting code — with the sole exception of pipelines zipping two flat-mapped streams (excluded in our library) — constructs no data structures beyond those constructed by the user-generators.

-- In order to prove this theorem, we first define, formally, quantification over well-typed pipeline generators "built by composing a stream producer with an arbitrary combination of transformers followed by a reducer". We express each pipeline generator (StreamBuilderSpec) as a sequence of transformers (StreamTransformer), initiated by a producer (StreamProducer), in order to capture the limited scope of allowed stream producers.

data StreamProducer (α : c_type) : Set where
  ofArr~ : ∀ { n } (v : Vec (Expr α) n) → StreamProducer α
  unfold~ : ∀ { ζ } (F : Expr ζ → Expr Bool × Expr α × Expr ζ) (z : Expr ζ) → StreamProducer α

data StreamTransformer : ∀ (α β : Set) → Set₁ where
  map~ : ∀ { α β } (f : α → β) → StreamTransformer α β
  filter~ : ∀ { α } (f : α → Expr Bool) → StreamTransformer α α
  take~ : ∀ { α } (n : Expr Int) → StreamTransformer α α
  flatmap~ : ∀ { α β } (f : α → SStream β) → StreamTransformer α β

data StreamBuilderSpec : Set → Set₁
spec-to-stream : ∀ { A } → StreamBuilderSpec A → SStream A

-- Without considering zipped streams, each pipeline generator is a list of stream transformer functions, notated in reverse order of application for readability. For example, ofArr~ v ▸ map~ f ▸ take 10, is the ≤10-element stream of (f xᵢ) for each xᵢ in the array v.

-- In order to include zipped streams, we also allow two pipeline generator specifications to be combined in a branching manner to produce a zipped stream of their elements, provided they aren't both nested streams as excluded by Theorem 1 and our implementation.

data StreamBuilderSpec where
  [_] : ∀ { α } → StreamProducer α → StreamBuilderSpec (Expr α)
  _▸_ : ∀ { α β } → StreamBuilderSpec α → StreamTransformer α β → StreamBuilderSpec β
  _⋎_⟨_⟩ : ∀ { A B } (x : StreamBuilderSpec A) (y : StreamBuilderSpec B)
    → ∥ spec-to-stream x ∥ₛ ℕ.+ ∥ spec-to-stream y ∥ₛ ℕ.≤ 1
    → StreamBuilderSpec (A × B) --zip

-- The `spec-to-stream` function reifies a pipeline generator specification to a stream datatype, which can then be folded to produce a statement in our object language.

spec-to-stream ([ ofArr~ v ]) = ofArr v
spec-to-stream ([ unfold~ F z ]) = unfold F z
spec-to-stream (spec ▸ map~ f) = map' f (spec-to-stream spec)
spec-to-stream (spec ▸ filter~ f) = filter f (spec-to-stream spec)
spec-to-stream (spec ▸ take~ n) = take n (spec-to-stream spec)
spec-to-stream (spec ▸ flatmap~ f) = flatmap f (spec-to-stream spec)
spec-to-stream (x ⋎ y ⟨ p ⟩) = zip (spec-to-stream x) (spec-to-stream y) {p}

build : ∀ { α ζ }
  → StreamBuilderSpec α → (Expr ζ → α → Expr ζ) → Expr ζ → Ref ζ → Statement
build spec F z = fold F z (spec-to-stream spec)

-- We now formally define what it means for a program to have no additional dynamic allocations. Here we use a natural structual recursive definition.

data NoAllocations : Statement → Set where
  if-allocs : ∀ { c : Expr Bool } { s₁ s₂ }
    → NoAllocations s₁ → NoAllocations s₂
    → NoAllocations (if c then s₁ else s₂)
  ≔-allocs : ∀ { α } { x : Ref α } { e : Expr α } → NoAllocations (x ≔ e)
  ；-allocs : ∀ { s₁ s₂ }
    → NoAllocations s₁ → NoAllocations s₂
    → NoAllocations (s₁ ； s₂)
  decl-allocs : ∀ { α } { f : Ref α → Statement }
    → (∀ x → NoAllocations (f x)) → NoAllocations (decl α f)
  nop-allocs : NoAllocations nop
  for-allocs : ∀ { u l : Expr Int } { f : Ref Int → Statement }
    → (∀ x → NoAllocations (f x)) → NoAllocations (for u to l then f)
  while-allocs : ∀ { e : Expr Bool } { s }
    → NoAllocations s → NoAllocations (while e then s)
  putchar-allocs : ∀ { e : Expr Int }
    → NoAllocations (putchar e)

-- Our fragment of the C language excludes any dynamic memory allocations (using new) and hence all expressible well-typed programs are contain no allocations.
  
theorem-1 : ∀ { α ζ } (spec : StreamBuilderSpec α) (F : Expr ζ → α → Expr ζ) z r
  → NoAllocations (build spec F z r)
theorem-1 [ ofArr~ v ] F z r = {!build [ ofArr~ v ] F z r!}
theorem-1 [ unfold~ F₁ z₁ ] F z r = {!!}
theorem-1 (spec ▸ x) F z r = {!!}
theorem-1 (spec ⋎ spec₁ ⟨ x₁ ⟩) F z r = {!!}

-- THEOREM 2
-- TODO: check in Kiselyov et al. for claim to the effect of:
-- Any well-typed pipeline generate produces code with a single outermost loop. (and only one branch of loops)
