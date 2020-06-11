open import Algebra.FunctionProperties
open import C.Lang
open import C.Semantics.SmallStep.Model
open import Codata.Musical.Colist as Colist
open import Codata.Musical.Notation
open import Data.Bool as 𝔹 using () renaming (Bool to 𝔹)
open import Data.Empty
open import Data.Integer as ℤ using (+_)
open import Data.Integer.Properties as ℤₚ using ()
open import Data.List as L using (List ; _∷_ ; [])
open import Data.Nat as ℕ using (ℕ)
open import Data.Product using (∃ ; _,_ ; ∃-syntax ; proj₁ ; proj₂)
open import Data.Sum
open import Data.Vec
open import Function.Nary.NonDependent
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Size

import Level
import Codata.Musical.Conat as Coℕ

module C.Semantics.SmallStep.Properties.Properties ⦃ _ : Lang ⦄ ⦃ _ : Semantics ⦄ where

open Lang ⦃ ... ⦄
open Semantics ⦃ ... ⦄
open ≡-Reasoning

-- PROGRAM EQUIVALENCE

L0 : ∀ { n } → Levels n
L0 {0} = _
L0 {ℕ.suc n} = Level.zero , L0

infix 0 _≅ₚ_
_≅ₚ_ : ∀ { n } { v : Sets n L0 } → Rel (v ⇉ Statement) Level.zero
_≅ₚ_ {0} x y = ∀ { k E } → 𝒮 x k E ≅ₛ 𝒮 y k E
_≅ₚ_ {ℕ.suc n} {_ , v} x y = ∀ { r } → _≅ₚ_ (x r) (y r)

≅ₚ-refl : ∀ { n } { v : Sets n L0 } → Reflexive (_≅ₚ_ {v = v})
≅ₚ-refl {ℕ.zero} {Level.lift _} {_} = ≅ₛ-refl
≅ₚ-refl {ℕ.suc n} {x , v} = (≅ₚ-refl {v = v})

≅ₚ-sym : ∀ { n } { v : Sets n L0 } → Symmetric (_≅ₚ_ {v = v})
≅ₚ-sym {0} {lift} i~j = ≅ₛ-sym i~j
≅ₚ-sym {ℕ.suc n} {x , v} i~j = ≅ₚ-sym {v = v} i~j

≅ₚ-trans : ∀ { n } { v : Sets n L0 } → Transitive (_≅ₚ_ {v = v})
≅ₚ-trans {0} {lift} i~j j~k = ≅ₛ-trans i~j j~k
≅ₚ-trans {ℕ.suc n} {x , v} i~j j~k = ≅ₚ-trans {v = v} i~j j~k

≅ₚ-equiv : ∀ { n } { v : Sets n L0 } → IsEquivalence (_≅ₚ_ {v = v})
≅ₚ-equiv = record { refl = ≅ₚ-refl ; sym = ≅ₚ-sym ; trans = ≅ₚ-trans }

≅ₚ-setoid : ∀ { n } { v : Sets n L0 } → Setoid _ _
≅ₚ-setoid {i} {v = v} = record {
  Carrier = v ⇉ Statement ;
  _≈_ = _≅ₚ_ ;
  isEquivalence = ≅ₚ-equiv }

import Relation.Binary.Reasoning.Setoid as Reasoning
module ≅-Reasoning = Reasoning (≅ₚ-setoid {0})
  renaming (_≈⟨_⟩_ to _≅⟨_⟩_ ; _≈˘⟨_⟩_ to _≅˘⟨_⟩_)
module ≅R = ≅-Reasoning
open ≅R
module ≈R = Reasoning [≈]-setoid
open ≈R

postulate ≅ₚ-cong : ∀ { n } { v : Sets n L0 } (f : (v ⇉ Statement) → Statement) (x y : v ⇉ Statement) → x ≅ₚ y → f x ≅ₚ f y

β-if-true : ∀ { x y : Statement }
  → (if true then x else y) ≅ₚ x
β-if-true = ↝⇒≅ₛ (↝-if-true true-eval)

β-if-false : ∀ { x y : Statement } → if false then x else y ≅ₚ y
β-if-false = ↝⇒≅ₛ (↝-if-false false-eval)

η-if : ∀ { cond : Expr Bool } { e : Statement } → if cond then e else e ≅ₚ e
η-if {cond}
  with ⊢-total {e = cond}
... | (𝔹.false , ⇒false) = ↝⇒≅ₛ (↝-if-false ⇒false)
... | (𝔹.true , ⇒true) = ↝⇒≅ₛ (↝-if-true ⇒true)

β-while : ∀ { e₁ : Expr Bool } { e₂ : Statement }
  → while e₁ then e₂ ≅ₚ if e₁ then (e₂ ； while e₁ then e₂) else nop
β-while = ↝⇒≅ₛ ↝-while

≔-subst : ∀ { α } { x : Ref α } { e : Expr α } { f : Expr α → Statement }
  → x ≔ e ； f (★ x) ≅ₚ f e
≔-subst {α} {x} {e} {f} {k} {E} =
  let v , ⇒v = ⊢-total {α} {E} {e} in
    ≈R.begin
      labels (𝒮 (x ≔ e ； f (★ x)) k E)
      ≈⟨ ↝⇒≅ₛ ↝-seq ⟩
      labels (𝒮 (x ≔ e) ((f (★ x)) ∷ k) E)
      ≈⟨ [≈]-reflexive (reduce-det _ (↝-assignment ⇒v ∷ ♯ reduce _)) ⟩
      labels-of (↝-assignment ⇒v ∷ _) 
      ≈⟨ left ignore-↦ (♯ [≈]-refl) ⟩
      labels (𝒮 nop ((f (★ x)) ∷ k) (x Env.↦ v , E))
      ≈⟨ ↝⇒≅ₛ ↝-nop ⟩
      labels (𝒮 (f (★ x)) k (x Env.↦ v , E))
      ≈⟨ ≅ₛ-subst (deref x↦v∈x↦v,E) ⇒v refl ⟩
      labels (𝒮 (f e) k E)
    ≈R.∎

decl-elim : ∀ { α } { f : Statement } → (decl α λ x → f) ≅ₚ f
decl-elim {α} {f} = ≅ₛ-decl

nested-while-loop : ∀ { s : Statement }
  → while true then s ≅ₚ while true then (while true then s)
nested-while-loop {s} {k} {E} =
  ≈R.begin
    labels (𝒮 (while true then s) k E)
  ≈⟨ ↝*⇒≅ₛ (↝-while ◅ ♯ (↝-if-true true-eval ◅ ♯ (↝-seq ◅ ♯ ε))) ⟩
    labels (𝒮 s ((while true then s) ∷ k) E)
  ≈˘⟨ ↝⇒≅ₛ ↝-nop ⟩
    labels (𝒮 nop (s ∷ (while true then s) ∷ k) E)
  ≈⟨
    cont-equiv
      (≅ₛ-refl {𝒮 nop (s ∷ []) E})
      (λ E' →
        cont-equiv
          (≈R.begin
            labels (𝒮 nop ((while true then s) ∷ []) E')
            ≈⟨ ↝⇒≅ₛ ↝-nop ⟩
            labels (𝒮 (while true then s) [] E')
            ≈⟨ ≅ₛ-while-true ⟩
            labels (𝒮 (while true then s) ((while true then (while true then s)) ∷ []) E')
            ≈˘⟨ ↝⇒≅ₛ ↝-nop ⟩
            labels (𝒮 nop ((while true then s) ∷ (while true then (while true then s)) ∷ []) E')
          ≈R.∎)
          (λ E'' → ≅ₛ-refl {𝒮 nop k E''}))
  ⟩
    labels (𝒮 nop (s ∷ (while true then s) ∷ (while true then (while true then s)) ∷ k) E)
  ≈⟨ ↝⇒≅ₛ ↝-nop ⟩
    labels (𝒮 s ((while true then s) ∷ (while true then (while true then s)) ∷ k) E)
  ≈˘⟨
    ↝*⇒≅ₛ
      (↝-while
        ◅ ♯ (↝-if-true true-eval
        ◅ ♯ (↝-seq
        ◅ ♯ (↝-while
        ◅ ♯ (↝-if-true true-eval
        ◅ ♯ (↝-seq
        ◅ ♯ ε)))))) ⟩
    labels (𝒮 (while true then (while true then s)) k E)
  ≈R.∎

nested-if : ∀ { e e' : Expr Bool } { s : Statement } { k E }
  → 𝒮 (if e then (if e' then s else nop) else nop) k E ≅ₛ 𝒮 (if (e && e') then s else nop) k E
nested-if {e} {e'} {s} {k} {E}
  with ⊢-total {Bool} {E} {e} | ⊢-total {Bool} {E} {e'}
... | 𝔹.false , ⇒v | _ , ⇒w =
  ≈R.begin
    labels (𝒮 (if e then (if e' then s else nop) else nop) k E)
    ≈⟨ ↝⇒≅ₛ (↝-if-false ⇒v) ⟩
    labels (𝒮 nop k E)
    ≈˘⟨ ↝⇒≅ₛ (↝-if-false (&&-eval ⇒v ⇒w)) ⟩
    labels (𝒮 (if (e && e') then s else nop) k E)
  ≈R.∎
... | 𝔹.true , ⇒v | 𝔹.false , ⇒w =
  ≈R.begin
    labels (𝒮 (if e then (if e' then s else nop) else nop) k E)
    ≈⟨ ↝⇒≅ₛ (↝-if-true ⇒v) ⟩
    labels (𝒮 (if e' then s else nop) k E)
    ≈⟨ ↝⇒≅ₛ (↝-if-false ⇒w) ⟩
    labels (𝒮 nop k E)
    ≈˘⟨ ↝⇒≅ₛ (↝-if-false (&&-eval ⇒v ⇒w)) ⟩
    labels (𝒮 (if (e && e') then s else nop) k E)
  ≈R.∎
... | 𝔹.true , ⇒v | 𝔹.true , ⇒w =
  ≈R.begin
    labels (𝒮 (if e then (if e' then s else nop) else nop) k E)
    ≈⟨ ↝⇒≅ₛ (↝-if-true ⇒v) ⟩
    labels (𝒮 (if e' then s else nop) k E)
    ≈⟨ ↝⇒≅ₛ (↝-if-true ⇒w) ⟩
    labels (𝒮 s k E)
    ≈˘⟨ ↝⇒≅ₛ (↝-if-true (&&-eval ⇒v ⇒w)) ⟩
    labels (𝒮 (if (e && e') then s else nop) k E)
  ≈R.∎
