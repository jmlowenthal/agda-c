open import C
open import C.Properties.ReductionSemantics
open import C.Properties.State

open import Algebra.FunctionProperties
open import Data.Bool as 𝔹 using () renaming (Bool to 𝔹)
open import Data.Empty
open import Data.Nat as ℕ using (ℕ)
open import Data.Integer as ℤ using (+_)
open import Data.Integer.Properties as ℤₚ using ()
open import Data.Product using (∃ ; _,_ ; ∃-syntax ; proj₁ ; proj₂)
open import Data.Sum
open import Data.Vec
open import Relation.Binary
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.Construct.Closure.Transitive
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Function.Nary.NonDependent

import Level


module C.Properties.Properties ⦃ _ : C ⦄ ⦃ _ : Semantics ⦄ where

open C.C ⦃ ... ⦄
open Semantics ⦃ ... ⦄
open ≡-Reasoning

-- VALUE JUDGEMENT LEMMAS

cong₃ : ∀ { a b c d : Level.Level } { A : Set a } { B : Set b } { C : Set c } { D : Set d }
  → ∀ (f : A → B → C → D) {x y u v a b}
  → x ≡ y → u ≡ v → a ≡ b → f x u a ≡ f y v b
cong₃ f refl refl refl = refl

⊢-cong : ∀ { E₁ E₂ α } { e₁ e₂ : Expr α } { x : ⟦ α ⟧ } { v₁ v₂ : Value α x }
  → E₁ ≡ E₂ → e₁ ≡ e₂ → v₁ ≡ v₂ → E₁ ⊢ e₁ ⇒ v₁ ≡ E₂ ⊢ e₂ ⇒ v₂
⊢-cong = cong₃ _⊢_⇒_


-- EXPRESSION EQUIVALENCE

+-left-id : LeftIdentity _≅ₑ_ (⟨ + 0 ⟩) _+_
+-left-id e {E} {v} {w} 0+e⇒v e⇒w =
  let 0+e⇒0+w = +-eval (nat (+ 0)) e⇒w in
  let v≡0+w = ⊢-det 0+e⇒v 0+e⇒0+w in
  begin
    v
    ≡⟨ v≡0+w ⟩
    + 0 ℤ.+ w
    ≡⟨ ℤₚ.+-identityˡ w ⟩
    w
  ∎

+-right-id : RightIdentity _≅ₑ_ (⟨ + 0 ⟩) _+_
+-right-id e {E} {v} {w} e+0⇒v e⇒w =
  let e+0⇒w+0 = +-eval e⇒w (nat (+ 0)) in
  let v≡w+0 = ⊢-det e+0⇒v e+0⇒w+0 in
  begin
    v
    ≡⟨ v≡w+0 ⟩
    w ℤ.+ + 0
    ≡⟨ ℤₚ.+-identityʳ w ⟩
    w
  ∎

+-id : Identity _≅ₑ_ (⟨ + 0 ⟩) _+_
+-id = +-left-id , +-right-id

+-assoc : Associative _≅ₑ_ _+_
+-assoc x y z {E} {v} {w} [x+y]+z⇒v x+[y+z]⇒w =
  let x' , ⇒x' = ⊢-total {e = x} in
  let y' , ⇒y' = ⊢-total {e = y} in
  let z' , ⇒z' = ⊢-total {e = z} in
  begin
    v
    ≡⟨ ⊢-det [x+y]+z⇒v (+-eval (+-eval ⇒x' ⇒y') ⇒z') ⟩
    (x' ℤ.+ y') ℤ.+ z'
    ≡⟨ ℤₚ.+-assoc x' y' z' ⟩
    x' ℤ.+ (y' ℤ.+ z')
    ≡⟨ ⊢-det (+-eval ⇒x' (+-eval ⇒y' ⇒z')) x+[y+z]⇒w ⟩
    w
  ∎

+-comm : Commutative _≅ₑ_ _+_
+-comm x y {E} {v} {w} x+y⇒v y+x⇒w =
  let x' , ⇒x' = ⊢-total {e = x} in
  let y' , ⇒y' = ⊢-total {e = y} in
  begin
    v
    ≡⟨ ⊢-det x+y⇒v (+-eval ⇒x' ⇒y') ⟩
    x' ℤ.+ y'
    ≡⟨ ℤₚ.+-comm x' y' ⟩
    y' ℤ.+ x'
    ≡⟨ ⊢-det (+-eval ⇒y' ⇒x') y+x⇒w ⟩
    w
  ∎

-- *-id : Identity _≅ₑ_ (⟨ + 1 ⟩) _*_
-- *-zero : Zero _≅ₑ_ (⟨ + 0 ⟩) _*_
-- *-assoc : Associative _≅ₑ_ _*_
-- *-commute : Commutative _≅ₑ_ _*_
-- ∸-id : Identity _≅ₑ_ (⟨ + 0 ⟩) _-_
-- /-id : Identity _≅ₑ_ (⟨ + 1 ⟩) _/_
-- -- TODO: algebra properties of _<_ _<=_ _>_ _>=_ _==_ using standard library algebra
-- <-trans : ∀ { x y z : Expr Int } → x < y ≅ₑ true → y < z ≅ₑ true → x < z ≅ₑ true
-- ||-id : Identity _≅ₑ_ false _||_
-- ||-zero : Zero _≅ₑ_ true _||_
-- ||-assoc : Associative _≅ₑ_ _||_
-- ||-commute : Commutative _≅ₑ_ _||_
-- &&-id : Identity _≅ₑ_ true _&&_
-- &&-zero : Zero _≅ₑ_ false _&&_
-- &&-assoc : Associative _≅ₑ_ _&&_
-- &&-commute : Commutative _≅ₑ_ _&&_ 


-- PROGRAM EQUIVALENCE

L0 : ∀ { n } → Levels n
L0 {0} = _
L0 {ℕ.suc n} = Level.zero , L0

infix 0 _≅ₚ_
_≅ₚ_ : ∀ { n } { v : Sets n L0 } → Rel (v ⇉ Statement) Level.zero
_≅ₚ_ {0} {lift} x y = ∀ { k E } → 𝒮 x k E ≅ₛ 𝒮 y k E
_≅ₚ_ {ℕ.suc n} {h , t} x y = {r : h} → _≅ₚ_ {v = t} (x r) (y r)

≅ₚ-refl : ∀ { n } { v : Sets n L0 } → Reflexive (_≅ₚ_ {v = v})
≅ₚ-refl {0} {lift} {x} {k} {E} = IsEquivalence.refl ≅ₛ-equiv
≅ₚ-refl {ℕ.suc n} {x , v} = ≅ₚ-refl {v = v}

≅ₚ-sym : ∀ { n } { v : Sets n L0 } → Symmetric (_≅ₚ_ {v = v})
≅ₚ-sym {0} {lift} i~j = IsEquivalence.sym ≅ₛ-equiv i~j
≅ₚ-sym {ℕ.suc n} {x , v} i~j = ≅ₚ-sym {v = v} i~j

≅ₚ-trans : ∀ { n } { v : Sets n L0 } → Transitive (_≅ₚ_ {v = v})
≅ₚ-trans {0} {lift} i~j j~k = IsEquivalence.trans ≅ₛ-equiv i~j j~k
≅ₚ-trans {ℕ.suc n} {x , v} i~j j~k = ≅ₚ-trans {v = v} i~j j~k

≅ₚ-equiv : ∀ { n } { v : Sets n L0 } → IsEquivalence (_≅ₚ_ {v = v})
≅ₚ-equiv = record { refl = ≅ₚ-refl ; sym = ≅ₚ-sym ; trans = ≅ₚ-trans }

≅ₚ-setoid : ∀ { n } { v : Sets n L0 } → Setoid _ _
≅ₚ-setoid {v = v} = record {
  Carrier = v ⇉ Statement ;
  _≈_ = _≅ₚ_ ;
  isEquivalence = ≅ₚ-equiv }

import Relation.Binary.Reasoning.Setoid as Reasoning
module ≅-Reasoning = Reasoning (≅ₚ-setoid {0})
  renaming (_≈⟨_⟩_ to _≅⟨_⟩_ ; _≈˘⟨_⟩_ to _≅˘⟨_⟩_)

open ≅-Reasoning
  renaming (_≡⟨⟩_ to _≡'⟨⟩_ ; begin_ to begin'_ ; _∎ to _∎')

postulate ≅ₚ-cong : ∀ { n } { v : Sets n L0 } (f : (v ⇉ Statement) → Statement) (x y : v ⇉ Statement) → x ≅ₚ y → f x ≅ₚ f y
-- ≅ₚ-cong {v = []} {[]} f x y x≅y {k} {E} =
--   ≅ₛ-cong (λ { (𝒮 s k E) → 𝒮 (f s) k E }) (𝒮 x k E) (𝒮 y k E) x≅y
-- ≅ₚ-cong {v = α ∷ αs} {[]} f x y x≅y {k} {E} =
--   let g : (r : α) → f (λ _ → x r) ≅ₚ f (λ _ → y r)
--       g r = ≅ₚ-cong {v = αs} {[]} (λ v → f (λ _ → v)) _ _ (x≅y {r})
--   in
--     {!g ? {k} {E}!}
-- ≅ₚ-cong {v = v} {β ∷ βs} f x y x≅y {r} =
--   ≅ₚ-cong {v = v} {βs} (λ c → f c r) _ _ x≅y

β-if-true : ∀ { x y : Statement }
  → (if true then x else y) ≅ₚ x
β-if-true = ↝*⇒≅ₛ (↝-if-true true-eval ◅ ε)

β-if-false : ∀ { x y : Statement } → if false then x else y ≅ₚ y
β-if-false = ↝*⇒≅ₛ (↝-if-false false-eval ◅ ε)

η-if : ∀ { cond : Expr Bool } { e : Statement } → if cond then e else e ≅ₚ e
η-if {cond}
  with ⊢-total {e = cond}
... | (𝔹.false , ⇒false) = ↝*⇒≅ₛ (↝-if-false ⇒false ◅ ε)
... | (𝔹.true , ⇒true) = ↝*⇒≅ₛ (↝-if-true ⇒true ◅ ε)

β-while : ∀ { e₁ : Expr Bool } { e₂ : Statement }
  → while e₁ then e₂ ≅ₚ if e₁ then (e₂ ； while e₁ then e₂) else nop
β-while = ↝*⇒≅ₛ (↝-while ◅ ε)

≔-subst : ∀ { α } { x : Ref α } { e : Expr α } { f : Expr α → Statement }
  → (x ≔ e ； f (★ x)) ≅ₚ (f e)
≔-subst {α} {x} {e} {f} {k} {E}
  with ⊢-total {α} {E} {e}
... | v , ⇒v
    with ≅ₛ-subst {f = f} (deref {x ↦ val v , E} {α} {x} x↦v∈x↦v,E) ⇒v refl
...   | inj₁ (A , f[★x]↝A , f[e]↝A) =
        let reduction = ↝-seq ◅ ↝-assignment ⇒v ◅ ↝-nop ◅ ε in
          inj₁ (A , reduction ◅◅ f[★x]↝A , f[e]↝A)
...   | inj₂ (f[★x]↝ω , f[e]↝ω) =
        let reduction = ↝-seq ◅ ↝-assignment ⇒v ◅ ↝-nop ◅ ε in
          inj₂ (↝ω-transᵇ reduction f[★x]↝ω , f[e]↝ω)

decl-elim : ∀ { α } { f : Statement } → (decl α λ x → f) ≅ₚ f
decl-elim {α} {f} = ≅ₛ-decl
