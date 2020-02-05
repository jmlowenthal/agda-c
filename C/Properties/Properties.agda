open import C
open import C.Properties.ReductionSemantics
open import C.Properties.State

open import Algebra.FunctionProperties
open import Data.Bool as 𝔹 using () renaming (Bool to 𝔹)
open import Data.Empty
open import Data.Integer as ℤ using (+_)
open import Data.Integer.Properties as ℤₚ
open import Data.Product using (∃ ; _,_ ; ∃-syntax ; proj₁ ; proj₂)
open import Data.Sum
open import Data.Vec
open import Relation.Binary
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.Construct.Closure.Transitive
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

import Level


module C.Properties.Properties ⦃ _ : C ⦄ ⦃ _ : Semantics ⦄ where

open C.C ⦃ ... ⦄
open Semantics ⦃ ... ⦄
open ≡-Reasoning

-- VALUE JUDGEMENT LEMMAS

-- ⊢-det : ∀ { E α } { e : Expr α } { x y : ⟦ α ⟧ }
--   → E ⊢ e ⇒ val x → E ⊢ e ⇒ val y → x ≡ y
-- ⊢-det {E} {α} {e} {x} {y} ⇒x ⇒y = IsEquivalence.refl ≅ₑ-equiv {e} {E} {x} {y} ⇒x ⇒y

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
  let 0+e⇒0+w = +-eval (nat { n = + 0 }) e⇒w in
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
  let e+0⇒w+0 = +-eval e⇒w (nat { n = + 0 }) in
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

-- +-assoc : Associative _≅ₑ_ _+_
-- +-commute : Commutative _≅ₑ_ _+_
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

Clos : ∀ { n } → (Vec Set n) → Set → Set
Clos [] B = B
Clos (h ∷ t) B = h → Clos t B

lift : ∀ { n } { v : Vec Set n } { A : Set } { B : Set }
  → Clos v (A → B) → A → Clos v B
lift {v = []} clos = clos
lift {v = h ∷ t} clos a x = lift (clos x) a

Closure : ∀ { n } → (Vec Set n) → Set
Closure v = Clos v Statement

infix 0 _≅ₚ_
_≅ₚ_ : ∀ { n } { v : Vec Set n } → Rel (Closure v) Level.zero
_≅ₚ_ {v = []} x y = ∀ { k E } → 𝒮 x k E  ≅ₛ 𝒮 y k E
_≅ₚ_ {v = h ∷ t} x y = {r : h} → _≅ₚ_ {v = t} (x r) (y r)

≅ₚ-refl : ∀ { n } { v : Vec Set n } → Reflexive (_≅ₚ_ {v = v})
≅ₚ-refl {v = []} {x} {k} {E} = IsEquivalence.refl ≅ₛ-equiv
≅ₚ-refl {v = x ∷ v} = ≅ₚ-refl {v = v}

≅ₚ-sym : ∀ { n } { v : Vec Set n } → Symmetric (_≅ₚ_ {v = v})
≅ₚ-sym {v = []} i~j = IsEquivalence.sym ≅ₛ-equiv i~j
≅ₚ-sym {v = x ∷ v} i~j = ≅ₚ-sym {v = v} i~j

≅ₚ-trans : ∀ { n } { v : Vec Set n } → Transitive (_≅ₚ_ {v = v})
≅ₚ-trans {v = []} i~j j~k = IsEquivalence.trans ≅ₛ-equiv i~j j~k
≅ₚ-trans {v = x ∷ v} i~j j~k = ≅ₚ-trans {v = v} i~j j~k

≅ₚ-equiv : ∀ { n } { v : Vec Set n } → IsEquivalence (_≅ₚ_ {v = v})
≅ₚ-equiv = record { refl = ≅ₚ-refl ; sym = ≅ₚ-sym ; trans = ≅ₚ-trans }

postulate ≅ₚ-cong : ∀ { n m } { v : Vec Set n } { w : Vec Set m } → ∀ ( f : Closure v → Closure w ) (x y : Closure v) → x ≅ₚ y → f x ≅ₚ f y

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
β-while = {!!}

≔-subst : ∀ { α } { x : Ref α } { e : Expr α } { f : Expr α → Statement }
  → (x ≔ e ； f (★ x)) ≅ₚ (f e)
-- ≔-subst {α} {x} {e} {f} {k} {E} {S₁} {S₂}
--   with ⊢-total {α} {E} {e}
-- ... | v , E⊢e⇒v
--     with ≅ₛ-subst {f = f} (deref {x ↦ val v , E} {α} {x} x↦v∈x↦v,E) E⊢e⇒v refl
-- ...   | inj₁ (f[★x]↝ω , f[e]↝ω) =
--         let reduction = ↝-seq ◅ ↝-assignment E⊢e⇒v ◅ ↝-nop ◅ ε in
--           inj₁ (↝ω-transᵇ reduction f[★x]↝ω , f[e]↝ω)
-- ...   | inj₂ t = inj₂ (λ x≔e/f[★x]↝*S₁ f[e]↝*S₂ S₁↝̸ S₂↝̸ →
--         let reduction = ↝-seq ◅ ↝-assignment E⊢e⇒v ◅ ↝-nop ◅ ε in
--           t (↝*-det' reduction x≔e/f[★x]↝*S₁ S₁↝̸) f[e]↝*S₂ S₁↝̸ S₂↝̸)

import C.Properties.Unembedding as DeB

decl-elim : ∀ { α } { f : Statement } → (decl α λ x → f) ≅ₚ f
decl-elim {α} {f} = ≅ₛ-decl
