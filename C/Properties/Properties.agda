open import C
open import C.Properties.ReductionSemantics
open import C.Properties.State

open import Algebra.FunctionProperties
open import Data.Empty
open import Data.Integer as ℤ using (+_)
open import Data.Integer.Properties as ℤₚ
open import Data.Product using (∃ ; _,_)
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

⊢-det : ∀ { E α } { e : Expr α } { x y : ⟦ α ⟧ }
  → E ⊢ e ⇒ val x → E ⊢ e ⇒ val y → x ≡ y
⊢-det {E} {α} {e} {x} {y} ⇒x ⇒y = IsEquivalence.refl ≅ₑ-equiv {e} {E} {x} {y} ⇒x ⇒y

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


-- REDUCTION LEMMAS

↝*-trans : Transitive _↝*_
↝*-trans = _◅◅_

↝*-to-↝⁺ : ∀ { A B C } → A ↝ B → B ↝* C → A ↝⁺ C
↝*-to-↝⁺ A↝B ε = Plus′.[ A↝B ]
↝*-to-↝⁺ A↝B (B↝X ◅ X↝*C) = A↝B ∷ (↝*-to-↝⁺ B↝X X↝*C)

↝⁺-to-↝* : ∀ { A B } → A ↝⁺ B → A ↝* B
↝⁺-to-↝* Plus′.[ A↝B ] = A↝B ◅ ε
↝⁺-to-↝* (A↝X ∷ X↝⁺B) = A↝X ◅ (↝⁺-to-↝* X↝⁺B)

↝̸-transᵇ : ∀ { S S' : State }
  → S ↝* S' → Terminating S' → Terminating S
↝̸-transᵇ {S} {S'} S↝*S' (X , S'↝*X , X↝̸) = X , (S↝*S' ◅◅ S'↝*X) , X↝̸

↝̸-transᶠ : ∀ { S S' : State }
  → S ↝* S' → Terminating S → Terminating S'
↝̸-transᶠ ε S↝̸ = S↝̸
↝̸-transᶠ (S↝X ◅ X↝*S') (S , ε , S↝̸) = ⊥-elim (S↝̸ _ S↝X)
↝̸-transᶠ (S↝A ◅ A↝*S') (X , S↝Y ◅ Y↝*X , X↝̸)
  with ↝-det S↝A S↝Y
... | refl = ↝̸-transᶠ A↝*S' (X , Y↝*X , X↝̸)

↝ω-transᵇ : ∀ { X Y : State }
  → X ↝* Y → ¬ Terminating Y → ¬ Terminating X
↝ω-transᵇ {X} {Y} X↝*Y Y↝ω X↝̸ = Y↝ω (↝̸-transᶠ X↝*Y X↝̸)

↝ω-transᶠ : ∀ { X Y : State }
  → X ↝* Y → ¬ Terminating X → ¬ Terminating Y
↝ω-transᶠ {X} {Y} X↝*Y X↝ω Y↝̸ = X↝ω (↝̸-transᵇ X↝*Y Y↝̸)

↝*-det : ∀ { S S₁ S₂ }
  → Stuck S₁ → Stuck S₂ → S ↝* S₁ → S ↝* S₂ → S₁ ≡ S₂
↝*-det S₁↝̸ S₂↝̸ ε ε = refl
↝*-det S↝̸ S₂↝̸ ε (_◅_ {j = X} S↝X X↝*S₂) = ⊥-elim (S↝̸ X S↝X)
↝*-det S₁↝̸ S↝̸ (_◅_ {j = X} S↝X X↝*S₂) ε = ⊥-elim (S↝̸ X S↝X)
↝*-det S₁↝̸ S₂↝̸ (S↝X ◅ X↝*S₁) (S↝Y ◅ Y↝*S₂)
  with ↝-det S↝X S↝Y
... | refl = ↝*-det S₁↝̸ S₂↝̸ X↝*S₁ Y↝*S₂

↝*-det' : ∀ { S S₁ S₂ }
  → S ↝* S₁ → S ↝* S₂ → Stuck S₂ → S₁ ↝* S₂
↝*-det' ε S↝*S₂ _ = S↝*S₂
↝*-det' (S↝X ◅ X↝*S₁) ε S↝̸ = ⊥-elim (S↝̸ _ S↝X)
↝*-det' (S↝X ◅ X↝*S₁) (S↝Y ◅ Y↝*S₂) S₂↝̸
  with ↝-det S↝X S↝Y
... | refl = ↝*-det' X↝*S₁ Y↝*S₂ S₂↝̸


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
≅ₚ-refl {v = []} {x} {k} {E} {wf₁} {wf₂} = IsEquivalence.refl ≅ₛ-equiv
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

β-if-true' : ∀ { x y : Statement } { k E S₁ S₂ }
  → 𝒮 (if true then x else y) k E ↝* S₁ → 𝒮 x k E ↝* S₂ → Stuck S₁ → Stuck S₂ → S₁ ≡ S₂
β-if-true' {x} {_} {k} {E} ε _ S₁↝̸ _ = ⊥-elim (S₁↝̸ (𝒮 x k E) (↝-if-true true-eval))
β-if-true' {x} {y} {k} {E} (if↝R ◅ R↝*S₁) x↝*S₂ S₁↝̸ S₂↝̸
  with ↝-det if↝R (↝-if-true true-eval)
... | refl = ↝*-det S₁↝̸ S₂↝̸ R↝*S₁ x↝*S₂

β-if-true : ∀ { x y : Statement }
  → (if true then x else y) ≅ₚ x
β-if-true = inj₂ β-if-true'

β-if-false : ∀ { x y : Statement } → if false then x else y ≅ₚ y
β-if-false = {!!}

η-if : ∀ { cond : Expr Bool } { e : Statement } → if cond then e else e ≅ₚ e
η-if = {!!}

β-while : ∀ { e₁ : Expr Bool } { e₂ : Statement }
  → while e₁ then e₂ ≅ₚ if e₁ then (e₂ ； while e₁ then e₂) else nop
β-while = {!!}

≔-subst : ∀ { α } { x : Ref α } { e : Expr α } { f : Expr α → Statement }
  → (x ≔ e ； f (★ x)) ≅ₚ (f e)
≔-subst {α} {x} {e} {f} {k} {E} {S₁} {S₂}
  with ⊢-total {α} {E} {e}
... | v , E⊢e⇒v
    with ≅ₛ-subst {f = f} (deref {x ↦ val v , E} {α} {x} x↦v∈x↦v,E) E⊢e⇒v refl
...   | inj₁ (f[★x]↝ω , f[e]↝ω) =
        let reduction = ↝-seq ◅ ↝-assignment E⊢e⇒v ◅ ↝-nop ◅ ε in
          inj₁ (↝ω-transᵇ reduction f[★x]↝ω , f[e]↝ω)
...   | inj₂ t = inj₂ (λ x≔e/f[★x]↝*S₁ f[e]↝*S₂ S₁↝̸ S₂↝̸ →
        let reduction = ↝-seq ◅ ↝-assignment E⊢e⇒v ◅ ↝-nop ◅ ε in
          t (↝*-det' reduction x≔e/f[★x]↝*S₁ S₁↝̸) f[e]↝*S₂ S₁↝̸ S₂↝̸)

decl-elim : ∀ { α } { f : Statement } → (decl α λ x → f) ≅ₚ f
decl-elim {α} {f} = {!!}
