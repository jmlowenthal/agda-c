open import streams
open import Category.Monad.State using (State)
open import Data.Vec using (Vec) renaming (_∷_ to _∷ᵥ_; [] to []ᵥ)

module Eval where

applyOperator : ∀ { α β γ Γ : Set } → (α → β → γ) → State Γ α → State Γ β → State Γ γ
applyOperator f x y state =
  let x' , state' = x state in
  let y' , state'' = y state' in
    f x' y' , state''

encode : ∀ { α : c_type } → ⟦ α ⟧ → ℤ
encode { Void } _ = int 0
encode { Char } = int ∘ Data.Char.toℕ
encode { Int } = id
encode { Bool } Data.Bool.false = int 0
encode { Bool } Data.Bool.true = int 1
encode { Array α n } x = int 0 -- Do not use, should be able to force this by typing...

updateMapForArray :
  ∀ { α n } → String → ⟦ Array α n ⟧ → (String → ℤ) → (String → ℤ)
updateMapForArray name []ᵥ = id
updateMapForArray {_} {ℕ.suc n} name (x ∷ᵥ arr) f =
  let f' = updateMapForArray name arr f in
    λ var →
      If var ==ₛ name ++ (Data.Nat.Show.show n)
      then encode x else f' name

safediv : ℤ → ℤ → ℤ
safediv x (int 0) = int 0
safediv x Data.Integer.+[1+ n ] = x /ᵢ (Data.Integer.+[1+ n ])
safediv x (ℤ.negsuc n) = x /ᵢ (ℤ.negsuc n)

impl : C
C.Code impl α = State (String → ℤ) ⟦ α ⟧
C.Ref impl α = C.Code impl α
--(impl C.∈ x) n = let x' , _ = x (λ _ → int 0) in (int 0 <ᵢ x') × (x' <ᵢ int n)
C.⟨ impl ⟩ n state = n , state
(impl C.+ x) y = applyOperator (_+ᵢ_) x y
(impl C.* x) y = applyOperator (_*ᵢ_) x y
(impl C.- x) y = applyOperator (_-ᵢ_) x y
(impl C./ x) y state = 
  let x' , state' = x state in
  let y' , state'' = y state' in
    (safediv x' y') , state''
C.true impl state = Data.Bool.true , state
C.false impl state = Data.Bool.false , state
(impl C.|| x) y = applyOperator Data.Bool._∨_ x y
(impl C.&& x) y = applyOperator Data.Bool._∧_ x y
(C.if impl then cond else a) b state =
  let cond' , state' = cond state in
    (If cond' then a else b) state'
C.[] impl state = []ᵥ , state
(impl C.∷ x) y = applyOperator (_∷ᵥ_) x y
C._[_] impl {_} {n} arr i state = {!!}
(C.★ impl) x state = {!!}
C._≔_ impl x y state = {!!}
(impl C.； x) f state = {!!}
C.decl impl α f state = {!!}
