module streams where

open import Data.Unit
open import Data.Integer using (ℤ)
  renaming (_+_ to _+ᵢ_; _*_ to _*ᵢ_; _-_ to _-ᵢ_; +_ to int)
open import Data.Integer.DivMod using () renaming (_div_ to _/ᵢ_)
open import Data.Nat using (ℕ; _<_)
import Data.Nat.Show
import Data.Nat.Properties
open import Data.String using (String; _++_; _==_)
import Data.Char
import Data.Bool
open Data.Bool using () renaming (if_then_else_ to If_then_else_)
import Data.List
open import Data.Vec using (Vec) renaming (_∷_ to _∷ᵥ_; [] to []ᵥ)
open import Category.Monad.State using (State)
open import Data.Product
open import Function
open import Relation.Nullary.Decidable using (⌊_⌋)

data c_type : Set where
  Void Char Int Bool : c_type
  Array : c_type → (n : ℕ) → { proof : 0 Data.Nat.< n } → c_type

record C : Set₁ where
  field
    Code : c_type → Set
    Ref : c_type → Set
    --_≃_ : ∀ { α β } → Code α → Code β → Set
    ⟨_⟩ : ℤ → Code Int
    _+_ _*_ _-_ _/_ : Code Int → Code Int → Code Int
    true false : Code Bool
    _||_ _&&_ : Code Bool → Code Bool → Code Bool
    if_then_else_ : ∀ { α } → Code Bool → Code α → Code α → Code α
    _≔_ : ∀ { α } → Ref α → Code α → Code α
    _；_ : ∀ { α β } → Code α → Code β → Code β

open C ⦃ ... ⦄

module Eval where

  ⟦_⟧ : c_type → Set
  ⟦ Void ⟧ = ⊤
  ⟦ Char ⟧ = Data.Char.Char
  ⟦ Int ⟧ = ℤ
  ⟦ Bool ⟧ = Data.Bool.Bool
  ⟦ Array α n ⟧ = Vec ⟦ α ⟧ n -- reversed order

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
    ∀ { α n } → { 0<n : 0 < n } → String → ⟦ Array α n { 0<n } ⟧ → (String → ℤ) → (String → ℤ)
  updateMapForArray {_} {ℕ.suc .0} {_} name (x ∷ᵥ []ᵥ) f var = 
    If var == name ++ "0" then encode x
    else f var
  updateMapForArray {_} {ℕ.suc (ℕ.suc n)} {_} name (x ∷ᵥ y ∷ᵥ arr) f =
    let f' = updateMapForArray {_} {ℕ.suc n} {Data.Nat.s≤s Data.Nat.z≤n} name (y ∷ᵥ arr) f in
      λ var →
        If var == name ++ (Data.Nat.Show.show n)
        then encode x else f' name

  safediv : ℤ → ℤ → ℤ
  safediv x (int 0) = int 0
  safediv x Data.Integer.+[1+ n ] = x /ᵢ (Data.Integer.+[1+ n ])
  safediv x (ℤ.negsuc n) = x /ᵢ (ℤ.negsuc n)

  impl : C
  C.Code impl α = State (String → ℤ) ⟦ α ⟧
  C.Ref impl α = String
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
  C._≔_ impl { Array α n { n>0 } } x y state =
    let y' , state' = y state in 
      y' , updateMapForArray {_} {_} { n>0 } x y' state'
  C._≔_ impl x y state =
    let y' , state' = y state in
      y' , (λ var → If var == x then (encode y') else state' var)
  (impl C.； x) y state = 
    let x' , state' = x state in
      y state'

eval : ∀ { α : c_type } → (∀ ⦃ impl : C ⦄ → Code ⦃ impl ⦄ α) → Eval.⟦ α ⟧
eval e = let v , _ = e ⦃ Eval.impl ⦄ (λ _ → int 0) in v

open import IO
main =
  let ex = eval (⟨ int 1 ⟩ + ⟨ int 1 ⟩) in
    run (IO.putStr (Data.Integer.show ex))
