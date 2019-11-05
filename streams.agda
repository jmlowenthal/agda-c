module streams where

open import Data.Unit
open import Data.Integer using (ℤ)
  renaming (_+_ to _+ᵢ_; _*_ to _*ᵢ_; _-_ to _-ᵢ_; +_ to int; _<_ to _<ᵢ_; _≤_ to _≤ᵢ_)
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
open import Data.Product hiding (map)
open import Function
open import Relation.Nullary.Decidable using (⌊_⌋)
import Data.Fin

data c_type : Set where
  Void Char Int Bool : c_type
  Array : c_type → (n : ℕ) → c_type

record C : Set₁ where
  field
    Code : c_type → Set
    Ref : c_type → Set
    --_≃_ : ∀ { α β } → Code α → Code β → Set
    _∈_ : Code Int → ℕ → Set
    ⟨_⟩ : ℤ → Code Int
    _+_ _*_ _-_ _/_ : Code Int → Code Int → Code Int
    true false : Code Bool
    _||_ _&&_ : Code Bool → Code Bool → Code Bool
    if_then_else_ : ∀ { α } → Code Bool → Code α → Code α → Code α
    [] : ∀ { α } → Code (Array α 0)
    _∷_ : ∀ { α n } → Code α → Code (Array α n) → Code (Array α (ℕ.suc n))
    _[_] : ∀ { α n } → { 0<n : 0 < n } → Ref (Array α n) → (i : Code Int)
      → { i∈n : i ∈ n } → Ref α
    ★_ : ∀ { α } → Ref α → Code α
    _≔_ : ∀ { α } → Ref α → Code α → Code α
    _；_ : ∀ { α β } → Code α → Code β → Code β
    decl : (α : c_type) → ∀ { β } → (Ref α → Code β) → Code β

  infix 0 _；_
  infix 1 if_then_else_
  infix 2 _≔_
  infix 3 _∷_
  infix 4 _/_
  infix 5 _*_
  infix 6 _+_
  infix 7 _-_
  infix 8 ★_ _||_ _&&_
  infix 9 _[_]

open C ⦃ ... ⦄

⟦_⟧ : c_type → Set
⟦ Void ⟧ = ⊤
⟦ Char ⟧ = Data.Char.Char
⟦ Int ⟧ = ℤ
⟦ Bool ⟧ = Data.Bool.Bool
⟦ Array α n ⟧ = Vec ⟦ α ⟧ n -- reversed order

-- Stream Fusion, to Completeness ----------------------------------------

data CardT : Set where
  atMost1 : CardT
  many : CardT

data ProducerT (α σ : Set) ⦃ _ : C ⦄ : Set where
  for : (σ → Code Int) × (σ → Code Int → (α → Code Void) → Code Void) → ProducerT α σ
  unfolder : (σ → Code Bool) × CardT × (σ → (α → Code Void) → Code Void) → ProducerT α σ

data Producer (α : Set) ⦃ _ : C ⦄ : Set₁ where
  producer : ∀ ⦃ σ ⦄ → (∀ { ω } → (σ → Code ω) → Code ω) × (ProducerT α σ) → Producer α

data Stream (α : c_type) ⦃ _ : C ⦄ : Set₁ where
  linear : Producer (Code α) → Stream α
  nested : ∀ ⦃ β ⦄ → Producer (Code β) × (Code β → Stream α) → Stream α

ofArr : ∀ ⦃ _ : C ⦄ → ∀ { α n } → Code (Array α n) → Stream α
ofArr { α } { n } arr =
  let init : ∀ { ω } → (Ref (Array α n) → Code ω) → Code ω
      init k = decl (Array α n) λ x → x ≔ arr ； k x
      upb : ∀ { m } → Ref (Array α m) → Code Int
      upb { m } _ = ⟨ int m ⟩
      index : ∀ { m } → Ref (Array α m) → Code Int → (Code α → Code Void) → Code Void
      index arr i k = decl α λ el → el ≔ ★ (arr [ i ]) ； k (★ el) -- TODO: requires i ∈ n
  in
    linear (producer ⦃ σ = Ref (Array α n) ⦄ (init , for (upb , index)))

-- TODO: C optionals / limited C structs
unfold : ∀ ⦃ _ : C ⦄ → ∀ { α ζ } → (Code ζ → Code Bool × Code α × Code ζ) → Code ζ → Stream α
unfold f x = linear (producer ⦃ σ = {!!} ⦄ ({!!} , unfolder ({!!} , {!!})))

forUnfold : ∀ ⦃ _ : C ⦄ → ∀ { α } → Stream α → Stream α
forUnfold (linear (producer ⦃ σ = σ ⦄ (init , for (bound , index)))) =
  let init' k = init (λ s0 → decl Int λ i → i ≔ ⟨ int 0 ⟩ ； k (i , s0)) in
  linear (producer ⦃ σ = Ref Int × σ ⦄ ({!!} , unfolder ({!!} , {!!})))
forUnfold (linear (producer ⦃ σ = σ ⦄ (init , unfolder x))) =
  linear (producer ⦃ σ = σ ⦄ (init , unfolder x))
forUnfold (nested (producer (init , for x) , snd)) = {!!}
forUnfold (nested (producer ⦃ σ = σ ⦄ (init , unfolder x) , f)) =
  nested (producer ⦃ σ = σ ⦄ (init , (unfolder x)) , f)

flatMap : ∀ ⦃ _ : C ⦄ → ∀ { α β } → (Code α → Stream β) → Stream α → Stream β
flatMap {α = α} f (linear x) = nested ⦃ β = α ⦄ (x , f)
flatMap f (nested ⦃ β = β ⦄ (x , g)) = nested ⦃ β = β ⦄ (x , λ a → flatMap f (g a))

filter : ∀ ⦃ _ : C ⦄ → ∀ { α : c_type } → (Code α → Code Bool) → Stream α → Stream α
filter { α = α } f = flatMap (
  λ x → linear (
    producer ⦃ σ = Code α ⦄ (
      (λ k → k x)
      , unfolder (f , atMost1 , λ a k → k a)
    )
  ))

take : ∀ ⦃ _ : C ⦄ → Code Int → ∀ { α } → Stream α → Stream α

iota : ∀ ⦃ _ : C ⦄ → ℕ → Stream Int
iota n = {!!}

--------------------------------------------------------------------------

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
  C.[] impl state = []ᵥ , state
  (impl C.∷ x) y = applyOperator (_∷ᵥ_) x y
  C._≔_ impl { Array α n } x y state =
    let y' , state' = y state in 
      y' , updateMapForArray x y' state'
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
  let ex = eval (⟨ int 1 ⟩ + ⟨ int 10 ⟩) in
    run (IO.putStr (Data.Integer.show ex))
