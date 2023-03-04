module InformationFlowSecurity where

open import Data.Nat using (ℕ; zero; suc; _+_ ; _≤_)
open import Data.String using (String)
open import Data.Bool using (Bool; true; false; not; _∧_ ; _∨_)
open import Data.Product using (_×_; _,_; proj₂)

-- <<user>> define var by different constructor
data var : Set where
  $a : var
  $b : var
  $c : var

-- <<module>> value constructors, language-specific
data value : Set where
  valₙ : ℕ → value
  valₒ : Bool → value
  undef : value

-- <<user>>
-- temporal code, it is ok for all possible variables.
-- since we can initialize the s₀ to s₀ (var n) = undef
-- then we can constantly update s
s₀ : var → value
s₀ $a = valₙ 1
s₀ $b = valₒ true
s₀ $c = undef

-- <<module>> language syntax
data lexp : Set where

data rexp : Set where

data bexp : Set where

data stmt : Set where
--  entry : stmt
  _⍮_ : stmt → stmt → stmt
  skip : stmt
  _:=_ : lexp → rexp → stmt
  if_then_else_ : bexp → stmt → stmt → stmt
  for_then : bexp → stmt → stmt

-- <<user>> define a program
program : stmt
program = skip

-- <<module>> sec-τ constructor 
data sec_ :  ℕ → Set where
  secₗ : ∀ (level : ℕ)  → sec level 

-- ex:
-- sec₀ : sec 0
-- sec₀ = secₗ 0 

-- <<user>>  
-- define security level for each var.   
sl : var → ℕ
sl $a = 1
sl $b = 2
sl $c = 3

-- <<module>> τ-var
τ-var : (v : var) → (sl : var → ℕ) → sec (sl v)
τ-var n sl = secₗ (sl n)

-- <<module>> τ-Base
data _<:τ_ : {l₁ l₂ : ℕ} → sec l₁ → sec l₂ → Set where
  l≤h : ∀ {l₁ l₂ : ℕ} {τ₁ : sec l₁} {τ₂ : sec l₂} → l₁ ≤ l₂ → τ₁ <:τ τ₂   

infix 4 _<:τ_

-- τ-base : (m n) → sec m → sec n → m n  











