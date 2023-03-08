module InformationFlowSecurity where

open import Data.Nat using (ℕ; zero; suc; _+_ ; _∸_; _*_; _≤_; _≤ᵇ_; _⊔_; _⊓_)
open import Data.String using (String)
open import Data.Bool using (Bool; true; false; not; _∧_ ; _∨_)
open import Data.Product using (_×_; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Relation.Nullary using (Dec; yes; no)

-- <<user>> define var by different constructor
data var : Set where
  $a : var
  $b : var
  $c : var

-- <<module>> value constructors, language-specific
data value : Set where
  valₙ  : ℕ → value
  valₒ  : Bool → value
  undef : value

-- <<user>>
-- temporal code, it is ok for all possible variables.
-- since we can initialize the s₀ to s₀ (var n) = undef
-- then we can constantly update s
state = var → value
s₀ : state
s₀ $a = valₙ 1
s₀ $b = valₒ true
s₀ $c = undef

-- <<module>> language syntax
data lexp : Set where
  lvar    : var → lexp

data nexp : Set where
  n-const : ℕ → nexp
  n-var   : var → nexp
  n-add   : nexp → nexp → nexp
  n-sub   : nexp → nexp → nexp
  n-mul   : nexp → nexp → nexp

data bexp : Set where
  b-const : Bool → bexp
  b-var    : var → bexp
  b-not   : bexp → bexp
  b-or    : bexp → bexp → bexp
  b-and   : bexp → bexp → bexp
  b-less  : nexp → nexp → bexp
  b-eq    : nexp → nexp → bexp


data rexp : Set where
  rbexp   : bexp → rexp
  rnexp   : nexp → rexp

data stmt : Set where
  skip          : stmt
  _:=_          : lexp → rexp → stmt
  if_then_else_ : bexp → stmt → stmt → stmt
  while_loop_   : bexp → stmt → stmt
  _⍮_           : stmt → stmt → stmt

-- <<user>> define a program
-- program : stmt
-- program = ( lvar $a := rnexp (n-const 2) ) ⍮ (lvar $b := rbexp (b-const false) )

-- abstract level is actually ℕ, but concrete values require to be defined by user
ℓₛ = ℕ
↦ℓₛ = var → ℓₛ

-- postulate
--  secᵥ : var → ℓₛ

-- expression security level : sec e = ⋁ sec eᵢ
secₙₑ : ↦ℓₛ → nexp → ℓₛ
secₙₑ secᵥ (n-const x) = 0 -- ⊥ ?
secₙₑ secᵥ (n-var x) = secᵥ x
secₙₑ secᵥ (n-add e₁ e₂) = secₙₑ secᵥ e₁ ⊔ secₙₑ secᵥ e₂
secₙₑ secᵥ (n-sub e₁ e₂) = secₙₑ secᵥ e₁ ⊔ secₙₑ secᵥ e₂
secₙₑ secᵥ (n-mul e₁ e₂) = secₙₑ secᵥ e₁ ⊔ secₙₑ secᵥ e₂

secₒₑ : ↦ℓₛ → bexp → ℓₛ
secₒₑ secᵥ (b-const x) = 0
secₒₑ secᵥ (b-var x) = secᵥ x
secₒₑ secᵥ (b-not e) = secₒₑ secᵥ e
secₒₑ secᵥ (b-or e₁ e₂) = secₒₑ secᵥ e₁ ⊔ secₒₑ secᵥ e₂
secₒₑ secᵥ (b-and e₁ e₂) = secₒₑ secᵥ e₁ ⊔ secₒₑ secᵥ e₂
secₒₑ secᵥ (b-less e₁ e₂) = secₙₑ secᵥ e₁ ⊔ secₙₑ secᵥ e₂
secₒₑ secᵥ (b-eq e₁ e₂) = secₙₑ secᵥ e₁ ⊔ secₙₑ secᵥ e₂

secₗₑ : ↦ℓₛ → lexp → ℓₛ
secₗₑ secᵥ (lvar x) = secᵥ x

secᵣₑ : ↦ℓₛ → rexp → ℓₛ
secᵣₑ secᵥ (rbexp x) = secₒₑ secᵥ x
secᵣₑ secᵥ (rnexp x) = secₙₑ secᵥ x 

-- ℕ with a greatest element ⊤
data ℕ̃ : Set where
  ⊤ : ℕ̃
  n≤⊤ : ℕ → ℕ̃

_⊓ᵍ_ : ℕ̃ → ℕ̃ → ℕ̃ 
⊤ ⊓ᵍ ⊤ = ⊤
⊤ ⊓ᵍ n≤⊤ x = n≤⊤ x
n≤⊤ x ⊓ᵍ ⊤ = n≤⊤ x
n≤⊤ x ⊓ᵍ n≤⊤ y = n≤⊤ (x ⊓ y)

infixl 7 _⊓ᵍ_

_≤ᵍ_ : ℕ̃ → ℕ̃ → Bool
⊤ ≤ᵍ ⊤ = true
⊤ ≤ᵍ n≤⊤ x = false
n≤⊤ x ≤ᵍ ⊤ = true
n≤⊤ x₁ ≤ᵍ n≤⊤ x₂ = x₁ ≤ᵇ x₂

infix 4 _≤ᵍ_

-- ℕ̃ℕ : ℕ̃  → ℕ 

-- CMD security level : st = ⋀ stᵢ
-- we should only keep the valid level, the valid level must be the greatest one.
-- do not worry about the invalid one, since it will be rejected early.
-- a valid 'if' or 'while', its valid level must be the lowest one
secₛₜ : ↦ℓₛ → stmt → ℕ̃
secₛₜ secᵥ skip = ⊤
secₛₜ secᵥ (x := e) = n≤⊤ (secₗₑ secᵥ x ⊔ secᵣₑ secᵥ e)
secₛₜ secᵥ (if e then st₁ else st₂) = n≤⊤ (secₒₑ secᵥ e) ⊓ᵍ secₛₜ secᵥ st₁ ⊓ᵍ secₛₜ secᵥ st₂
secₛₜ secᵥ (while e loop st) = n≤⊤ (secₒₑ secᵥ e) ⊓ᵍ secₛₜ secᵥ st
secₛₜ secᵥ (st₁ ⍮ st₂) = secₛₜ secᵥ st₁ ⊓ᵍ secₛₜ secᵥ st₂

-- rules: 
-- 1. assign : high ← low 
-- 2. conditional branch : if(c ← low){ st ← high} and (accept st secᵥ ≡ true) 
-- 3. otherwise rejects.
accept : stmt → ↦ℓₛ → Bool
accept skip secᵥ = true
accept (x := e) secᵥ = secᵣₑ secᵥ e ≤ᵇ secₗₑ secᵥ x
accept (if e then st₁ else st₂) secᵥ with accept st₁ secᵥ | accept st₂ secᵥ
... | true | true = n≤⊤ (secₒₑ secᵥ e) ≤ᵍ secₛₜ secᵥ st₁ ⊓ᵍ secₛₜ secᵥ st₂
... | _  | _  = false
accept (while e loop st) secᵥ with accept st secᵥ
... | true = n≤⊤ (secₒₑ secᵥ e) ≤ᵍ secₛₜ secᵥ st
... | _ = false
accept (st₁ ⍮ st₂) secᵥ = accept st₁ secᵥ ∧ accept st₂ secᵥ

secᵥ⁰ : ↦ℓₛ
secᵥ⁰ $a = 1
secᵥ⁰ $b = 2
secᵥ⁰ $c = 3

-- ex1 a = 2; b = false
p₁ : stmt
p₁ = ( lvar $a := rnexp (n-const 2) ) ⍮ (lvar $b := rbexp (b-const false) )
p₁r = accept p₁ secᵥ⁰ 
?p₁r : p₁r ≡ true 
?p₁r = refl

-- ex2 a = 1; a = b
p₂ : stmt
p₂ = ( lvar $a := rnexp (n-const 2) ) ⍮ (lvar $a := rnexp (n-var $b) )
p₂r = accept p₂ secᵥ⁰ 
?p₂r : not p₂r ≡ true 
?p₂r = refl

-- ex3 if(b) {$a = $b}
p₃ : stmt
p₃ = if (b-var $b) then (lvar $a := rnexp (n-var $b)) else (skip)
p₃r = accept p₃ secᵥ⁰ 
?p₃r : not p₃r ≡ true 
?p₃r = refl


-- TODO: infinite variables.
_[_↦_] : state → var → value → state
(s [ x₁ ↦ v ]) x with x₁ | x
... | $a | $a = v
... | $b | $b = v
... | $c | $c = v
... | _  | _  = s x

⟦_⟧ₙₑ : bexp → state → value
⟦ b-const e ⟧ₙₑ s = {!   !}
⟦ b-var e ⟧ₙₑ s = {!   !}
⟦ b-not e ⟧ₙₑ s = {!   !}
⟦ b-or e₁ e₂ ⟧ₙₑ s = {!   !}
⟦ b-and e₁ e₂ ⟧ₙₑ s = {!   !}
⟦ b-less e₁ e₂ ⟧ₙₑ s = {!   !}
⟦ b-eq e₁ e₂ ⟧ₙₑ s = {!   !}

⟦_⟧ₒₑ : bexp → state → value
⟦ b-const e ⟧ₒₑ s = {!   !}
⟦ b-var e ⟧ₒₑ s = {!   !}
⟦ b-not e ⟧ₒₑ s = {!   !}
⟦ b-or e₁ e₂ ⟧ₒₑ s = {!   !}
⟦ b-and e₁ e₂ ⟧ₒₑ s = {!   !}
⟦ b-less e₁ e₂ ⟧ₒₑ s = {!   !}
⟦ b-eq e₁ e₂ ⟧ₒₑ s = {!   !}

⟦_⟧ᵣₑ : rexp → state → value
⟦ rbexp (b-const e) ⟧ᵣₑ s = {!   !}
⟦ rbexp (b-var e) ⟧ᵣₑ s = {!   !}
⟦ rbexp (b-not e) ⟧ᵣₑ s = {!   !}
⟦ rbexp (b-or e₁ e₂) ⟧ᵣₑ s = {!   !}
⟦ rbexp (b-and e₁ e₂) ⟧ᵣₑ s = {!   !}
⟦ rbexp (b-less e₁ e₂) ⟧ᵣₑ s = {!   !}
⟦ rbexp (b-eq e₁ e₂) ⟧ᵣₑ s = {!   !}
⟦ rnexp (n-const e) ⟧ᵣₑ s = {!   !}
⟦ rnexp (n-var e) ⟧ᵣₑ s = {!   !}
⟦ rnexp (n-add e₁ e₂) ⟧ᵣₑ s = {!   !}
⟦ rnexp (n-sub e₁ e₂) ⟧ᵣₑ s = {!   !}
⟦ rnexp (n-mul e₁ e₂) ⟧ᵣₑ s = {!   !}

-- [_]⇒ₛₜ_ : state → stmt → state
-- [ s ]⇒ₛₜ (st₁ ⍮ st₂) = [ [ s ]⇒ₛₜ st₁ ]⇒ₛₜ st₂
-- [ s ]⇒ₛₜ skip = s
-- [ s ]⇒ₛₜ (lvar x := e) = s [ x ↦ {!   !} ]
-- [ s ]⇒ₛₜ (if e then st₁ else st₂) = {!   !}
-- [ s ]⇒ₛₜ (while e loop st) = {!   !}


-- operational semantics
data ❴_❵_❴_❵ : state → stmt → state → Set where
  ❴p❵skip❴q❵ : 
        (s : state) → (st : stmt) 
        → st ≡ skip 
        → ❴ s ❵ st ❴ s ❵
  ❴p❵assign❴q❵ : {x : var} {e : rexp} 
        → (s : state) → (st : stmt) 
        → st ≡ lvar x := e 
        → ❴ s ❵ st ❴ s [ x ↦ (⟦ e ⟧ᵣₑ s) ] ❵
  ❴p❵if-true❴q❵ : {e : bexp} {st₁ st₂ : stmt} {s' : state}        
        → (s : state) → (st : stmt)
        → st ≡ if e then st₁ else st₂
        → ⟦ e ⟧ₒₑ s ≡ valₒ true
        → (❴p❵st₁❴q❵ : ❴ s ❵ st₁ ❴ s' ❵)
        → ❴ s ❵ st ❴ s' ❵
  ❴p❵if-false❴q❵ : {e : bexp} {st₁ st₂ : stmt} {s' : state}        
        → (s : state) → (st : stmt)
        → st ≡ if e then st₁ else st₂
        → ⟦ e ⟧ₒₑ s ≡ valₒ false
        → (❴p❵st₂❴q❵ : ❴ s ❵ st₂ ❴ s' ❵)
        → ❴ s ❵ st ❴ s' ❵
  ❴p❵while-false❴q❵ : {e : bexp} {st₁ : stmt}
        → (s : state) → (st : stmt)
        → st ≡ while e loop st₁
        → ⟦ e ⟧ₒₑ s ≡ valₒ false
        → ❴ s ❵ st ❴ s ❵
  ❴p❵while-true❴q❵ : {e : bexp} {st₁ : stmt} {s₁ s₂ : state}
        → (s : state) → (st : stmt)
        → st ≡ while e loop st₁
        → ⟦ e ⟧ₒₑ s ≡ valₒ true
        → (❴p❵st₁❴q❵ : ❴ s ❵ st₁ ❴ s₁ ❵)
        → (❴p❵st₁❴q❵ : ❴ s₁ ❵ st ❴ s₂ ❵)
        → ❴ s ❵ st ❴ s₂ ❵
  ❴p❵seq❴q❵ : {e : bexp} {st₁ st₂ : stmt} {s₁ s₂ : state}
        → (s : state) → (st : stmt)
        → st ≡ st₁ ⍮ st₂
        → (❴p❵st₁❴q❵ : ❴ s ❵ st₁ ❴ s₁ ❵)
        → (❴p❵st₂❴q❵ : ❴ s ❵ st₂ ❴ s₂ ❵)
        → ❴ s ❵ st ❴ s₂ ❵    

postulate
  secᵥ' : ↦ℓₛ

-- State equivalence by visible distinguishability.
-- Notice that it is not defined in new datatype, 
-- since we do not really construct a such equivalence.
-- It is just a assumption
_[≡_]_ : state → ℓₛ → state → Set
s₁ [≡ l ] s₂ = ∀ {v : var} → secᵥ' v ≤ l → s₁ v ≡ s₂ v


-- The final theorem is  
-- s₁ [≡ l ] s₂ → (st : stmt) → (secᵥ' : ↦ℓₛ) → accept st secᵥ' ≡ true → s₁⟦st⟧ [≡ l ] s₂⟦st⟧      