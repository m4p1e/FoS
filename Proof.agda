module Proof where

open import Data.Nat using (ℕ; zero; suc; _+_ ; _∸_; _*_; _≤_; _≤ᵇ_; _⊔_; _⊓_) renaming (_≟_ to _≟ₙ_) 
open import Data.String using (String; _≟_)
open import Data.Bool using (Bool; true; false; not; _∧_ ; _∨_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong-app)
open import Relation.Nullary using (Dec; yes; no; _because_)

var : Set
var = String

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

-- states updating
_[_↦_] : state → var → value → state
(s [ x₁ ↦ v ]) x with x₁ ≟ x 
... | false because proof = s x
... | true because proof = v  

b→n : Bool → ℕ 
b→n false = 0
b→n true = 1

n→b : ℕ → Bool 
n→b zero = false
n→b (suc n) = true

vb→n : value → value
vb→n (valₒ x) = valₙ (b→n x)
vb→n v = v 
vn→b : value → value
vn→b (valₙ x) = valₒ (n→b x)
vn→b v = v

+' : ℕ → ℕ → ℕ
+' a b = a + b

∸' : ℕ → ℕ → ℕ
∸' a b = a ∸ b

*' : ℕ → ℕ → ℕ
*' a b = a * b

neval' : (ℕ → ℕ → ℕ) → value → value → value
neval' f (valₙ x₁) (valₙ x₂) = valₙ (f x₁ x₂)
neval' f (valₙ x₁) (valₒ x₂) = valₙ (f x₁ (b→n x₂))
neval' f (valₒ x₁) (valₙ x₂) = valₙ (f (b→n x₁) x₂)
neval' f (valₒ x₁) (valₒ x₂) = valₙ (f (b→n x₁) (b→n x₂))
neval' f v₁ undef = undef
neval' f undef v₂ = undef

∨' : Bool → Bool → Bool
∨' a b = a ∨ b

∧' : Bool → Bool → Bool
∧' a b = a ∧ b

≤ᵇ' : ℕ → ℕ → Bool
≤ᵇ' a b = a ≤ᵇ b

=' : ℕ → ℕ → Bool
=' a b with a | b
... | zero | zero = true
... | zero | suc y = false
... | suc x | zero = false
... | suc x | suc y = =' x y

nbeval' : (Bool → Bool) → value → value
nbeval' f (valₙ x) = valₒ (f (n→b x))
nbeval' f (valₒ x) = valₒ (f x)
nbeval' f undef = undef 

bbeval' : (Bool → Bool → Bool) → value → value → value
bbeval' f (valₙ x₁) (valₙ x₂) = valₒ (f (n→b x₁) (n→b x₂))
bbeval' f (valₙ x₁) (valₒ x₂) = valₒ (f (n→b x₁) x₂)
bbeval' f (valₒ x₁) (valₙ x₂) = valₒ (f x₁ (n→b x₂))
bbeval' f (valₒ x₁) (valₒ x₂) = valₒ (f x₁ x₂)
bbeval' f v₁ undef = undef
bbeval' f undef v₂ = undef

nnbeval' : (ℕ → ℕ → Bool) → value → value → value
nnbeval' f (valₙ x₁) (valₙ x₂) = valₒ (f x₁ x₂)
nnbeval' f (valₙ x₁) (valₒ x₂) = valₒ (f x₁ (b→n x₂))
nnbeval' f (valₒ x₁) (valₙ x₂) = valₒ (f (b→n x₁) x₂)
nnbeval' f (valₒ x₁) (valₒ x₂) = valₒ (f (b→n x₁) (b→n x₂))
nnbeval' f v₁ undef = undef
nnbeval' f undef v₂ = undef

-- evaluation
⟦_⟧ₙₑ : nexp → state → value
⟦ n-const x ⟧ₙₑ   s = valₙ x
⟦ n-var x ⟧ₙₑ     s = vb→n (s x)
⟦ n-add e₁ e₂ ⟧ₙₑ s = neval' +' (⟦ e₁ ⟧ₙₑ s)  (⟦ e₂ ⟧ₙₑ s)
⟦ n-sub e₁ e₂ ⟧ₙₑ s = neval' ∸' (⟦ e₁ ⟧ₙₑ s)  (⟦ e₂ ⟧ₙₑ s)
⟦ n-mul e₁ e₂ ⟧ₙₑ s = neval' *' (⟦ e₁ ⟧ₙₑ s)  (⟦ e₂ ⟧ₙₑ s)

⟦_⟧ₒₑ : bexp → state → value
⟦ b-const e ⟧ₒₑ     s = valₒ e
⟦ b-var e ⟧ₒₑ       s = vn→b (s e)
⟦ b-not e ⟧ₒₑ       s = nbeval' not (⟦ e ⟧ₒₑ s)
⟦ b-or e₁ e₂ ⟧ₒₑ    s = bbeval' ∨' (⟦ e₁ ⟧ₒₑ s)  (⟦ e₂ ⟧ₒₑ s)
⟦ b-and e₁ e₂ ⟧ₒₑ   s = bbeval' ∧' (⟦ e₁ ⟧ₒₑ s)  (⟦ e₂ ⟧ₒₑ s)
⟦ b-less e₁ e₂ ⟧ₒₑ  s = nnbeval' ≤ᵇ' (⟦ e₁ ⟧ₙₑ s)  (⟦ e₂ ⟧ₙₑ s)
⟦ b-eq e₁ e₂ ⟧ₒₑ    s = nnbeval'  =' (⟦ e₁ ⟧ₙₑ s)  (⟦ e₂ ⟧ₙₑ s)

⟦_⟧ᵣₑ : rexp → state → value
⟦ rbexp e ⟧ᵣₑ s = ⟦ e ⟧ₒₑ s
⟦ rnexp e ⟧ᵣₑ s = ⟦ e ⟧ₙₑ s

-- operational semantics
data ❴_❵_❴_❵ : state → stmt → state → Set where
  ❴_❵skip❴_❵ : 
          (s  : state) 
        → (s' : state) 
        → s ≡ s' 
        → ❴ s ❵ skip ❴ s ❵
  ❴_❵assign❴_❵ : {x : var} {e : rexp} 
        → (s  : state)
        → (s' : state)
        → (s' ≡ s [ x ↦ (⟦ e ⟧ᵣₑ s) ]) 
        → ❴ s ❵ lvar x := e ❴ s' ❵
  ❴_❵if-true❴_❵ : {e : bexp} {st₁ st₂ : stmt}
        → (s  : state)
        → (s' : state)
        → ⟦ e ⟧ₒₑ s ≡ valₒ true
        → ❴ s ❵ st₁ ❴ s' ❵
        → ❴ s ❵ if e then st₁ else st₂ ❴ s' ❵
  ❴_❵if-false❴_❵ : {e : bexp} {st₁ st₂ : stmt}       
        → (s  : state)
        → (s' : state)      
        → ⟦ e ⟧ₒₑ s ≡ valₒ false
        → ❴ s ❵ st₂ ❴ s' ❵
        → ❴ s ❵ if e then st₁ else st₂ ❴ s' ❵
  ❴_❵while-false❴_❵ : {e : bexp} {st : stmt}
        → (s  : state) 
        → (s' : state)
        → s ≡ s'
        → ⟦ e ⟧ₒₑ s ≡ valₒ false
        → ❴ s ❵ while e loop st ❴ s' ❵
  ❴_❵while-true❴_❵ : {e : bexp} {st : stmt} {s₁ : state}
        → (s  : state) 
        → (s' : state)
        → ⟦ e ⟧ₒₑ s ≡ valₒ true
        → ❴ s  ❵ st ❴ s₁ ❵
        → ❴ s₁ ❵ while e loop st ❴ s' ❵
        → ❴ s  ❵ while e loop st ❴ s' ❵
  ❴_❵seq❴_❵ : {e : bexp} {st₁ st₂ : stmt} {s₁ : state}
        → (s  : state)
        → (s' : state)
        → (❴ s  ❵ st₁ ❴ s₁ ❵)
        → (❴ s₁ ❵ st₂ ❴ s' ❵)
        → ❴ s ❵ st₁ ⍮ st₂ ❴ s' ❵       

postulate
  secᵥ' : ↦ℓₛ

-- State equivalence by visible distinguishability.
-- Notice that it is not defined in new datatype, 
-- since we do not really construct a such equivalence.
-- It is just a assumption
_[≡_]_ : state → ℓₛ → state → Set
s₁ [≡ l ] s₂ = ∀ {v : var} → secᵥ' v ≤ l → s₁ v ≡ s₂ v
  
-- The final theorem 
theorem : {l : ℕ}
          → (s₁ : state) → (s₁' : state)
          → (s₂ : state) → (s₂' : state)
          → s₁ [≡ l ] s₂ 
          → (st : stmt)
          → (secᵥ' : ↦ℓₛ) 
          → accept st secᵥ' ≡ true
          → ❴ s₁ ❵ st ❴ s₁' ❵
          → ❴ s₂ ❵ st ❴ s₂' ❵
          → s₁' [≡ l ] s₂'


theorem s₁ s₁ s₂ s₂ s₁=ₛs₂ skip m acc (❴ s₁ ❵skip❴ s₁' ❵ c₁) (❴ s₂ ❵skip❴ s₂' ❵ c₂) {v} vs≤l = s₁=ₛs₂ vs≤l
theorem s₁ s₁' s₂ s₂' s₁=ₛs₂ .(lvar _ := _) m acc (❴ .s₁ ❵assign❴ .s₁' ❵ x) y = {!   !}
theorem s₁ s₁' s₂ s₂' s₁=ₛs₂ .(if _ then _ else _) m acc (❴ .s₁ ❵if-true❴ .s₁' ❵ x x₁) y = {!   !}
theorem s₁ s₁' s₂ s₂' s₁=ₛs₂ .(if _ then _ else _) m acc (❴ .s₁ ❵if-false❴ .s₁' ❵ x x₁) y = {!   !}
theorem s₁ s₁' s₂ s₂' s₁=ₛs₂ .(while _ loop _) m acc (❴ .s₁ ❵while-false❴ .s₁' ❵ x x₁) y = {!   !}
theorem s₁ s₁' s₂ s₂' s₁=ₛs₂ .(while _ loop _) m acc (❴ .s₁ ❵while-true❴ .s₁' ❵ x x₁ x₂) y = {!   !}
theorem s₁ s₁' s₂ s₂' s₁=ₛs₂ .(_ ⍮ _) m acc (❴ .s₁ ❵seq❴ .s₁' ❵ x x₁) y = {!   !}