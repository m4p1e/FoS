module Proof where

open import Data.Nat using (ℕ; zero; suc; _+_ ; _∸_; _*_; _≤_; _≤ᵇ_; _<_; _⊔_; _⊓_; z≤n; s≤s; _<ᵇ_) renaming (_≟_ to _≟ₙ_)
open import Data.Nat.Properties using (≤-trans)
open import Data.String using (String; _≟_; _==_)
open import Data.Bool using (Bool; true; false; not; _∧_ ; _∨_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; cong-app; trans)
open import Relation.Nullary using (¬_)

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

infix 5 _≤ᵍ_

n<1+n : {x : ℕ} → (x <ᵇ suc x) ≡ true
n<1+n {zero} = refl
n<1+n {suc x} = n<1+n {x}

x⊓y<x+1 : {x y : ℕ} → (x ⊓ y <ᵇ suc x) ≡ true
x⊓y<x+1 {zero} {y} = refl
x⊓y<x+1 {suc x} {zero} = refl
x⊓y<x+1 {suc x} {suc y} = x⊓y<x+1 {x}

x⊓y<y+1 : {x y : ℕ} → (x ⊓ y <ᵇ suc y) ≡ true
x⊓y<y+1 {zero} {zero} = refl
x⊓y<y+1 {suc x} {zero} = refl
x⊓y<y+1 {zero} {suc y} = refl
x⊓y<y+1 {suc x} {suc y} = x⊓y<y+1 {x} {y} 

x⊓y≤x : {x y : ℕ} → ((x ⊓ y) ≤ᵇ x) ≡ true
x⊓y≤x {zero} {y} = refl
x⊓y≤x {suc x} {zero} = refl
x⊓y≤x {suc x} {suc y} = x⊓y<x+1 {x} 

x⊓y≤y : {x y : ℕ} → ((x ⊓ y) ≤ᵇ y) ≡ true
x⊓y≤y {zero} {zero} = refl
x⊓y≤y {suc x} {zero} = refl
x⊓y≤y {zero} {suc y} = refl
x⊓y≤y {suc x} {suc y} = x⊓y<y+1 {x} {y}

≤ᵇ-reflexive : {x : ℕ} → x ≡ x → (x ≤ᵇ x) ≡ true   
≤ᵇ-reflexive {zero} refl = refl
≤ᵇ-reflexive {suc x} refl = n<1+n {x}

x⊓ᵍy≤x : {x y : ℕ̃} → (x ⊓ᵍ y) ≤ᵍ x ≡ true
x⊓ᵍy≤x {⊤} {y} with ⊤ ⊓ᵍ y
... | ⊤ = refl
... | n≤⊤ x = refl
x⊓ᵍy≤x {n≤⊤ x} {⊤} = ≤ᵇ-reflexive {x} refl
x⊓ᵍy≤x {n≤⊤ x} {n≤⊤ _} = x⊓y≤x {x} 

x⊓ᵍy≤y : {x y : ℕ̃} → (x ⊓ᵍ y) ≤ᵍ y ≡ true
x⊓ᵍy≤y {x} {⊤} with x ⊓ᵍ ⊤ 
... | ⊤ = refl
... | n≤⊤ x₁ = refl
x⊓ᵍy≤y {⊤} {n≤⊤ x} = ≤ᵇ-reflexive {x} refl
x⊓ᵍy≤y {n≤⊤ x} {n≤⊤ y} = x⊓y≤y {x} {y}

≤ᵍ-trans : {x y z : ℕ̃} → x ≤ᵍ y ≡ true → y ≤ᵍ z ≡ true → x ≤ᵍ z ≡ true   
≤ᵍ-trans {x} {y} {z} x≤ᵍy y≤ᵍz = {!   !}

x≤y⊓ᵍz₁ : {x y z : ℕ̃} → x ≤ᵍ (y ⊓ᵍ z) ≡ true → x ≤ᵍ y ≡ true      
x≤y⊓ᵍz₁ {x} {y} {z} x≤y⊓ᵍz = ≤ᵍ-trans {x} {y ⊓ᵍ z} {y} x≤y⊓ᵍz (x⊓ᵍy≤x {y} {z})

x≤y⊓ᵍz₂ : {x y z : ℕ̃} → x ≤ᵍ (y ⊓ᵍ z) ≡ true → x ≤ᵍ z ≡ true      
x≤y⊓ᵍz₂ {x} {y} {z} x≤y⊓ᵍz = ≤ᵍ-trans {x} {y ⊓ᵍ z} {z} x≤y⊓ᵍz (x⊓ᵍy≤y {y} {z})


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
(s [ x₁ ↦ v ]) x with x₁ == x
... | false = s x
... | true = v

s[x↦v]-elim₁ : {s s' : state} {x₁ x₂ : var} {v : value} → s' ≡ (s [ x₁ ↦ v ]) → (x₁ == x₂) ≡ true → s' x₂ ≡ v 
s[x↦v]-elim₁ {s} {s'} {x₁} {x₂} {v} c x₁=x₂ rewrite c | x₁=x₂ = refl

s[x↦v]-elim₂ : {s s' : state} {x₁ x₂ : var} {v : value} → s' ≡ (s [ x₁ ↦ v ]) → (x₁ == x₂) ≡ false → s' x₂ ≡ s x₂ 
s[x↦v]-elim₂ {s} {s'} {x₁} {x₂} {v} c x₁!=x₂ rewrite c | x₁!=x₂ = refl

-- casting
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

-- number evaluation
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

-- number evaluation
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
        → ⟦ e ⟧ₒₑ s ≡ valₒ false
        → s ≡ s'
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
-- since we do not really need to construct a such equivalence.
-- It is just a assumption
_[≡_]_ : state → ℓₛ → state → Set
s₁ [≡ l ] s₂ = ∀ {v : var} → secᵥ' v ≤ l → s₁ v ≡ s₂ v

infix 4 _[≡_]_

s[≡l]s'-trans : {l : ℕ} {s₁ s₂ s₃ : state} → s₁ [≡ l ] s₂ → s₂ [≡ l ] s₃ → s₁ [≡ l ] s₃  
s[≡l]s'-trans s₁[≡l]s₂ s₁[≡l]s₃ = {!   !}

s[≡l]s'-sym : {l : ℕ} {s₁ s₂ : state} → s₁ [≡ l ] s₂ → s₂ [≡ l ] s₁
s[≡l]s'-sym = {!   !}

-- anti monotonicity of level
anti-mono-veq : {l₁ l₂ : ℕ} {s₁ s₂ : state} → l₂ ≤ l₁ →  s₁ [≡ l₁ ] s₂ → s₁ [≡ l₂ ] s₂  
anti-mono-veq {l₁} {l₂} {s₁} {s₂} l₁≤l₂ s₁=ₗs₂ {v} vsl≤l = s₁=ₗs₂ (≤-trans vsl≤l l₁≤l₂)

--  evaluation of number-expression of visible area always produces same result
safe-evalₙₑ : {l : ℕ} {s₁ s₂ : state} {e : nexp} {v₁ v₂ : value}
            → s₁ [≡ l ] s₂
            → secₙₑ secᵥ' e ≤ l
            → v₁ ≡ ⟦ e ⟧ₙₑ s₁
            → v₂ ≡ ⟦ e ⟧ₙₑ s₂
            → v₁ ≡ v₂
safe-evalₙₑ {l} {s₁} {s₂} {e} {v₁} {v₂} s₁=ₗs₂ e≤l ve₁ ve₂ = {!   !}            

--  evaluation of boolean-expression of visible area always produces same result
safe-evalₒₑ : {l : ℕ} {s₁ s₂ : state} {e : bexp} {v₁ v₂ : value}
            → s₁ [≡ l ] s₂
            → secₒₑ secᵥ' e ≤ l
            → v₁ ≡ ⟦ e ⟧ₒₑ s₁
            → v₂ ≡ ⟦ e ⟧ₒₑ s₂
            → v₁ ≡ v₂
safe-evalₒₑ {l} {s₁} {s₂} {e} {v₁} {v₂} s₁=ₗs₂ e≤l ve₁ ve₂ = {!   !}

--  evaluation of right-expression of visible area always produces same result
safe-evalᵣₑ : {l : ℕ} {s₁ s₂ : state} {e : rexp} {v₁ v₂ : value}
            → s₁ [≡ l ] s₂
            → secᵣₑ secᵥ' e ≤ l
            → v₁ ≡ ⟦ e ⟧ᵣₑ s₁
            → v₂ ≡ ⟦ e ⟧ᵣₑ s₂
            → v₁ ≡ v₂

-- safe-eval {l} {s₁} {s₂} {x} {rbexp (b-const c)} {v₁} {v₂} s₁=ₗs₂ e≤l ve₁ ve₂ = trans ve₁ (sym ve₂)
-- it requires proofing s₁ bv ≡ s₂ bv, thus we have to construct bv ≤ l, but agda is powerful, it is e≤l.
-- safe-eval {l} {s₁} {s₂} {x} {rbexp (b-var bv)} {v₁} {v₂} s₁=ₗs₂ e≤l ve₁ ve₂ rewrite s₁=ₗs₂ e≤l = trans ve₁ (sym ve₂)
safe-evalᵣₑ {l} {s₁} {s₂} {rbexp be} {v₁} {v₂} s₁=ₗs₂ e≤l ve₁ ve₂ = safe-evalₒₑ {l} {s₁} {s₂} {be} {_} {_} s₁=ₗs₂ _ _ _
safe-evalᵣₑ {l} {s₁} {s₂} {rnexp ne} {v₁} {v₂} s₁=ₗs₂ e≤l ve₁ ve₂ = safe-evalₙₑ {l} {s₁} {s₂} {ne} {_} {_} s₁=ₗs₂ _ _ _

-- it is ok that a safe data write it to a visible area
safe-write1 : {l : ℕ} {s₁ s₂ : state} {s₁' s₂' : state} {x : var} {e : rexp} {v₁ v₂ : value}
            → s₁ [≡ l ] s₂ 
            → secᵥ' x ≤ l 
            → secᵣₑ secᵥ' e ≤ l
            → v₁ ≡ ⟦ e ⟧ᵣₑ s₁
            → v₂ ≡ ⟦ e ⟧ᵣₑ s₂
            → s₁' ≡ s₁ [ x ↦ v₁ ]
            → s₂' ≡ s₂ [ x ↦ v₂ ] 
            → s₁' [≡ l ] s₂'

safe-write1 {l} {s₁} {s₂} {s₁'} {s₂'} {x} {e} {v₁} {v₂} s₁=ₗs₂ x≤l e≤l ve₁ ve₂ c₁ c₂ {y} y≤l with x == y 
... | false rewrite s[x↦v]-elim₂ {s₁} {s₁'} {x} {y} {v₁} _ _ | s[x↦v]-elim₂ {s₂} {s₂'} {x} {y} {v₂} _ _ = s₁=ₗs₂ y≤l
... | true rewrite s[x↦v]-elim₂ {s₁} {s₁'} {x} {y} {v₁} _ _ | s[x↦v]-elim₂ {s₂} {s₂'} {x} {y} {v₂} _ _ = safe-evalᵣₑ {l} {s₁} {s₂} {e} {_} {_} s₁=ₗs₂ _ _ _  

postulate
  l-neq : {x : var} {y : var} → secᵥ' y < secᵥ' x → (x == y) ≡ false
  ≤-<-trans : {x y z : ℕ} → x ≤ y → y < z → x < z

-- it is non-interferential that a safe data write it to a visible area
safe-write2 : {l : ℕ} {s₁ s₂ : state} {s₁' s₂' : state} {x : var} {e : rexp} {v₁ v₂ : value}
            → s₁ [≡ l ] s₂ 
            → l < secᵥ' x
            → v₁ ≡ ⟦ e ⟧ᵣₑ s₁
            → v₂ ≡ ⟦ e ⟧ᵣₑ s₂
            → s₁' ≡ s₁ [ x ↦ v₁ ]
            → s₂' ≡ s₂ [ x ↦ v₂ ] 
            → s₁' [≡ l ] s₂'
            
safe-write2 {l} {s₁} {s₂} {s₁'} {s₂'} {x} {e} {v₁} {v₂} s₁=ₗs₂ l<x ve₁ ve₂ c₁ c₂ {y} y≤l 
  rewrite l-neq (≤-<-trans {secᵥ' y} {l} {secᵥ' x} y≤l l<x) | s[x↦v]-elim₂ {s₁} {s₁'} {x} {y} {v₁} _ _ | s[x↦v]-elim₂ {s₂} {s₂'} {x} {y} {v₂} _ _ = s₁=ₗs₂ y≤l  

postulate
  ¬≤ᵇ-elim : {a b : ℕ } → (a ≤ᵇ b) ≡ false → b < a

-- How is it terminal ?
<ᵇ-elim : {a b : ℕ } → (a <ᵇ b) ≡ true → suc a ≤ b
<ᵇ-elim {zero} {suc b} c = s≤s z≤n
<ᵇ-elim {suc a} {suc b} c = s≤s (<ᵇ-elim c) 

≤ᵇ-elim : {a b : ℕ } → (a ≤ᵇ b) ≡ true → a ≤ b
≤ᵇ-elim {zero} {b} c = z≤n
≤ᵇ-elim {suc a} {b} c = <ᵇ-elim c

∧-elim₁ : {a b : Bool} → a ∧ b ≡ true → a ≡ true
∧-elim₁ {true} {b} a∧b=true = refl

∧-elim₂ : {a b : Bool} → a ∧ b ≡ true → b ≡ true
∧-elim₂ {true} {true} a∧b=true = refl

-- a ≤ᵇ b ≡ true  →  a ≤ b 
acceptAssignThenNoInterfere : {x : var} {e : rexp} → accept (lvar x := e) secᵥ' ≡ true →  secᵣₑ secᵥ' e  ≤ secᵥ' x 
acceptAssignThenNoInterfere c = ≤ᵇ-elim c

-- accept (if e then st₁ else st₂) → accept st₁ × accept st₂
accepIfThenNoInterfere₁ : {e : bexp} { st₁ st₂ : stmt} → accept (if e then st₁ else st₂) secᵥ' ≡ true → (accept st₁ secᵥ' ≡ true) × (accept st₂ secᵥ' ≡ true)
accepIfThenNoInterfere₁ acc-if = {!   !}

accepIfThenNoInterfere₂ : {e : bexp} { st₁ st₂ : stmt} {s₁ s₂ : state} {l : ℕ} 
                        → accept (if e then st₁ else st₂) secᵥ' ≡ true 
                        → ⟦ e ⟧ₒₑ s₁ ≢ ⟦ e ⟧ₒₑ s₂ 
                        → s₁ [≡ l ] s₂ 
                        → l < secₒₑ secᵥ' e

accepIfThenNoInterfere₂ acc-if s₁e≢s₂e s₁=ₗs₂ = {!   !}

accpeWhileThenNoInterfere₁ : {e : bexp} {st : stmt} → accept (while e loop st) secᵥ' ≡ true → (accept st secᵥ' ≡ true)
accpeWhileThenNoInterfere₁ acc-while = {!   !}

accepSeqThenNoInterfere₁ : { st₁ st₂ : stmt} → accept (st₁ ⍮ st₂) secᵥ' ≡ true → accept st₁ secᵥ' ≡ true
accepSeqThenNoInterfere₁ acc-seq = ∧-elim₁ acc-seq

accepSeqThenNoInterfere₂ : { st₁ st₂ : stmt} → accept (st₁ ⍮ st₂) secᵥ' ≡ true → accept st₂ secᵥ' ≡ true
accepSeqThenNoInterfere₂ acc-seq = ∧-elim₂ acc-seq


-- Evaluation of high level stmt will not interfere visible area
lemma₁ : {l : ℕ}
          → (s s' : state)
          → (st : stmt)
          → (secₛₜ secᵥ' st ≤ᵍ n≤⊤ l) ≡ false
          → ❴ s ❵ st ❴ s' ❵
          → s [≡ l ] s'

lemma₁ = {!   !}

corollary₁ : {l : ℕ}
          → (s₁ : state) → (s₁' : state)
          → (s₂ : state) → (s₂' : state)
          → s₁ [≡ l ] s₂ 
          → (st₁ : stmt)
          → (st₂ : stmt)
          → (secₛₜ secᵥ' st₁ ≤ᵍ n≤⊤ l) ≡ false
          → (secₛₜ secᵥ' st₂ ≤ᵍ n≤⊤ l) ≡ false
          → ❴ s₁ ❵ st₁ ❴ s₁' ❵
          → ❴ s₂ ❵ st₂ ❴ s₂' ❵
          → s₁' [≡ l ] s₂'

corollary₁ {l} s₁ s₁' s₂ s₂' s₁=ₗs₂ st₁ st₂ l₁<l l₂<l c₁ c₂ 
  = s[≡l]s'-trans {l} {s₁'} {s₂} {s₂'}( 
      s[≡l]s'-trans {l} {s₁'} {s₁} {s₂} 
      (s[≡l]s'-sym {l} {s₁} {s₁'} (lemma₁ {l} s₁ s₁' st₁ l₁<l c₁))
      s₁=ₗs₂ 
    ) (lemma₁ {l} s₂ s₂' st₂ l₂<l c₂)

-- lemma₁ {l} s₁ s₁' st₁ l₁<l c₁ : s₁ [≡ l ] s₁'
-- lemma₁ {l} s₂ s₂' st₂ l₂<l c₂ : s₂ [≡ l ] s₂'

-- The final theorem 
theorem : {l : ℕ}
          → (s₁ : state) → (s₁' : state)
          → (s₂ : state) → (s₂' : state)
          → s₁ [≡ l ] s₂ 
          → (st : stmt)
          → accept st secᵥ' ≡ true
          → ❴ s₁ ❵ st ❴ s₁' ❵
          → ❴ s₂ ❵ st ❴ s₂' ❵
          → s₁' [≡ l ] s₂'


theorem s₁ s₁ s₂ s₂ s₁=ₗs₂ 
  skip acc 
  (❴ s₁ ❵skip❴ s₁' ❵ c₁) 
  (❴ s₂ ❵skip❴ s₂' ❵ c₂) 
  = s₁=ₗs₂
  
theorem {l} s₁ s₁' s₂ s₂' s₁=ₗs₂ 
  (lvar x := e) acc 
  (❴ s₁ ❵assign❴ s₁' ❵ c₁) 
  (❴ s₂ ❵assign❴ s₂' ❵ c₂) 
  with secᵥ' x ≤ᵇ l
... | false = (safe-write2 {l} {s₁} {s₂} {s₁'} {s₂'} {x} {e} {⟦ e ⟧ᵣₑ s₁} {⟦ e ⟧ᵣₑ s₂} s₁=ₗs₂ (¬≤ᵇ-elim {secᵥ' x} {l} _) refl refl c₁ c₂)
-- (≤ᵇ-elim {secᵥ' x} {l} _) : secᵥ' x < l 
-- (≤-trans (acceptAssignThenNoInterfere {x} {e} acc) (≤ᵇ-elim {secᵥ' x} {l} _)) : secᵣₑ secᵥ' e  ≤ l
... | true  = (safe-write1 {l} {s₁} {s₂} {s₁'} {s₂'} {x} {e} {⟦ e ⟧ᵣₑ s₁} {⟦ e ⟧ᵣₑ s₂} s₁=ₗs₂ 
              (≤ᵇ-elim {secᵥ' x} {l} _) 
              (≤-trans (acceptAssignThenNoInterfere {x} {e} acc) (≤ᵇ-elim {secᵥ' x} {l} _))  
              refl refl c₁ c₂)

-- if-true and if-true or if-false and if-false, we have to induce the proof of (accept st₁) and (accept st₂) from (accept if).
theorem s₁ s₁' s₂ s₂' s₁=ₗs₂ 
  (if e then st₁ else st₂) acc 
  (❴ s₁ ❵if-true❴ s₁' ❵ e=true₁ c₁) 
  (❴ s₂ ❵if-true❴ s₂' ❵ e=true₂ c₂) 
  = theorem s₁ s₁' s₂ s₂' s₁=ₗs₂ st₁ (proj₁ (accepIfThenNoInterfere₁ {e} {st₁} {st₂} acc)) c₁ c₂

theorem s₁ s₁' s₂ s₂' s₁=ₗs₂
  (if e then st₁ else st₂) acc 
  (❴ s₁ ❵if-false❴ s₁' ❵ e=false c₁) 
  (❴ s₂ ❵if-false❴ s₂' ❵ e=false₂ c₂) 
  = theorem s₁ s₁' s₂ s₂' s₁=ₗs₂ st₂ (proj₂ (accepIfThenNoInterfere₁ {e} {st₁} {st₂} acc)) c₁ c₂


-- if-true and if-false or if-false and if-true, we have to prove l < secᵥ' e   
theorem s₁ s₁' s₂ s₂' s₁=ₗs₂ 
  (if e then st₁ else st₂) acc 
  (❴ s₁ ❵if-true❴ s₁' ❵ e=true₁ c₁) 
  (❴ s₂ ❵if-false❴ s₂' ❵ e=false₂ c₂) 
  = corollary₁ s₁ s₁' s₂ s₂' s₁=ₗs₂ st₁ st₂ _ _ c₁ c₂

theorem s₁ s₁' s₂ s₂' s₁=ₗs₂ 
  (if e then st₁ else st₂) acc 
  (❴ s₁ ❵if-false❴ s₁' ❵ e=false₁ c₁) 
  (❴ s₂ ❵if-true❴ s₂' ❵ e=true₂ c₂) 
  = corollary₁ s₁ s₁' s₂ s₂' s₁=ₗs₂ st₂ st₁ _ _ c₁ c₂


theorem s₁ s₁' s₂ s₂' s₁=ₗs₂ 
  (while e loop st) acc 
  (❴ s₁ ❵while-true❴ s₁' ❵ e=true₁ s₁⇒sₜ sₜ⇒s₁') 
  (❴ s₂ ❵while-true❴ s₂' ❵ e=true₂ s₂⇒sₜ sₜ⇒s₂') 
  = theorem _ s₁' _ s₂' (
      theorem s₁ _ s₂ _ s₁=ₗs₂ st (accpeWhileThenNoInterfere₁ {e} {st} acc) s₁⇒sₜ s₂⇒sₜ
    ) (while e loop st) acc sₜ⇒s₁' sₜ⇒s₂'

theorem s₁ s₁' s₂ s₂' s₁=ₗs₂ 
  (while e loop st) acc 
  (❴ s₁ ❵while-false❴ s₁' ❵ e=false₁ s₁⇒s₁') 
  (❴ s₂ ❵while-false❴ s₂' ❵ e=false₂ s₂⇒s₂') rewrite s₁⇒s₁' | s₂⇒s₂'
  = s₁=ₗs₂

theorem {l} s₁ s₁' s₂ s₂' s₁=ₗs₂ 
  (while e loop st) acc 
  (❴ s₁ ❵while-true❴ s₁' ❵ e=true₁ s₁⇒sₜ sₜ⇒s₁')
  (❴ s₂ ❵while-false❴ s₂' ❵ e=false₂ s₂⇒s₂') {v} v≤l rewrite s₂⇒s₂'
  = trans 
    (sym ((s[≡l]s'-trans {l} {s₁} {_} {s₁'} (lemma₁ {l} s₁ _ st _  s₁⇒sₜ) (lemma₁ {l} _ s₁' (while e loop st) _ sₜ⇒s₁')) {v} v≤l)) 
    (s₁=ₗs₂ {v} v≤l)

-- s₁=ₗs₂ {v} v≤l : s₁ v = s₂' v
-- (s[≡l]s'-trans {l} {s₁} {_} {s₁'} (lemma₂ {l} s₁ _ st _  s₁⇒sₜ) (lemma₂ {l} _ s₁' (while e loop st) _ sₜ⇒s₁')) {v}  v≤l : s₁ v ≡ s₁' v

theorem {l} s₁ s₁' s₂ s₂' s₁=ₗs₂ 
  (while e loop st) acc 
  (❴ s₁ ❵while-false❴ s₁' ❵ e=false₁ s₁⇒s₁') 
  (❴ s₂ ❵while-true❴ s₂' ❵ e=true₂ s₂⇒sₜ sₜ⇒s₂') {v} v≤l rewrite s₁⇒s₁'
  = trans 
    (s₁=ₗs₂ {v} v≤l) 
    ((s[≡l]s'-trans {l} {s₂} {_} {s₂'} (lemma₁ {l} s₂ _ st _  s₂⇒sₜ) (lemma₁ {l} _ s₂' (while e loop st) _ sₜ⇒s₂')) {v} v≤l)

-- s₁=ₗs₂ {v} v≤l : s₁' v ≡ s₂ v
-- sym ((s[≡l]s'-trans {l} {s₂} {_} {s₂'} (lemma₂ {l} s₂ _ st _  s₂⇒sₜ) (lemma₂ {l} _ s₂' (while e loop st) _ sₜ⇒s₂')) {v}  v≤l) : s₂' v ≡ s₂ v

theorem s₁ s₁' s₂ s₂' s₁=ₗs₂ 
  (st₁ ⍮ st₂) acc 
  (❴ s₁ ❵seq❴ s₁' ❵ s₁⇒sₜ sₜ⇒s₁') 
  (❴ s₂ ❵seq❴ s₂' ❵ s₂⇒sₜ sₜ⇒s₂') 
  = theorem _ s₁' _ s₂' (
      theorem s₁ _ s₂ _ s₁=ₗs₂ st₁ (accepSeqThenNoInterfere₁ {st₁} {st₂} acc) s₁⇒sₜ s₂⇒sₜ
  ) st₂ ((accepSeqThenNoInterfere₂ {st₁} {st₂} acc)) sₜ⇒s₁' sₜ⇒s₂' 