module Proof where

open import Data.Nat using (ℕ; zero; suc; _+_ ; _∸_; _*_; _≤_; _≤ᵇ_; _<_; _⊔_; _⊓_; z≤n; s≤s; _<ᵇ_) renaming (_≟_ to _≟ₙ_)
open import Data.Nat.Properties using (≤-trans; m≤m⊔n; m≤n⊔m; m⊔n≤o⇒m≤o; m⊔n≤o⇒n≤o)
open import Data.String using (String; _≟_; _==_)
open import Data.Bool using (Bool; true; false; not; _∧_ ; _∨_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; cong₂; cong-app; trans; inspect; [_])
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
  b-var   : var → bexp
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

<-trans' : {x y z : ℕ} →  (x <ᵇ suc y) ≡ true → (y <ᵇ suc z) ≡ true → (x <ᵇ suc z) ≡ true
<-trans' {zero} {zero} {z} x<ᵇsucy y<ᵇsucz = refl
<-trans' {zero} {suc y} {z} x<ᵇsucy y<ᵇsucz = refl
<-trans' {suc x} {suc y} {suc z} x<ᵇsucy y<ᵇsucz = <-trans' {x} {y} {z} x<ᵇsucy y<ᵇsucz 

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

≤ᵇ-trans : {x y z : ℕ} → (x ≤ᵇ y) ≡ true → (y ≤ᵇ z) ≡ true → (x ≤ᵇ z) ≡ true
≤ᵇ-trans {x} {zero} {zero} x≤ᵇy y≤ᵇz = x≤ᵇy
≤ᵇ-trans {zero} {zero} {suc z} x≤ᵇy y≤ᵇz = refl
≤ᵇ-trans {zero} {suc y} {suc z} x≤ᵇy y≤ᵇz = refl
≤ᵇ-trans {suc x} {suc y} {suc z} x≤ᵇy y≤ᵇz = <-trans' {x} {y} {z} x≤ᵇy y≤ᵇz


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
≤ᵍ-trans {⊤} {y} {⊤} x≤ᵍy y≤ᵍz = refl
≤ᵍ-trans {n≤⊤ x₁} {y} {⊤} x≤ᵍy y≤ᵍz = refl 
≤ᵍ-trans {n≤⊤ x₁} {n≤⊤ y₁} {n≤⊤ z₁} x≤ᵍy y≤ᵍz = ≤ᵇ-trans {x₁} {y₁} {z₁} x≤ᵍy y≤ᵍz
≤ᵍ-trans {⊤} {n≤⊤ y₂} {n≤⊤ z₁} x≤ᵍy y≤ᵍz = x≤ᵍy 

x≤y⊓ᵍz₁ : {x y z : ℕ̃} → x ≤ᵍ (y ⊓ᵍ z) ≡ true → x ≤ᵍ y ≡ true      
x≤y⊓ᵍz₁ {x} {y} {z} x≤y⊓ᵍz = ≤ᵍ-trans {x} {y ⊓ᵍ z} {y} x≤y⊓ᵍz (x⊓ᵍy≤x {y} {z})

x≤y⊓ᵍz₂ : {x y z : ℕ̃} → x ≤ᵍ (y ⊓ᵍ z) ≡ true → x ≤ᵍ z ≡ true      
x≤y⊓ᵍz₂ {x} {y} {z} x≤y⊓ᵍz = ≤ᵍ-trans {x} {y ⊓ᵍ z} {z} x≤y⊓ᵍz (x⊓ᵍy≤y {y} {z})

≤ᵇ⇒≤ᵍ : {a b : ℕ} → (a ≤ᵇ b) ≡ false → ((n≤⊤ a) ≤ᵍ (n≤⊤ b) ≡ false)
≤ᵇ⇒≤ᵍ {a} {b} a≤ᵇb = a≤ᵇb

contradiction₂ : (true ≡ false) → ⊥
contradiction₂ = λ ()

x<ᵇsucz=false∧y<ᵇsucz=false⇒x⊓y<ᵇsucz=false : {x y z : ℕ} → (x <ᵇ suc z) ≡ false → (y <ᵇ suc z) ≡ false → (x ⊓ y <ᵇ suc z) ≡ false
x<ᵇsucz=false∧y<ᵇsucz=false⇒x⊓y<ᵇsucz=false {suc x} {suc y} {zero} x<ᵇsucz=false y<ᵇsucz≡false = x<ᵇsucz=false
x<ᵇsucz=false∧y<ᵇsucz=false⇒x⊓y<ᵇsucz=false {suc x} {suc y} {suc z} x<ᵇsucz=false y<ᵇsucz≡false = x<ᵇsucz=false∧y<ᵇsucz=false⇒x⊓y<ᵇsucz=false {x} {y} {z} x<ᵇsucz=false y<ᵇsucz≡false

x≤ᵇz=false∧y≤ᵇz=false⇒x⊓y≤ᵇz=false : {x y z : ℕ} → (x ≤ᵇ z) ≡ false → (y ≤ᵇ z) ≡ false → (x ⊓ y ≤ᵇ z) ≡ false
x≤ᵇz=false∧y≤ᵇz=false⇒x⊓y≤ᵇz=false {suc x} {suc y} {zero} x≤ᵇz=false y≤ᵇz≡false = x≤ᵇz=false
x≤ᵇz=false∧y≤ᵇz=false⇒x⊓y≤ᵇz=false {suc x} {suc y} {suc z} x≤ᵇz=false y≤ᵇz≡false = x<ᵇsucz=false∧y<ᵇsucz=false⇒x⊓y<ᵇsucz=false {x} {y} {z} x≤ᵇz=false y≤ᵇz≡false

x≤ᵍz=false∧y≤ᵍz=false⇒x⊓ᵍy≤ᵍz=false : {x y z : ℕ̃} → x ≤ᵍ z ≡ false → y ≤ᵍ z ≡ false → x ⊓ᵍ y ≤ᵍ z ≡ false
x≤ᵍz=false∧y≤ᵍz=false⇒x⊓ᵍy≤ᵍz=false {⊤} {⊤} {⊤} x≤ᵍz=false y≤ᵍz≡false = x≤ᵍz=false
x≤ᵍz=false∧y≤ᵍz=false⇒x⊓ᵍy≤ᵍz=false {n≤⊤ x} {⊤} {⊤} x≤ᵍz=false y≤ᵍz≡false = x≤ᵍz=false
x≤ᵍz=false∧y≤ᵍz=false⇒x⊓ᵍy≤ᵍz=false {x} {n≤⊤ y₁} {⊤} x≤ᵍz=false y≤ᵍz≡false = ⊥-elim (contradiction₂ y≤ᵍz≡false)
x≤ᵍz=false∧y≤ᵍz=false⇒x⊓ᵍy≤ᵍz=false {⊤} {⊤} {n≤⊤ z₁} x≤ᵍz=false y≤ᵍz≡false = x≤ᵍz=false
x≤ᵍz=false∧y≤ᵍz=false⇒x⊓ᵍy≤ᵍz=false {n≤⊤ x₁} {⊤} {n≤⊤ z₁} x≤ᵍz=false y≤ᵍz≡false = x≤ᵍz=false
x≤ᵍz=false∧y≤ᵍz=false⇒x⊓ᵍy≤ᵍz=false {⊤} {n≤⊤ y₁} {n≤⊤ z₁} x≤ᵍz=false y≤ᵍz≡false = y≤ᵍz≡false
x≤ᵍz=false∧y≤ᵍz=false⇒x⊓ᵍy≤ᵍz=false {n≤⊤ x₁} {n≤⊤ y₁} {n≤⊤ z₁} x≤ᵍz=false y≤ᵍz≡false = x≤ᵇz=false∧y≤ᵇz=false⇒x⊓y≤ᵇz=false {x₁} {y₁} {z₁} x≤ᵍz=false y≤ᵍz≡false

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

neval' : (ℕ → ℕ → ℕ) → value → value → value
neval' f (valₙ x₁) (valₙ x₂) = valₙ (f x₁ x₂)
neval' f (valₙ x₁) (valₒ x₂) = valₙ (f x₁ (b→n x₂))
neval' f (valₒ x₁) (valₙ x₂) = valₙ (f (b→n x₁) x₂)
neval' f (valₒ x₁) (valₒ x₂) = valₙ (f (b→n x₁) (b→n x₂))
neval' f v₁ undef = undef
neval' f undef v₂ = undef

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
⟦ n-add e₁ e₂ ⟧ₙₑ s = neval' _+_ (⟦ e₁ ⟧ₙₑ s)  (⟦ e₂ ⟧ₙₑ s)
⟦ n-sub e₁ e₂ ⟧ₙₑ s = neval' _∸_ (⟦ e₁ ⟧ₙₑ s)  (⟦ e₂ ⟧ₙₑ s)
⟦ n-mul e₁ e₂ ⟧ₙₑ s = neval' _*_ (⟦ e₁ ⟧ₙₑ s)  (⟦ e₂ ⟧ₙₑ s)

⟦_⟧ₒₑ : bexp → state → value
⟦ b-const e ⟧ₒₑ     s = valₒ e
⟦ b-var e ⟧ₒₑ       s = vn→b (s e)
⟦ b-not e ⟧ₒₑ       s = nbeval' not (⟦ e ⟧ₒₑ s)
⟦ b-or e₁ e₂ ⟧ₒₑ    s = bbeval' _∨_ (⟦ e₁ ⟧ₒₑ s)  (⟦ e₂ ⟧ₒₑ s)
⟦ b-and e₁ e₂ ⟧ₒₑ   s = bbeval' _∧_ (⟦ e₁ ⟧ₒₑ s)  (⟦ e₂ ⟧ₒₑ s)
⟦ b-less e₁ e₂ ⟧ₒₑ  s = nnbeval' _≤ᵇ_ (⟦ e₁ ⟧ₙₑ s)  (⟦ e₂ ⟧ₙₑ s)
⟦ b-eq e₁ e₂ ⟧ₒₑ    s = nnbeval'  =' (⟦ e₁ ⟧ₙₑ s)  (⟦ e₂ ⟧ₙₑ s)

⟦_⟧ᵣₑ : rexp → state → value
⟦ rbexp e ⟧ᵣₑ s = ⟦ e ⟧ₒₑ s
⟦ rnexp e ⟧ᵣₑ s = ⟦ e ⟧ₙₑ s

postulate
  eval-notfalse→true : {e : bexp} {s : state} → nbeval' not (⟦ e ⟧ₒₑ s) ≡ valₒ false → (⟦ e ⟧ₒₑ s) ≡ valₒ true
  eval-nottrue→false : {e : bexp} {s : state} → nbeval' not (⟦ e ⟧ₒₑ s) ≡ valₒ true → (⟦ e ⟧ₒₑ s) ≡ valₒ false

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
s[≡l]s'-trans {l} {s₁} {s₂} {s₃} s₁[≡l]s₂ s₂[≡l]s₃ {v} vsl≤l =  trans (s₁[≡l]s₂ {v} vsl≤l) (s₂[≡l]s₃ {v} vsl≤l)  

s[≡l]s'-sym : {l : ℕ} {s₁ s₂ : state} → s₁ [≡ l ] s₂ → s₂ [≡ l ] s₁
s[≡l]s'-sym {l} {s₁} {s₂} s₁[≡l]s₂ {v} vsl≤l = sym (s₁[≡l]s₂ {v} vsl≤l) 

s[≡l]s'-refl : {l : ℕ} {s : state} → s [≡ l ] s
s[≡l]s'-refl = λ _ → refl


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
safe-evalₙₑ {l} {s₁} {s₂} {n-const x} {v₁} {v₂} s₁=ₗs₂ e≤l ve₁ ve₂ = trans ve₁ (sym ve₂)
safe-evalₙₑ {l} {s₁} {s₂} {n-var x} {v₁} {v₂} s₁=ₗs₂ e≤l ve₁ ve₂ =  trans (trans ve₁ (cong vb→n (s₁=ₗs₂ {x} e≤l))) (sym ve₂)
safe-evalₙₑ {l} {s₁} {s₂} {n-add e₁ e₂} {v₁} {v₂} s₁=ₗs₂ e≤l ve₁ ve₂ with safe-evalₙₑ {l} {s₁} {s₂} {e₁} s₁=ₗs₂ (m⊔n≤o⇒m≤o (secₙₑ secᵥ' e₁) (secₙₑ secᵥ' e₂) e≤l ) refl refl | safe-evalₙₑ {l} {s₁} {s₂} {e₂} s₁=ₗs₂ (m⊔n≤o⇒n≤o (secₙₑ secᵥ' e₁) (secₙₑ secᵥ' e₂) e≤l ) refl refl
... | eq₁ | eq₂ = trans ve₁ (trans (cong₂ (neval' _+_) (eq₁) (eq₂)) (sym ve₂))
safe-evalₙₑ {l} {s₁} {s₂} {n-sub e₁ e₂} {v₁} {v₂} s₁=ₗs₂ e≤l ve₁ ve₂ with safe-evalₙₑ {l} {s₁} {s₂} {e₁} s₁=ₗs₂ (m⊔n≤o⇒m≤o (secₙₑ secᵥ' e₁) (secₙₑ secᵥ' e₂) e≤l ) refl refl | safe-evalₙₑ {l} {s₁} {s₂} {e₂} s₁=ₗs₂ (m⊔n≤o⇒n≤o (secₙₑ secᵥ' e₁) (secₙₑ secᵥ' e₂) e≤l ) refl refl
... | eq₁ | eq₂ = trans ve₁ (trans (cong₂ (neval' _∸_) (eq₁) (eq₂)) (sym ve₂))
safe-evalₙₑ {l} {s₁} {s₂} {n-mul e₁ e₂} {v₁} {v₂} s₁=ₗs₂ e≤l ve₁ ve₂ with safe-evalₙₑ {l} {s₁} {s₂} {e₁} s₁=ₗs₂ (m⊔n≤o⇒m≤o (secₙₑ secᵥ' e₁) (secₙₑ secᵥ' e₂) e≤l ) refl refl | safe-evalₙₑ {l} {s₁} {s₂} {e₂} s₁=ₗs₂ (m⊔n≤o⇒n≤o (secₙₑ secᵥ' e₁) (secₙₑ secᵥ' e₂) e≤l ) refl refl
... | eq₁ | eq₂ = trans ve₁ (trans (cong₂ (neval' _*_) (eq₁) (eq₂)) (sym ve₂))

--  evaluation of boolean-expression of visible area always produces same result
safe-evalₒₑ : {l : ℕ} {s₁ s₂ : state} {e : bexp} {v₁ v₂ : value}
            → s₁ [≡ l ] s₂
            → secₒₑ secᵥ' e ≤ l
            → v₁ ≡ ⟦ e ⟧ₒₑ s₁
            → v₂ ≡ ⟦ e ⟧ₒₑ s₂
            → v₁ ≡ v₂
safe-evalₒₑ {l} {s₁} {s₂} {b-const x} {v₁} {v₂} s₁=ₗs₂ e≤l ve₁ ve₂ = trans ve₁ (sym ve₂)
safe-evalₒₑ {l} {s₁} {s₂} {b-var x} {v₁} {v₂} s₁=ₗs₂ e≤l ve₁ ve₂ = trans (trans ve₁ (cong vn→b (s₁=ₗs₂ {x} e≤l))) (sym ve₂)
safe-evalₒₑ {l} {s₁} {s₂} {b-not e} {v₁} {v₂} s₁=ₗs₂ e≤l ve₁ ve₂ with safe-evalₒₑ {l} {s₁} {s₂} {e} {⟦ e ⟧ₒₑ s₁} {⟦ e ⟧ₒₑ s₂} s₁=ₗs₂ e≤l refl refl
... | eq₁ = trans ve₁ (trans (cong (nbeval' not) (eq₁)) (sym ve₂))
safe-evalₒₑ {l} {s₁} {s₂} {b-or e₁ e₂} {v₁} {v₂} s₁=ₗs₂ e≤l ve₁ ve₂ with safe-evalₒₑ {l} {s₁} {s₂} {e₁} s₁=ₗs₂ (m⊔n≤o⇒m≤o (secₒₑ secᵥ' e₁) (secₒₑ secᵥ' e₂) e≤l ) refl refl | safe-evalₒₑ {l} {s₁} {s₂} {e₂} s₁=ₗs₂ (m⊔n≤o⇒n≤o (secₒₑ secᵥ' e₁) (secₒₑ secᵥ' e₂) e≤l ) refl refl
... | eq₁ | eq₂ = trans ve₁ (trans (cong₂ (bbeval' _∨_) (eq₁) (eq₂)) (sym ve₂))
safe-evalₒₑ {l} {s₁} {s₂} {b-and e₁ e₂} {v₁} {v₂} s₁=ₗs₂ e≤l ve₁ ve₂ with safe-evalₒₑ {l} {s₁} {s₂} {e₁} s₁=ₗs₂ (m⊔n≤o⇒m≤o (secₒₑ secᵥ' e₁) (secₒₑ secᵥ' e₂) e≤l ) refl refl | safe-evalₒₑ {l} {s₁} {s₂} {e₂} s₁=ₗs₂ (m⊔n≤o⇒n≤o (secₒₑ secᵥ' e₁) (secₒₑ secᵥ' e₂) e≤l ) refl refl
... | eq₁ | eq₂ = trans ve₁ (trans (cong₂ (bbeval' _∧_) (eq₁) (eq₂)) (sym ve₂))
safe-evalₒₑ {l} {s₁} {s₂} {b-less x₁ x₂} {v₁} {v₂} s₁=ₗs₂ e≤l ve₁ ve₂ with safe-evalₙₑ {l} {s₁} {s₂} {x₁} s₁=ₗs₂ (m⊔n≤o⇒m≤o (secₙₑ secᵥ' x₁) (secₙₑ secᵥ' x₂) e≤l ) refl refl | safe-evalₙₑ {l} {s₁} {s₂} {x₂} s₁=ₗs₂ (m⊔n≤o⇒n≤o (secₙₑ secᵥ' x₁) (secₙₑ secᵥ' x₂) e≤l ) refl refl
... | eq₁ | eq₂ = trans ve₁ (trans (cong₂ (nnbeval' _≤ᵇ_) (eq₁) (eq₂)) (sym ve₂))
safe-evalₒₑ {l} {s₁} {s₂} {b-eq x₁ x₂} {v₁} {v₂} s₁=ₗs₂ e≤l ve₁ ve₂ with safe-evalₙₑ {l} {s₁} {s₂} {x₁} s₁=ₗs₂ (m⊔n≤o⇒m≤o (secₙₑ secᵥ' x₁) (secₙₑ secᵥ' x₂) e≤l ) refl refl | safe-evalₙₑ {l} {s₁} {s₂} {x₂} s₁=ₗs₂ (m⊔n≤o⇒n≤o (secₙₑ secᵥ' x₁) (secₙₑ secᵥ' x₂) e≤l ) refl refl
... | eq₁ | eq₂ = trans ve₁ (trans (cong₂ (nnbeval' =') (eq₁) (eq₂)) (sym ve₂))

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
safe-evalᵣₑ {l} {s₁} {s₂} {rbexp be} {v₁} {v₂} s₁=ₗs₂ e≤l ve₁ ve₂ = safe-evalₒₑ {l} {s₁} {s₂} {be} {_} {_} s₁=ₗs₂  e≤l ve₁ ve₂  
safe-evalᵣₑ {l} {s₁} {s₂} {rnexp ne} {v₁} {v₂} s₁=ₗs₂ e≤l ve₁ ve₂ = safe-evalₙₑ {l} {s₁} {s₂} {ne} {_} {_} s₁=ₗs₂  e≤l ve₁ ve₂   

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

safe-write1 {l} {s₁} {s₂} {s₁'} {s₂'} {x} {e} {v₁} {v₂} s₁=ₗs₂ x≤l e≤l ve₁ ve₂ c₁ c₂ {y} y≤l with x == y | inspect (x ==_) y
... | false | [ x≠y ] rewrite s[x↦v]-elim₂ {s₁} {s₁'} {x} {y} {v₁} c₁ x≠y | s[x↦v]-elim₂ {s₂} {s₂'} {x} {y} {v₂} c₂ x≠y = s₁=ₗs₂ y≤l
... | true  | [ x=y ] rewrite s[x↦v]-elim₁ {s₁} {s₁'} {x} {y} {v₁} c₁ x=y | s[x↦v]-elim₁ {s₂} {s₂'} {x} {y} {v₂} c₂ x=y = safe-evalᵣₑ {l} {s₁} {s₂} {e} {_} {_} s₁=ₗs₂ e≤l ve₁ ve₂     

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
            
safe-write2 {l} {s₁} {s₂} {s₁'} {s₂'} {x} {e} {v₁} {v₂} s₁=ₗs₂ l<x ve₁ ve₂ c₁ c₂ {y} y≤l rewrite
  l-neq (≤-<-trans {secᵥ' y} {l} {secᵥ' x} y≤l l<x) | s[x↦v]-elim₂ {s₁} {s₁'} {x} {y} {v₁} c₁ (l-neq (≤-<-trans {secᵥ' y} {l} {secᵥ' x} y≤l l<x)) |
  s[x↦v]-elim₂ {s₂} {s₂'} {x} {y} {v₂} c₂ (l-neq (≤-<-trans {secᵥ' y} {l} {secᵥ' x} y≤l l<x))
  = s₁=ₗs₂ y≤l

-- single version of safe-write2
safe-write3 : {l : ℕ} {s : state} {s' : state} {x : var} {e : rexp} {v : value} 
            → l < secᵥ' x
            → v ≡ ⟦ e ⟧ᵣₑ s
            → s' ≡ s [ x ↦ v ] 
            → s [≡ l ] s'

safe-write3 {l} {s} {s'} {x} {e} {v} l<x ve c {y} y≤l rewrite l-neq (≤-<-trans y≤l l<x) | s[x↦v]-elim₂ {s} {s'} {x} {y} {v} c (l-neq (≤-<-trans y≤l l<x)) = refl

postulate
  ¬≤ᵇ-elim : {a b : ℕ } → (a ≤ᵇ b) ≡ false → b < a
  a<b∧b≤c⇒a<c : {a b : ℕ} {c : ℕ̃} → (b ≤ᵇ a) ≡ false → n≤⊤ b ≤ᵍ c ≡ true → c ≤ᵍ n≤⊤ a ≡ false 

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
accepIfThenNoInterfere₁ {e} {st₁} {st₂} acc-if with accept st₁ secᵥ' | accept st₂ secᵥ'
... | true | true = refl , refl

constcon₁ : (valₒ false ≡ valₒ true) → true ≡ false
constcon₁ ()

constcon₂ : (valₒ true ≡ valₒ false) → true ≡ false
constcon₂ ()

highLevelMayProduceDiff : {e : bexp} {s₁ s₂ : state} {l : ℕ}
                        → s₁ [≡ l ] s₂
                        → ⟦ e ⟧ₒₑ s₁ ≡ valₒ true
                        → ⟦ e ⟧ₒₑ s₂ ≡ valₒ false
                        → (secₒₑ secᵥ' e ≤ᵇ l) ≡ false

highLevelMayProduceDiff {b-const false} {s₁} {s₂} {l} s₁=ₗs₂ e₁=true e₂=false = constcon₁ e₁=true
highLevelMayProduceDiff {b-const true} {s₁} {s₂} {l} s₁=ₗs₂ e₁=true e₂=false = constcon₂ e₂=false
highLevelMayProduceDiff {b-var x} {s₁} {s₂} {l} s₁=ₗs₂ e₁=true e₂=false with ((secᵥ' x) ≤ᵇ l) | inspect (secᵥ' x ≤ᵇ_) l
... | false | [ sx≰l ] = refl
... | true  | [ sx≤l ] rewrite s₁=ₗs₂ (≤ᵇ-elim sx≤l) = constcon₂ (trans (sym e₁=true) e₂=false)
highLevelMayProduceDiff {b-not e} {s₁} {s₂} {l} s₁=ₗs₂ e₁=true e₂=false = highLevelMayProduceDiff {e} {s₂} {s₁} (s[≡l]s'-sym s₁=ₗs₂) (eval-notfalse→true {e} {s₂} e₂=false) (eval-nottrue→false {e} {s₁} e₁=true)
highLevelMayProduceDiff {b-or e₁ e₂} {s₁} {s₂} {l} s₁=ₗs₂ e₁=true e₂=false = {!   !}
highLevelMayProduceDiff {b-and e₁ e₂} {s₁} {s₂} {l} s₁=ₗs₂ e₁=true e₂=false = {!   !}
highLevelMayProduceDiff {b-less x₁ x₂} {s₁} {s₂} {l} s₁=ₗs₂ e₁=true e₂=false = {!   !}
highLevelMayProduceDiff {b-eq x₁ x₂} {s₁} {s₂} {l} s₁=ₗs₂ e₁=true e₂=false = {!   !} 


contradiction : {st : stmt} {l : ℕ} → (false ≡ true) → secₛₜ secᵥ' st ≤ᵍ n≤⊤ l ≡ false
contradiction ()

accepIfThenNoInterfere₂-TF-st₁ : {e : bexp} { st₁ st₂ : stmt} {s₁ s₂ : state} {l : ℕ}
                        → s₁ [≡ l ] s₂  
                        → (n≤⊤ (secₒₑ secᵥ' e) ≤ᵍ secₛₜ secᵥ' st₁ ⊓ᵍ secₛₜ secᵥ' st₂) ≡ true
                        → ⟦ e ⟧ₒₑ s₁ ≡ valₒ true
                        → ⟦ e ⟧ₒₑ s₂ ≡ valₒ false 
                        → secₛₜ secᵥ' st₁ ≤ᵍ n≤⊤ l ≡ false

accepIfThenNoInterfere₂-TF-st₁ {e} {st₁} {st₂} {s₁} {s₂} {l} s₁=ₗs₂ acc-if e₁=true e₂=false = a<b∧b≤c⇒a<c {l} {secₒₑ secᵥ' e} {secₛₜ secᵥ' st₁} l<e e≤st₁ where
  l<e : (secₒₑ secᵥ' e ≤ᵇ l) ≡ false
  l<e = highLevelMayProduceDiff {e} {s₁} {s₂} {l} s₁=ₗs₂ e₁=true e₂=false
  
  e≤st₁ : n≤⊤ (secₒₑ secᵥ' e) ≤ᵍ secₛₜ secᵥ' st₁ ≡ true
  e≤st₁ = x≤y⊓ᵍz₁ {n≤⊤ (secₒₑ secᵥ' e)} {secₛₜ secᵥ' st₁} {secₛₜ secᵥ' st₂} acc-if 

accepIfThenNoInterfere₂-TF-st₂ : {e : bexp} { st₁ st₂ : stmt} {s₁ s₂ : state} {l : ℕ}
                        → s₁ [≡ l ] s₂  
                        → (n≤⊤ (secₒₑ secᵥ' e) ≤ᵍ secₛₜ secᵥ' st₁ ⊓ᵍ secₛₜ secᵥ' st₂) ≡ true
                        → ⟦ e ⟧ₒₑ s₁ ≡ valₒ true
                        → ⟦ e ⟧ₒₑ s₂ ≡ valₒ false 
                        → secₛₜ secᵥ' st₂ ≤ᵍ n≤⊤ l ≡ false

accepIfThenNoInterfere₂-TF-st₂ {e} {st₁} {st₂} {s₁} {s₂} {l} s₁=ₗs₂ acc-if e₁=true e₂=false = a<b∧b≤c⇒a<c {l} {secₒₑ secᵥ' e} {secₛₜ secᵥ' st₂} l<e e≤st₂ where 
  l<e : (secₒₑ secᵥ' e ≤ᵇ l) ≡ false
  l<e = highLevelMayProduceDiff {e} {s₁} {s₂} {l} s₁=ₗs₂ e₁=true e₂=false
  
  e≤st₂ : n≤⊤ (secₒₑ secᵥ' e) ≤ᵍ secₛₜ secᵥ' st₂ ≡ true
  e≤st₂ = x≤y⊓ᵍz₂ {n≤⊤ (secₒₑ secᵥ' e)} {secₛₜ secᵥ' st₁} {secₛₜ secᵥ' st₂} acc-if 


accepIfThenNoInterfere₂-FT-st₁ : {e : bexp} { st₁ st₂ : stmt} {s₁ s₂ : state} {l : ℕ}
                        → s₁ [≡ l ] s₂  
                        → (n≤⊤ (secₒₑ secᵥ' e) ≤ᵍ secₛₜ secᵥ' st₁ ⊓ᵍ secₛₜ secᵥ' st₂) ≡ true
                        → ⟦ e ⟧ₒₑ s₁ ≡ valₒ false
                        → ⟦ e ⟧ₒₑ s₂ ≡ valₒ true 
                        → secₛₜ secᵥ' st₁ ≤ᵍ n≤⊤ l ≡ false

accepIfThenNoInterfere₂-FT-st₁ {e} {st₁} {st₂}  {s₁} {s₂} {l} s₁=ₗs₂ acc-if e₁=false e₂=true = a<b∧b≤c⇒a<c {l} {secₒₑ secᵥ' e} {secₛₜ secᵥ' st₁} l<e e≤st₁ where
  l<e : (secₒₑ secᵥ' e ≤ᵇ l) ≡ false
  l<e = highLevelMayProduceDiff {e} {s₂} {s₁} {l} (s[≡l]s'-sym s₁=ₗs₂) e₂=true e₁=false
  
  e≤st₁ : n≤⊤ (secₒₑ secᵥ' e) ≤ᵍ secₛₜ secᵥ' st₁ ≡ true
  e≤st₁ = x≤y⊓ᵍz₁ {n≤⊤ (secₒₑ secᵥ' e)} {secₛₜ secᵥ' st₁} {secₛₜ secᵥ' st₂} acc-if 

accepIfThenNoInterfere₂-FT-st₂ : {e : bexp} { st₁ st₂ : stmt} {s₁ s₂ : state} {l : ℕ}
                        → s₁ [≡ l ] s₂  
                        → (n≤⊤ (secₒₑ secᵥ' e) ≤ᵍ secₛₜ secᵥ' st₁ ⊓ᵍ secₛₜ secᵥ' st₂) ≡ true
                        → ⟦ e ⟧ₒₑ s₁ ≡ valₒ false
                        → ⟦ e ⟧ₒₑ s₂ ≡ valₒ true 
                        → secₛₜ secᵥ' st₂ ≤ᵍ n≤⊤ l ≡ false

accepIfThenNoInterfere₂-FT-st₂ {e} {st₁} {st₂} {s₁} {s₂} {l} s₁=ₗs₂ acc-if e₁=false e₂=true = a<b∧b≤c⇒a<c {l} {secₒₑ secᵥ' e} {secₛₜ secᵥ' st₂} l<e e≤st₂ where 
  l<e : (secₒₑ secᵥ' e ≤ᵇ l) ≡ false
  l<e = highLevelMayProduceDiff {e} {s₂} {s₁} {l} (s[≡l]s'-sym s₁=ₗs₂) e₂=true e₁=false
  
  e≤st₂ : n≤⊤ (secₒₑ secᵥ' e) ≤ᵍ secₛₜ secᵥ' st₂ ≡ true
  e≤st₂ = x≤y⊓ᵍz₂ {n≤⊤ (secₒₑ secᵥ' e)} {secₛₜ secᵥ' st₁} {secₛₜ secᵥ' st₂} acc-if 


accpeWhileThenNoInterfere₁ : {e : bexp} {st : stmt} → accept (while e loop st) secᵥ' ≡ true → (accept st secᵥ' ≡ true)
accpeWhileThenNoInterfere₁ {e} {st} acc-while with accept st secᵥ'
... | true = refl 

accpeWhileThenNoInterfere₂ : {e : bexp} {st : stmt} {s₁ s₂ : state} {l : ℕ} 
                            → s₁ [≡ l ] s₂
                            → accept (while e loop st) secᵥ' ≡ true 
                            → ⟦ e ⟧ₒₑ s₁ ≡ valₒ true
                            → ⟦ e ⟧ₒₑ s₂ ≡ valₒ false
                            → secₛₜ secᵥ' st ≤ᵍ n≤⊤ l ≡ false

accpeWhileThenNoInterfere₂ {e} {st} {s₁} {s₂} {l} s₁=ₗs₂ acc e₁=true e₂=false = a<b∧b≤c⇒a<c {l} {secₒₑ secᵥ' e} {secₛₜ secᵥ' st} l<e e≤st where 
  l<e : (secₒₑ secᵥ' e ≤ᵇ l) ≡ false
  l<e = highLevelMayProduceDiff {e} {s₁} {s₂} {l} (s₁=ₗs₂) e₁=true e₂=false

  e≤st : n≤⊤ (secₒₑ secᵥ' e) ≤ᵍ secₛₜ secᵥ' st ≡ true
  e≤st with accept st secᵥ' 
  ... | true = acc

accepSeqThenNoInterfere₁ : { st₁ st₂ : stmt} → accept (st₁ ⍮ st₂) secᵥ' ≡ true → accept st₁ secᵥ' ≡ true
accepSeqThenNoInterfere₁ acc-seq = ∧-elim₁ acc-seq

accepSeqThenNoInterfere₂ : { st₁ st₂ : stmt} → accept (st₁ ⍮ st₂) secᵥ' ≡ true → accept st₂ secᵥ' ≡ true
accepSeqThenNoInterfere₂ acc-seq = ∧-elim₂ acc-seq


postulate
  c<a⊔b∧b≤a⇒c<a : {a b c : ℕ} → (a ⊔ b ≤ᵇ c) ≡ false → (b ≤ᵇ a) ≡ true → c < a
  c<a⊓ᵍb⇒c<a : {a b c : ℕ̃} → a ⊓ᵍ b ≤ᵍ c ≡ false → a ≤ᵍ c ≡ false
  c<a⊓ᵍb⇒c<b : {a b c : ℕ̃} → a ⊓ᵍ b ≤ᵍ c ≡ false → b ≤ᵍ c ≡ false 
  d<a⊓ᵍb⊓ᵍc⇒d<b : {a b c d : ℕ̃} → a ⊓ᵍ b ⊓ᵍ c ≤ᵍ d ≡ false → b ≤ᵍ d ≡ false
  d<a⊓ᵍb⊓ᵍc⇒d<c : {a b c d : ℕ̃} → a ⊓ᵍ b ⊓ᵍ c ≤ᵍ d ≡ false → c ≤ᵍ d ≡ false
        

-- single evaluation at high level is safe
lemma₁ : {l : ℕ} {s s' : state}
          → (st : stmt)
          → accept st secᵥ' ≡ true
          → (secₛₜ secᵥ' st ≤ᵍ n≤⊤ l) ≡ false
          → ❴ s ❵ st ❴ s' ❵
          → s [≡ l ] s'

lemma₁ {l} {s} {.s} skip acc st≤ᵍl=false (❴ .s ❵skip❴ s' ❵ s=s') = λ _ → refl
lemma₁ {l} {s} {s'} (lvar x := e) acc st≤ᵍl=false (❴ .s ❵assign❴ .s' ❵ s'=s[x↦e]) = safe-write3 {l} {s} {s'} {x} {e} {⟦ e ⟧ᵣₑ s} l<x refl s'=s[x↦e] where
  l<x : l < secᵥ' x
  l<x = c<a⊔b∧b≤a⇒c<a {secᵥ' x} {secᵣₑ secᵥ' e} {l} st≤ᵍl=false acc

lemma₁ {l} {s} {s'} (if e then st₁ else st₂) acc st≤ᵍl=false (❴ .s ❵if-true❴ .s' ❵ e=true c) = lemma₁ {l} {s} {s'} st₁ accst₁ l<st₁ c where
  accst₁ : accept st₁ secᵥ' ≡ true
  accst₁ with accept st₁ secᵥ'
  ... | true = refl

  l<st₁ : secₛₜ secᵥ' st₁ ≤ᵍ n≤⊤ l ≡ false
  l<st₁ = d<a⊓ᵍb⊓ᵍc⇒d<b {n≤⊤ (secₒₑ secᵥ' e)} {secₛₜ secᵥ' st₁} {secₛₜ secᵥ' st₂} {n≤⊤ l} st≤ᵍl=false 
lemma₁ {l} {s} {s'} (if e then st₁ else st₂) acc st≤ᵍl=false (❴ .s ❵if-false❴ .s' ❵ e=false c) = lemma₁ {l} {s} {s'} st₂ accst₂ l<st₂ c where
  accst₂ : accept st₂ secᵥ' ≡ true
  accst₂ with  accept st₁ secᵥ' | accept st₂ secᵥ'
  ... | true | true = refl

  l<st₂ : secₛₜ secᵥ' st₂ ≤ᵍ n≤⊤ l ≡ false
  l<st₂ = d<a⊓ᵍb⊓ᵍc⇒d<c {n≤⊤ (secₒₑ secᵥ' e)} {secₛₜ secᵥ' st₁} {secₛₜ secᵥ' st₂} {n≤⊤ l} st≤ᵍl=false

lemma₁ {l} {s} {s'} (while e loop st) acc st≤ᵍl=false (❴ .s ❵while-false❴ .s' ❵ e=false s⇒s') rewrite s⇒s' = λ _ → refl
lemma₁ {l} {s} {s'} (while e loop st) acc st≤ᵍl=false (❴ .s ❵while-true❴ .s' ❵ e=true s⇒sₜ sₜ⇒s') = s[≡l]s'-trans (lemma₁ {l} {s} st accst l<st s⇒sₜ) (lemma₁ {l} {_} {s'} (while e loop st) accwhile l<while sₜ⇒s') where 
  accst : accept st secᵥ' ≡ true 
  accst with accept st secᵥ'
  ... | true = refl

  l<st : secₛₜ secᵥ' st ≤ᵍ n≤⊤ l ≡ false
  l<st = c<a⊓ᵍb⇒c<b {n≤⊤ (secₒₑ secᵥ' e)} {secₛₜ secᵥ' st}  st≤ᵍl=false

  accwhile : accept (while e loop st) secᵥ' ≡ true
  accwhile = acc

  l<while : secₛₜ secᵥ' (while e loop st) ≤ᵍ n≤⊤ l ≡ false
  l<while = st≤ᵍl=false

lemma₁ {l} {s} {s'} (st₁ ⍮ st₂) acc st≤ᵍl=false (❴ .s ❵seq❴ .s' ❵ s⇒sₜ sₜ⇒s') = s[≡l]s'-trans (lemma₁ {l} {s} st₁ accst₁ l<st₁ s⇒sₜ) (lemma₁ {l} {_} {s'} st₂ accst₂ l<st₂ sₜ⇒s') where
  accst₁ : accept st₁ secᵥ' ≡ true 
  accst₁ with accept st₁ secᵥ' 
  ... | true = refl

  l<st₁ : secₛₜ secᵥ' st₁ ≤ᵍ n≤⊤ l ≡ false
  l<st₁ = c<a⊓ᵍb⇒c<a {secₛₜ secᵥ' st₁} {secₛₜ secᵥ' st₂} st≤ᵍl=false

  accst₂ : accept st₂ secᵥ' ≡ true
  accst₂ with accept st₁ secᵥ' | accept st₂ secᵥ' 
  ... | true | true = refl

  l<st₂ : secₛₜ secᵥ' st₂ ≤ᵍ n≤⊤ l ≡ false
  l<st₂ = c<a⊓ᵍb⇒c<b {secₛₜ secᵥ' st₁} {secₛₜ secᵥ' st₂} st≤ᵍl=false  

-- multiple evaluations at high level are safe
corollary₁ : {l : ℕ}
          → (s₁ : state) → (s₁' : state)
          → (s₂ : state) → (s₂' : state)
          → s₁ [≡ l ] s₂ 
          → (st₁ : stmt)
          → (st₂ : stmt)
          → accept st₁ secᵥ' ≡ true
          → accept st₂ secᵥ' ≡ true
          → (secₛₜ secᵥ' st₁ ≤ᵍ n≤⊤ l) ≡ false
          → (secₛₜ secᵥ' st₂ ≤ᵍ n≤⊤ l) ≡ false
          → ❴ s₁ ❵ st₁ ❴ s₁' ❵
          → ❴ s₂ ❵ st₂ ❴ s₂' ❵
          → s₁' [≡ l ] s₂'

corollary₁ {l} s₁ s₁' s₂ s₂' s₁=ₗs₂ st₁ st₂ acc₁ acc₂  l₁<l l₂<l c₁ c₂ 
  = s[≡l]s'-trans {l} {s₁'} {s₂} {s₂'}( 
      s[≡l]s'-trans {l} {s₁'} {s₁} {s₂} 
      (s[≡l]s'-sym {l} {s₁} {s₁'} (lemma₁ {l} {s₁} {s₁'} st₁ acc₁ l₁<l c₁))
      s₁=ₗs₂ 
    ) (lemma₁ {l} {s₂} {s₂'} st₂ acc₂ l₂<l c₂)



-- The final theorem, no interfere
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
  with secᵥ' x ≤ᵇ l | inspect (secᵥ' x ≤ᵇ_) l
... | false | [ vsec≰l ] = (safe-write2 {l} {s₁} {s₂} {s₁'} {s₂'} {x} {e} {⟦ e ⟧ᵣₑ s₁} {⟦ e ⟧ᵣₑ s₂} s₁=ₗs₂ (¬≤ᵇ-elim {secᵥ' x} {l} vsec≰l) refl refl c₁ c₂)
... | true  | [ vsec≤l ] = (safe-write1 {l} {s₁} {s₂} {s₁'} {s₂'} {x} {e} {⟦ e ⟧ᵣₑ s₁} {⟦ e ⟧ᵣₑ s₂} s₁=ₗs₂ 
              (≤ᵇ-elim {secᵥ' x} {l} vsec≤l) 
              (≤-trans (acceptAssignThenNoInterfere {x} {e} acc) (≤ᵇ-elim {secᵥ' x} {l} vsec≤l))  
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
theorem {l} s₁ s₁' s₂ s₂' s₁=ₗs₂ 
  (if e then st₁ else st₂) acc 
  (❴ s₁ ❵if-true❴ s₁' ❵ e=true₁ c₁) 
  (❴ s₂ ❵if-false❴ s₂' ❵ e=false₂ c₂) = s₁'=ₗs₂' where
--    st₁≤l=false : (secₛₜ secᵥ' st₁ ≤ᵍ n≤⊤ l) ≡ false
--    st₁≤l=false = (accepIfThenNoInterfere₂-TF-st₁ {e} {st₁} {st₂} s₁=ₗs₂ acc e=true₁ e=false₂)

--    st₂≤l=false : (secₛₜ secᵥ' st₂ ≤ᵍ n≤⊤ l) ≡ false
--    st₂≤l=false = (accepIfThenNoInterfere₂-TF-st₂ {e} {st₁} {st₂} s₁=ₗs₂ acc e=true₁ e=false₂)

    s₁'=ₗs₂' : s₁' [≡ l ] s₂'
    s₁'=ₗs₂' with accept st₁ secᵥ' | accept st₂ secᵥ' | inspect (accept st₁) secᵥ' | inspect (accept st₂) secᵥ'
    ... | true | true | [ acc₁ ] | [ acc₂ ] = corollary₁ s₁ s₁' s₂ s₂'  s₁=ₗs₂ st₁ st₂ acc₁ acc₂ 
                                                (accepIfThenNoInterfere₂-TF-st₁ {e} {st₁} {st₂} s₁=ₗs₂ acc e=true₁ e=false₂) 
                                                (accepIfThenNoInterfere₂-TF-st₂ {e} {st₁} {st₂} s₁=ₗs₂ acc e=true₁ e=false₂) c₁ c₂

theorem {l} s₁ s₁' s₂ s₂' s₁=ₗs₂ 
  (if e then st₁ else st₂) acc 
  (❴ s₁ ❵if-false❴ s₁' ❵ e=false₁ c₁) 
  (❴ s₂ ❵if-true❴ s₂' ❵ e=true₂ c₂) = s₁'=ₗs₂' where
    s₁'=ₗs₂' : s₁' [≡ l ] s₂'
    s₁'=ₗs₂' with accept st₁ secᵥ' | accept st₂ secᵥ' | inspect (accept st₁) secᵥ' | inspect (accept st₂) secᵥ'
    ... | true | true | [ acc₁ ] | [ acc₂ ] = corollary₁ s₁ s₁' s₂ s₂' (s₁=ₗs₂) st₂ st₁ acc₂ acc₁ 
                                                (accepIfThenNoInterfere₂-FT-st₂ {e} {st₁} {st₂} s₁=ₗs₂ acc e=false₁ e=true₂) 
                                                (accepIfThenNoInterfere₂-FT-st₁ {e} {st₁} {st₂} s₁=ₗs₂ acc e=false₁ e=true₂) c₁ c₂

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
  (❴ s₂ ❵while-false❴ s₂' ❵ e=false₂ s₂⇒s₂') {v} v≤l
  = trans 
    (sym ((s[≡l]s'-trans {l} {s₁} {_} {s₁'}  s₁=ₗsₜ  sₜ=ₗs₁') {v} v≤l)) s₁v=s₂'v where
      st≤l=false : secₛₜ secᵥ' st ≤ᵍ n≤⊤ l ≡ false
      st≤l=false = (accpeWhileThenNoInterfere₂ {e} {st} {s₁} {s₂} {l} s₁=ₗs₂ acc e=true₁ e=false₂)

      e≤l=false : (n≤⊤ (secₒₑ secᵥ' e) ≤ᵍ n≤⊤ l) ≡ false
      e≤l=false = ≤ᵇ⇒≤ᵍ {secₒₑ secᵥ' e} {l} (highLevelMayProduceDiff {e} {s₁} {s₂} {l} s₁=ₗs₂ e=true₁ e=false₂)

      accst : accept st secᵥ' ≡ true
      accst with accept st secᵥ' | inspect (accept st) secᵥ'
      ... | true | [ accst' ] = refl

      s₁=ₗsₜ : s₁ [≡ l ] _
      s₁=ₗsₜ = (lemma₁ st accst st≤l=false  s₁⇒sₜ)
  
      sₜ=ₗs₁' : _ [≡ l ] s₁'
      sₜ=ₗs₁' = (lemma₁ (while e loop st) acc (x≤ᵍz=false∧y≤ᵍz=false⇒x⊓ᵍy≤ᵍz=false {n≤⊤ (secₒₑ secᵥ' e)} {secₛₜ secᵥ' st} {n≤⊤ l} e≤l=false st≤l=false) sₜ⇒s₁')

      s₁v=s₂'v : s₁ v ≡ s₂' v
      s₁v=s₂'v rewrite s₂⇒s₂' = s₁=ₗs₂ {v} v≤l

theorem {l} s₁ s₁' s₂ s₂' s₁=ₗs₂ 
  (while e loop st) acc 
  (❴ s₁ ❵while-false❴ s₁' ❵ e=false₁ s₁⇒s₁') 
  (❴ s₂ ❵while-true❴ s₂' ❵ e=true₂ s₂⇒sₜ sₜ⇒s₂') {v} v≤l
  = trans s₁'v=s₂v ((s[≡l]s'-trans {l} {s₂} {_} {s₂'} s₂=ₗsₜ sₜ=ₗs₂') {v} v≤l) where 
      st≤l=false : secₛₜ secᵥ' st ≤ᵍ n≤⊤ l ≡ false
      st≤l=false = (accpeWhileThenNoInterfere₂ {e} {st} {s₂} {s₁} {l} (s[≡l]s'-sym s₁=ₗs₂) acc e=true₂ e=false₁)

      e≤l=false : (n≤⊤ (secₒₑ secᵥ' e) ≤ᵍ n≤⊤ l) ≡ false
      e≤l=false = ≤ᵇ⇒≤ᵍ {secₒₑ secᵥ' e} {l} (highLevelMayProduceDiff {e} {s₂} {s₁} {l} (s[≡l]s'-sym s₁=ₗs₂) e=true₂ e=false₁)

      accst : accept st secᵥ' ≡ true
      accst with accept st secᵥ' | inspect (accept st) secᵥ'
      ... | true | [ accst' ] = refl 

      s₂=ₗsₜ : s₂ [≡ l ] _
      s₂=ₗsₜ = (lemma₁ st accst st≤l=false  s₂⇒sₜ)
  
      sₜ=ₗs₂' : _ [≡ l ] s₂'
      sₜ=ₗs₂' = (lemma₁ (while e loop st) acc (x≤ᵍz=false∧y≤ᵍz=false⇒x⊓ᵍy≤ᵍz=false {n≤⊤ (secₒₑ secᵥ' e)} {secₛₜ secᵥ' st} {n≤⊤ l} e≤l=false st≤l=false) sₜ⇒s₂')

      s₁'v=s₂v : s₁' v ≡ s₂ v
      s₁'v=s₂v rewrite s₁⇒s₁' = s₁=ₗs₂ {v} v≤l

theorem s₁ s₁' s₂ s₂' s₁=ₗs₂ 
  (st₁ ⍮ st₂) acc 
  (❴ s₁ ❵seq❴ s₁' ❵ s₁⇒sₜ sₜ⇒s₁') 
  (❴ s₂ ❵seq❴ s₂' ❵ s₂⇒sₜ sₜ⇒s₂') 
  = theorem _ s₁' _ s₂' (
      theorem s₁ _ s₂ _ s₁=ₗs₂ st₁ (accepSeqThenNoInterfere₁ {st₁} {st₂} acc) s₁⇒sₜ s₂⇒sₜ
  ) st₂ ((accepSeqThenNoInterfere₂ {st₁} {st₂} acc)) sₜ⇒s₁' sₜ⇒s₂'