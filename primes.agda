-- Primes from Scratch --

-- Natural numbers

data ℕ : Set where
     zero : ℕ
     suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

infixr 10 _+_
_+_ : ℕ → ℕ → ℕ
0 + b = b
suc a + b = suc (a + b)

infixr 11 _*_
_*_ : ℕ → ℕ → ℕ
0 * b = 0
(suc a) * b = b + a * b

pred : ℕ → ℕ
pred 0 = 0
pred (suc n) = n

minus : ℕ → ℕ → ℕ
minus m 0 = m
minus m (suc n) =  minus (pred m) n

-- Booleans

data Bool : Set where
  true : Bool
  false : Bool

infix 10 _∨_
_∨_ : Bool → Bool → Bool
false ∨ false = false
_ ∨ _ = true

if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

-- Relations and predicates

infix 20 _<_
_<_ : ℕ → ℕ → Bool
0 < 0 = false
suc n < 0 = false
0 < suc n = true
suc m < suc n = m < n

infix 21 _=ℕ_
_=ℕ_ : ℕ → ℕ → Bool
0 =ℕ 0 = true
suc m =ℕ 0 = false
0 =ℕ suc n = false
suc m =ℕ suc n = m =ℕ n

nonzero : ℕ → Bool
nonzero 0 = false
nonzero (suc n) = true

iszero : ℕ → Bool
iszero 0 = true
iszero (suc n) = false

-- Division algorithm

record QuotData : Set where
  field
    remainder : ℕ
    quotient : ℕ
    divisor : ℕ

-- for testing:
qd : QuotData
qd = record { remainder = 16; quotient = 0; divisor = 5 }


-- One step in the division algorithm:
step : QuotData → QuotData
step qd =
  let
    rem = minus (QuotData.remainder qd) (QuotData.divisor qd)
  in
  if iszero rem
    then qd
    else (record qd { remainder = rem;  quotient = suc (QuotData.quotient qd) })
                


div-alg-aux : ℕ → QuotData → QuotData
div-alg-aux 0 qd =
   qd
div-alg-aux (suc n) qd =
    let
     rem = QuotData.remainder qd
     rem' = minus rem (QuotData.divisor qd)
    in
    if rem < QuotData.divisor qd then qd
    else if iszero rem'
    then record qd { remainder = 0; quotient = 1 + QuotData.quotient qd }
    else (div-alg-aux n (step qd))

  
div-alg : ℕ → ℕ → QuotData
div-alg n d =
  div-alg-aux n qdIn where
      qdIn = record { remainder = n; quotient = 0; divisor = d }

infix 12 _/_
_/_ : ℕ →  ℕ →  ℕ
n / d = QuotData.quotient qq where
          qq = div-alg n d

divides : ℕ → ℕ → Bool
divides d n =
  iszero rem where
    rem = QuotData.remainder (div-alg n d)
  
data Maybe {a} (A : Set a) : Set a where
  nothing : Maybe A
  just    : A → Maybe A

has-divisor : ℕ → ℕ → Maybe ℕ
has-divisor 0 n = nothing
has-divisor 1 n = nothing
has-divisor 2 n = nothing
has-divisor (suc k) n =
  if divides k n then just k
  else has-divisor k n

has-divisor' : ℕ → ℕ → Maybe ℕ
has-divisor' 0 n = nothing
has-divisor' 1 n = nothing
has-divisor' (suc k) n = -- trial divisor = n - k
  if divides (minus n  k) n then just (minus n k)
  else has-divisor' k n

least-divisor : ℕ → Maybe ℕ
least-divisor n = has-divisor' (pred n) n

greatest-divisor : ℕ → Maybe ℕ
greatest-divisor n = has-divisor n n

isprime : ℕ → Bool
isprime n with least-divisor n
... | nothing = true
... | just _ = false



data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A


infixr 50  _::_

record PrimeDivisors : Set where
  field
    target : ℕ
    quotient : ℕ
    divisors : List ℕ
    done : Bool

step-divisor-init : ℕ → PrimeDivisors
step-divisor-init n = record { target = n; quotient = n; divisors = []; done = false }



step-divisor : PrimeDivisors → PrimeDivisors
step-divisor divs with least-divisor (PrimeDivisors.quotient divs)
... | nothing = record divs { done = true }
... | just d = record divs { quotient = PrimeDivisors.quotient divs / d
                            ; divisors = d :: PrimeDivisors.divisors divs
                            ; done = false }
    



x0 : PrimeDivisors
x0 = step-divisor-init 30

x1 : PrimeDivisors
x1 = step-divisor x0

x2 : PrimeDivisors
x2 = step-divisor x1

-- PrimeDivisors.quotient x2 = 5
-- PrimeDivisors.divisors x2 = 3 :: 2 :: []


x3 : PrimeDivisors
x3 = step-divisor x2


f : ℕ → List ℕ
f n =
  PrimeDivisors.divisors pd where
    pd = step-divisor (step-divisor-init 12)

prime-divisors-aux : ℕ → PrimeDivisors → PrimeDivisors
prime-divisors-aux 0 pd = pd
prime-divisors-aux (suc n) pd =
  if PrimeDivisors.quotient pd =ℕ 1 then pd
  else prime-divisors-aux n pd' where
    pd' = step-divisor pd

prime-divisors : ℕ → List ℕ
prime-divisors n =
  PrimeDivisors.divisors pd where
    pd = prime-divisors-aux n (step-divisor-init n)
   
  
