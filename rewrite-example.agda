{-# OPTIONS --without-K --safe #-}

{-

 Agda’s rewrite rule is a feature that allows for equational reasoning in proofs. 
 It provides a mechanism to rewrite expressions using specified equalities in a 
 localized manner, making proofs more concise and readable.

1.	Declare an Equality: 

The rewrite rule operates on an equality  e : a ≡ b , where  ≡  is the equality type 
in Agda. This equality could be proven within the current context or imported from elsewhere.

2. Use the rewrite Keyword: 

The rewrite keyword is used within a function or proof to indicate that the current 
goal or an expression should be rewritten using the given equality.  When invoked, 
Agda substitutes occurrences of  a  with  b  (or vice versa) in the goal or relevant 
expressions.

3.	Effect:

After applying rewrite e, Agda transforms the current goal or expression by replacing 
terms according to the equality  e . The proof or computation then continues with 
the rewritten goal.

-- Example: Prove that if x ≡ y and y ≡ z, then x ≡ z
transitivity : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
transitivity eq1 eq2 = 
  rewrite eq1
  rewrite eq2
  refl

Here’s what happens:

	1.	After rewrite eq1, the goal changes from  x ≡ z  to  y ≡ z , because  x  is rewritten to  y .
	
  2.	After rewrite eq2, the goal  y ≡ z  becomes trivial, and refl completes the proof.

  https://www.math.fsu.edu/~ealdrov/teaching/2020-21/fall/MAS5932/agda/simplethms-1.html#587

-}


infix 4 _≡_  
data _≡_ {A : Set} (x : A) : A → Set  where
  instance refl : x ≡ x

sym : ∀ {A : Set} {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : ∀ { A : Set } { a b c : A } → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

cong : {A B : Set} (f : A → B) { x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {A B C : Set} (f : A → B → C) {u x : A} {v y : B}
  → u ≡ x
  → v ≡ y
    -------------
  → f u v ≡ f x y
cong₂ f refl refl  =  refl


{-# BUILTIN EQUALITY _≡_ #-}

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero + m = m
suc n + m = suc (n + m)

_*_ : ℕ → ℕ → ℕ
zero * m = zero
suc n * m = m + (n * m)

+0 : ∀ (m : ℕ) → m + zero ≡ m
+0 zero = refl
+0 (suc m) rewrite +0 m = refl

+suc : ∀ (m n : ℕ) → m + suc n ≡ suc m + n
+suc zero n rewrite +0 n = refl
+suc (suc m) n rewrite +suc m n = refl


f : (m n : ℕ) → suc (m + n) ≡ m + suc n
f zero n rewrite +0 n = refl
f (suc m) n rewrite +suc m n | f m n = refl

is-comm+ : ∀ (m n : ℕ) → m + n ≡ n + m
is-comm+ zero n rewrite (+0 n) = refl 
is-comm+ (suc m) n rewrite +suc m n | is-comm+ m n | f n m  = refl



foo : (m n : ℕ) → suc m + n ≡ (suc m) + n
foo m n = refl
 