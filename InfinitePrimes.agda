module InfinitePrimes where


open import Data.List using (List; []; _∷_; foldr; all; filter)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _≥_;_<_; _≟_; _>_;pred; _∸_; NonZero)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-antisym; _≤?_; +-comm; *-comm)
open import Data.Nat.Divisibility using (_∣_)
open import Data.Sum using (_⊎_)
open import Data.Bool using (Bool; true; false; not)
open import Data.Nat.DivMod using (_mod_)
open import Data.Fin using (Fin; toℕ) 
open import Data.Empty using (⊥) 
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; _,_) 
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-antisym) 

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong) 
open import Relation.Nullary using (¬_; yes; no; Dec; ⌊_⌋)

open import Function using (_∘_) 


-- Primality definition
divides : ℕ → ℕ → Set
divides m n = ∃[ k ] (k * m ≡ n)

-- Agda was trying to use ℕ as a sort (type universe) when it should be used as a type.


product : List ℕ → ℕ
product = foldr _*_ 1

-- Helper functions

  
{-# TERMINATING #-}  -- Add this pragma for fromTo

-- generates a list of numbers from m 
fromTo : ℕ → ℕ → List ℕ
fromTo m n with m ≤? n
... | yes m≤n = m ∷ fromTo (suc m) n
... | no _ = []

isPrime' : ℕ → Bool
isPrime' n with n ≤? 1
... | yes _ = false
... | no n≥2 = all checkDivisor (fromTo 2 (n ∸ 1))
  where
    checkDivisor : ℕ → Bool
    checkDivisor zero = true  -- This case shouldn't occur as we start from 2
    checkDivisor (suc m) = not ⌊ toℕ (n mod (suc m)) ≟ 0 ⌋

isPrime? : ∀ n → Dec (isPrime' n ≡ true)
isPrime? n with isPrime' n
... | true = yes refl
... | false = no λ()


-- gives a list of prime numbers up to n.
primesUpTo : ℕ → List ℕ
primesUpTo n = filter (λ x → isPrime? x) (fromTo 2 n)


-- First, let's make sure we have isPrime defined properly
isPrime : ℕ → Set
isPrime n = (n > 1) × ((m : ℕ) → divides m n → (m ≡ 1) ⊎ (m ≡ n))

-- Helper function to compute N
bigN : ℕ → ℕ
bigN n = suc (product (primesUpTo n))


-- Helper lemma: if a divides N = (product of primes up to n) + 1, 
-- then a cannot be in our list of primes
divide-not-in-list : ∀ (n a : ℕ) → 
  (a ∣ bigN n) → a ≢ 1 → a ≤ n → isPrime a → ⊥
divide-not-in-list n a = {!!}  

--Theorem: There are infinitely many primes
infinitePrimes : (n : ℕ) → Σ ℕ (λ p → (p > n) × isPrime p)
infinitePrimes n = {!!}


-- This explicitly tells Agda that we're looking for a natural number p that csatisfies our conditions. The Σ type constructor takes two arguments:
-- The type of the value we're looking for (ℕ in this case)
-- A predicate over that type (λ p → (p > n) × isPrime p)

