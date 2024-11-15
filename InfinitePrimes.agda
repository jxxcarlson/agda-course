module InfinitePrimes where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _≥_;_<_; _≟_; _>_;pred; _∸_; NonZero)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-antisym; _≤?_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans)
open import Data.List using (List; []; _∷_; foldr; all; filter)

open import Data.Product using (_×_; ∃; ∃-syntax; Σ) 
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-antisym) 
open import Relation.Nullary using (¬_; yes; no; Dec; ⌊_⌋)
open import Data.Nat.Divisibility using (_∣_)
open import Data.Sum using (_⊎_)

open import Data.Bool using (Bool; true; false; not)
open import Data.Nat.DivMod using (_mod_)
open import Data.Fin using (Fin; toℕ) 
open import Function using (_∘_) 


-- ßPrimality definition
divides : ℕ → ℕ → Set
divides m n = ∃[ k ] (k * m ≡ n)

-- Agda was trying to use ℕ as a sort (type universe) when it should be used as a type.



product : List ℕ → ℕ
product = foldr _*_ 1

-- Helper functions

-- generates a list of numbers from m   
{-# TERMINATING #-}  -- Add this pragma for fromTo
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




-- This explicitly tells Agda that we're looking for a natural number p that satisfies our conditions. The Σ type constructor takes two arguments:
-- The type of the value we're looking for (ℕ in this case)
-- A predicate over that type (λ p → (p > n) × isPrime p)

