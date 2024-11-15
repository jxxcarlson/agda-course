module InfinitePrimes where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _≥_;_<_; _≟_; _>_;pred)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-antisym)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Data.List using (List; []; _∷_; filter; foldr)

open import Data.Product using (_×_; ∃; ∃-syntax; Σ) 
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-antisym) 
open import Relation.Nullary using (¬_; yes; no) 
open import Data.Nat.Divisibility using (_∣_)
open import Data.Sum using (_⊎_)


-- Primality definition
divides : ℕ → ℕ → Set
divides m n = ∃[ k ] (k * m ≡ n)

-- Agda was trying to use ℕ as a sort (type universe) when it should be used as a type.

isPrime : ℕ → Set
isPrime n = (n > 1) × ((m : ℕ) → divides m n → (m ≡ 1) ⊎ (m ≡ n))

product : List ℕ → ℕ
product = foldr _*_ 1

-- Theorem: There are infinitely many primes
infinitePrimes : (n : ℕ) → Σ ℕ (λ p → (p > n) × isPrime p)
infinitePrimes n = {!!}

-- This explicitly tells Agda that we're looking for a natural number p that satisfies our conditions. The Σ type constructor takes two arguments:
-- The type of the value we're looking for (ℕ in this case)
-- A predicate over that type (λ p → (p > n) × isPrime p)

