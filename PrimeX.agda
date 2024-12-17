module PrimeX where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc; _*_; _+_; _<_; _≤_; _>_; _<ᵇ_; _≡ᵇ_; s≤s)
open import Data.Nat.Properties using (<-trans; <-irrefl; n≮n; <-asym)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat.DivMod using (_mod_)
open import Data.Fin.Base using (Fin; toℕ)

data _∣_ : ℕ → ℕ → Set where
  divides : ∀ m n k → m * k ≡ n → m ∣ n

data Prime (n : ℕ) : Set where
  prime : 
    (n>1 : 1 < n) →
    (∀ (m : ℕ) → m ∣ n → (m ≡ 1) ⊎ (m ≡ n)) →
    Prime n

infix 4 _>ᵇ_
_>ᵇ_ : ℕ → ℕ → Bool
m >ᵇ n = n <ᵇ m

remainder : ℕ → (d : ℕ) → ℕ
remainder n zero = zero
remainder n (suc d) = toℕ (n mod (suc d))

is-prime? : ℕ → Bool
is-prime? zero = false
is-prime? (suc zero) = false
is-prime? n = go n n 2
  where
    go : ℕ → ℕ → ℕ → Bool
    go _ zero _ = true
    go n' (suc fuel) d with d * d >ᵇ n'
    ... | true = true
    ... | false with remainder n' d ≡ᵇ 0
    ...   | true = false
    ...   | false = if (n' <ᵇ d)
                    then true
                    else go n' fuel (suc d)

prodPrimesUpTo : ℕ → ℕ
prodPrimesUpTo zero = 1
prodPrimesUpTo (suc n) with is-prime? (suc n)
... | true  = suc n * prodPrimesUpTo n
... | false = prodPrimesUpTo n

M : ℕ → ℕ
M n = prodPrimesUpTo n + 1

2≰0 : ¬ (2 ≤ 0)
2≰0 ()

2≰1 : ¬ (2 ≤ 1)
2≰1 (s≤s ())

lemmaPrimeDivisor : ∀ n → (1 < n) → Σ ℕ (λ p → Prime p × p ∣ n)
lemmaPrimeDivisor zero p = ⊥-elim (2≰0 p)
lemmaPrimeDivisor (suc zero) p = ⊥-elim (2≰1 p)
lemmaPrimeDivisor (suc (suc n)) p = {!   !}
