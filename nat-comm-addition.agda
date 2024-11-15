open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

data ℕ : Set where
     zero : ℕ
     suc : ℕ → ℕ


{-# BUILTIN NATURAL ℕ #-}

-- 1. Define addition in ℕ 

infixr 10 _+_ 
_+_ : ℕ → ℕ → ℕ
0 + n = n
suc m + n = suc (m + n)

-- 2. Define multiplication in ℕ

infixr 20 _*_
_*_ : ℕ → ℕ → ℕ
0 * n = 0
suc m * n = n + m * n


-- Some proofs. 

-- This time we import the code needed to define the identity type,
-- the symmetry property, the transitivity property, and the congruence principle.
-- In addition, we import code for "equational reasoning", which is a convenient
-- way of chaining equalities together.


-- Lemma 1: 0 is a left-identity
-- The  proof is elementary, because the propsition is inhabited by the function 'relf'.
-- It works because 0 + a and a are definitionally equal. That is
-- both 0 + a and a reduce to the same thing via the rules  used to define ℕ.

-- ∀ a → 0 + a ≡ a
left-zero : (a : ℕ) → 0 + a ≡ a
left-zero a = refl

-- Lemma 2: 0 is a right-identity
-- The proof is by induction. Induction requires the congruence principle.

-- ∀ a → a + 0 ≡ a
right-zero : ∀ a → a + 0 ≡ a
right-zero 0 = refl
right-zero (suc a) = cong suc (right-zero a)


-- Lemma 3: Addition is associative

-- ∀ a b c → a + (b + c) ≡ (a + b) + c
assoc-plus : ∀ a b c → a + (b + c) ≡ (a + b) + c
assoc-plus  zero b c = refl
assoc-plus (suc a) b c = cong suc (assoc-plus a b c)


-- Lemma 4. Special case of commutativity of addition

-- ∀ a  → 0 + a ≡ a + 0
comm-add-zero : ∀ a  → 0 + a ≡ a + 0
comm-add-zero a = trans (left-zero a) (sym (right-zero a))


-- Lemma 5: addition is right-distributive over successor

-- ∀ m n → suc (m + n) ≡ m + suc n
add-suc : ∀ m n → suc (m + n) ≡ m + suc n
add-suc zero n = refl
add-suc (suc m) n = cong suc (add-suc m n)


 
-- Proposition: Addition is commutative
-- The proof is by induction on the first argument.
-- Equational reasoning is used to chain equalities together
-- The chain begins with 'comm-plus (suc m) n' and ends with '(n + suc m)'
-- thereby completing the induction step. 

-- ∀ m n → m + n ≡ n + m
comm-plus : ∀ m n → m + n ≡ n + m
comm-plus zero n = comm-add-zero n
comm-plus (suc m) n = begin
  (suc m + n)
    ≡⟨ refl ⟩
  (suc (m + n))
    ≡⟨ cong suc (comm-plus m n) ⟩
  (suc (n + m))
    ≡⟨ add-suc n m ⟩
  (n + suc m)
  ∎

