data ℕ : Set where
     zero : ℕ
     suc : ℕ → ℕ

-- 1.
-- Try C-c C-n 'suc (suc zero)`
-- You have evaluate the number two

-- 2,
-- Uncomment the line below to use the conventional notation for nautral numbers
{-# BUILTIN NATURAL ℕ #-}


-- 3.
-- Try C-c -C-n 'suc (suc zero)' again.
-- Now try C-c C-n 7 RET
-- You can evaluate natural numbers written as '2' instead of `'suc (suc zero)'

-- 4.
-- Addition:
infixr 10 _+_ 
_+_ : ℕ → ℕ → ℕ
0 + n = n
suc m + n = suc (m + n)

-- 5.
-- Multiplication
-- Calculate 2 + 3 * 7 to check
-- Note the whitespace around + and *
infixr 20 _*_
_*_ : ℕ → ℕ → ℕ
0 * n = 0
suc m * n = n + m * n


--6. The identity type
infix 4 _≡_
data _≡_ { A : Set } (a : A) : A → Set where
  refl : a ≡ a
  
-- 7. The symmetry property is a theorem
sym : ∀ {A : Set} {a b : A} → a ≡ b → b ≡ a
sym refl = refl

-- 8. The transitive property is also a theorem
trans : ∀ { A : Set } { a b c : A } → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

-- 7. Congruence: function application respects the identity type
cong : {A B : Set} (f : A → B) { x y : A} → 
       x ≡ y → f x ≡ f y
cong f refl = refl



-- Some proofs


-- 8. 0 is a left-identity
-- The  proof is elmentary, becuase the propsition is inhabited by the function 'relf'.
-- It worls because 0 + a and a are definitionally equal. That is
-- both 0 + a and a reduce to the same thing via the rules
-- used to define ℕ.
left-zero : (a : ℕ) → 0 + a ≡ a
left-zero a = refl

-- 9. 0 is a right-identity
-- The proof is by induction. Induction requires the congruence principle
-- proved above.
--right-zero : (a : ℕ) → a + 0 ≡ a
right-zero : ∀ a → a + 0 ≡ a
right-zero 0 = refl
right-zero (suc a) = cong suc (right-zero a)


-- Associativity of addition
assoc-plus : ∀ a b c → a + (b + c) ≡ (a + b) + c
assoc-plus  zero b c = refl
assoc-plus (suc a) b c = cong suc (assoc-plus a b c)

-- Lemma to prove that addition is commutative
comm-add-zero : ∀ a  → 0 + a ≡ a + 0
comm-add-zero a = trans (left-zero a) (sym (right-zero a))


-- Lemma: suc (m + n) ≡ m + suc n
add-suc : ∀ m n → suc (m + n) ≡ m + suc n
add-suc zero n = refl
add-suc (suc m) n = cong suc (add-suc m n)






