

-- The boolean type
data Bool : Set where
  true : Bool
  false : Bool

-- Operators

-- Negation
¬_ : Bool → Bool
¬ true = false
¬ false = true

-- Conjunction
infixl 20 _∧_
_∧_ : Bool → Bool → Bool
true ∧ true = true
_ ∧ _  = false

-- Disjunction
infix 10 _∨_
_∨_ : Bool → Bool → Bool
false ∨ false = false
_ ∨ _ = true

-- Also disjunction
or' : Bool → Bool → Bool
or' false false = false
or' _ _ = true

-- Some proofs

-- For the proofs we need equality as a type
-- Its sole constructor is 'refl'
infix 4 _≡_
data _≡_ { A : Set } (a : A) : A → Set where
  refl : a ≡ a


-- Double negation
doublenegation : (a : Bool) → ¬ ¬ a ≡ a
doublenegation true = refl
doublenegation false = refl

not-and : (a b : Bool) → ¬ (a ∧ b) ≡ ¬ a ∨ ¬ b
not-and true true = refl
not-and true false = refl
not-and false true = refl
not-and false false = refl

or-assoc : (a b c : Bool) -> (a ∨ b) ∨ c ≡ a ∨ (b ∨ c)
or-assoc true b c = refl
or-assoc false true c = refl
or-assoc false false true = refl
or-assoc false false false = refl

an-implication : { A B C : Set } → (B → C) → (A → B) → A → C
an-implication g f x = g (f x)

modus-ponens : { P Q : Set } → (P → Q) → P → Q
modus-ponens {P} {Q} f p = f p

or : Bool -> Bool -> Bool
or a true = true
or a false = a

comm-or : (a b : Bool) -> a ∨ b ≡ b ∨ a
comm-or true true = refl
comm-or true false = refl
comm-or false true = refl
comm-or false false = refl
