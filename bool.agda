data Bool : Set where
  true : Bool
  false : Bool
  
¬_ : Bool → Bool
¬ true = false
¬ false = true

infixl 20 _∧_
_∧_ : Bool → Bool → Bool
true ∧ true = true
_ ∧ _  = false

infix 10 _∨_
_∨_ : Bool → Bool → Bool
false ∨ false = false
_ ∨ _ = true

or' : Bool → Bool → Bool
or' false false = false
or' _ _ = true

-- Some proofs

infix 4 _≡_
data _≡_ { A : Set } (a : A) : A → Set where
  refl : a ≡ a
  
doublenegation : (a : Bool) → ¬ ¬ a ≡ a
doublenegation true = refl
doublenegation false = refl

not-and : (a b : Bool) → ¬ (a ∧ b) ≡ ¬ a ∨ ¬ b
not-and true true = refl
not-and true false = refl
not-and false true = refl
not-and false false = refl

-- C-c C-f
-- or-assoc : (a b c : Bool) -> (a ∨ b) ∨ c ≡ a ∨ (b ∨ c)
-- or-assoc true b c = refl
-- or-assoc false b c = {!!}




-- C-c C-a -- find proof
an-implication : { A B C : Set } → (B → C) → (A → B) → A → C
an-implication g f x = g (f x)

-- C-c C-a
modus-ponens : { P Q : Set } → (P → Q) → P → Q
modus-ponens f p = f p

or : Bool -> Bool -> Bool
or a true = true
or a false = a

comm-or : (a b : Bool) -> a ∨ b ≡ b ∨ a
comm-or true true = refl
comm-or true false = refl
comm-or false true = refl
comm-or false false = refl
