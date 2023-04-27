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
