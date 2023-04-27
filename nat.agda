
data ℕ : Set where
     zero : ℕ
     suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

infixr 10 _+_
_+_ : ℕ → ℕ → ℕ
0 + b = b
suc a + b = suc (a + b)

infix 20 _*_
_*_ : ℕ → ℕ → ℕ
0 * b = 0
(suc a) * b = b + a * b



-- Some proofs

infix 4 _≡_
data _≡_ { A : Set } (a : A) : A → Set where
  refl : a ≡ a

cong : {A B : Set} (f : A → B) { x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

mult-zero : (a : ℕ) → 0 * a ≡ 0
mult-zero a = refl

mult-one : (a : ℕ) → a * 1 ≡ a
mult-one 0 = refl
mult-one (suc a) = cong suc (mult-one a) 



