-- import Relation.Binary.PropositionalEquality

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



-- Equality and its properties

infix 4 _≡_
data _≡_ { A : Set } (a : A) : A → Set where
  refl : a ≡ a

sym : ∀ {A : Set} {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : ∀ { A : Set } { a b c : A } → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

cong : {A B : Set} (f : A → B) { x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

eq : {A : Set} -> (a b c : A) -> (p : a ≡ b) -> (q : b ≡ c) -> a ≡ c
eq {A} a b c refl refl = refl


infixr 3 _∙_
_∙_ : {A : Set} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
p ∙ q = trans p q



-- Some proofs

suc-apply : (a b : ℕ) -> suc a + b ≡ suc (a + b)
suc-apply a b  = refl

left-zero : (a : ℕ) → 0 + a ≡ a
left-zero a = refl


right-zero : (a : ℕ) → a + 0 ≡ a
right-zero 0 = refl
right-zero (suc a) = cong suc (right-zero a)

lr-add-zero : (a : ℕ) → 0 + a ≡ a + 0
lr-add-zero a = trans (left-zero a) (sym (right-zero a))

right-suc : (a b : ℕ) → a + suc b ≡ suc (a + b)
right-suc zero b = left-zero (suc b) ∙ cong suc (sym (left-zero b))
right-suc (suc a) b = g ∙ f where
   f = cong suc (sym (suc-apply a b))
   g = (cong suc (right-suc a b))


assoc-plus : (a b c : ℕ) -> (a + b) + c ≡ a + (b + c)
assoc-plus 0 b c = refl
assoc-plus (suc a) b c = cong suc (assoc-plus a b c)

comm-plus : (a b : ℕ) → a + b ≡ b + a
comm-plus zero b = lr-add-zero b
comm-plus (suc a) zero = trans (right-zero (suc a)) (left-zero (suc a))
comm-plus (suc a) (suc b) =  f₁ ∙ f₂ ∙ f₃ where
  f₁ = suc-apply a (suc b)             -- suc a + suc b ≡ suc (a + suc b)
  f₂ = cong suc (comm-plus a (suc b))  -- 
  f₃ = sym (right-suc (suc b) a)       --
   

mult-zero : (a : ℕ) → 0 * a ≡ 0
mult-zero a = refl

mult-one : (a : ℕ) → a * 1 ≡ a
mult-one 0 = refl
mult-one (suc a) = cong suc (mult-one a) 



