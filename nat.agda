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

cong₂ : ∀ {A B C : Set} (f : A → B → C) {u x : A} {v y : B}
  → u ≡ x
  → v ≡ y
    -------------
  → f u v ≡ f x y
cong₂ f refl refl  =  refl

cong-app : ∀ {A B : Set} {f g : A → B}
  → f ≡ g
    ---------------------
  → ∀ (x : A) → f x ≡ g x
cong-app refl x = refl


eq : {A : Set} -> (a b c : A) -> (p : a ≡ b) -> (q : b ≡ c) -> a ≡ c
eq {A} a b c refl refl = refl


infixr 3 _∙_
_∙_ : {A : Set} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
p ∙ q = trans p q




-- Some proofs

-- Addition

left-zero : (a : ℕ) → 0 + a ≡ a
left-zero a = refl

right-zero : (a : ℕ) → a + 0 ≡ a
right-zero 0 = refl
right-zero (suc a) = cong suc (right-zero a)

lr-add-zero : (a : ℕ) → 0 + a ≡ a + 0
lr-add-zero a = trans (left-zero a) (sym (right-zero a))

suc-add-left : (a b : ℕ) -> suc a + b ≡ suc (a + b)
suc-add-left a b  = refl

suc-add-right : (a b : ℕ) → a + suc b ≡ suc (a + b)
suc-add-right zero b = left-zero (suc b) ∙ cong suc (sym (left-zero b))
suc-add-right (suc a) b = g ∙ f where
   f = cong suc (sym (suc-add-left a b))
   g = (cong suc (suc-add-right a b))

assoc-plus : (a b c : ℕ) -> (a + b) + c ≡ a + (b + c)
assoc-plus 0 b c = refl
assoc-plus (suc a) b c = cong suc (assoc-plus a b c)

comm-plus : (a b : ℕ) → a + b ≡ b + a
comm-plus zero b = lr-add-zero b
comm-plus (suc a) zero = right-zero (suc a) ∙ left-zero (suc a)
comm-plus (suc a) (suc b) =  f₁ ∙ f₂ ∙ f₃ where
  f₁ = suc-add-left a (suc b)             -- suc a + suc b ≡ suc (a + suc b)
  f₂ = cong suc (comm-plus a (suc b))  -- 
  f₃ = sym (suc-add-right (suc b) a)       --
   

-- Multplication

mult-zero : (a : ℕ) → 0 * a ≡ 0
mult-zero a = refl

suc-mul-left : (a b : ℕ) → (suc a) * b ≡ b + a * b
suc-mul-left zero b = refl
suc-mul-left (suc a) b = {!!} where
  f₁ = cong suc (suc-mul-left a b)
  f₂ = sym (suc-add-right b (a * b))

suc-mul-right : (a b : ℕ) → a * (suc b) ≡ a + a * b
suc-mul-right zero b = refl
suc-mul-right (suc a) b = {!!}


identity-right : (a : ℕ) → a * (suc zero) ≡ a
identity-right 0 = refl
identity-right (suc a) = cong suc (identity-right a)

identity-left : (a : ℕ) → (suc zero) * a ≡ a
identity-left zero = refl
identity-left (suc a) = {!? !}

plus : ℕ → ℕ → ℕ
plus a x = a + x

f : ℕ → ℕ
f = plus 2


dist : (a b c : ℕ) → a * (b + c) ≡ a * b + a * c
dist zero b c = refl
dist (suc a) b c = {!!} where
  f₁ = cong (plus (b + c)) (dist a b c)


-- Recursive functions

double : ℕ → ℕ
double zero = zero
double (suc n) = suc (suc (double n))




check-double : (a : ℕ) → double a ≡ 2 * a
check-double zero = refl
check-double (suc a) = cong suc2 (check-double a) ∙ {!!}  where
   suc2 : ℕ → ℕ
   suc2 a = suc (suc a)
   
