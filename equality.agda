module Equality where



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
  → u ≡ x → v ≡ y → f u v ≡ f x y
cong₂ f refl refl = refl


cong-app : ∀ {A B : Set} {f g : A → B}
  → f ≡ g
    ---------------------
  → ∀ (x : A) → f x ≡ g x
cong-app refl x = refl


subst : ∀ {A : Set} {x y : A} (P : A → Set)
  → x ≡ y
    ---------
  → P x → P y
subst P refl px = px

eq : {A : Set} -> (a b c : A) -> (p : a ≡ b) -> (q : b ≡ c) -> a ≡ c
eq {A} a b c refl refl = refl


infixr 3 _∙_
_∙_ : {A : Set} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
p ∙ q = trans p q
