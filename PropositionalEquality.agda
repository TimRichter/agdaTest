module PropositionalEquality where

open import TypeConstructions public

data _==_ {A : Set} (x : A) : A → Set where
  Refl : x == x

infix 4 _==_

_==⟨_⟩_ : {A : Set} → (x : A) → {y z : A} → x == y → y == z → x == z
x ==⟨ Refl ⟩ Refl = Refl

infixr 2 _==⟨_⟩_

_qed : {A : Set} → (x : A) → x == x
x qed = Refl

infixr 2 _qed

bydef : {A : Set} → {x : A} → x == x
bydef = Refl

sym== : {A : Set} → {x y : A} → (x == y) → (y == x)
sym== Refl = Refl

trans== : {A : Set} → {x y z : A}  → (x == y) → (y == z) → (x == z)
trans== Refl Refl = Refl

app : {A B : Set} → (f : A -> B) → {x y : A} → (x == y) → (f x == f y)
app f Refl = Refl

transp : {A : Set} → (B : A → Set) → {x y : A} → x == y → B x → B y
transp B {x} {.x} Refl pr[Bx] = pr[Bx]
