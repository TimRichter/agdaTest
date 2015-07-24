module PropositionalEquality where

open import TypeConstructions public
-- open import Sub.TypeConstructions public

data _==_ {A : Set} (x : A) : A → Set where
  Refl : x == x

infix 4 _==_

==sym : {A : Set} → {x y : A} → (x == y) → (y == x)
==sym Refl = Refl

==trans : {A : Set} → {x y z : A}  → (x == y) → (y == z) → (x == z)
==trans Refl Refl = Refl

app : {A B : Set} → (f : A -> B) → {x y : A} → (x == y) → (f x == f y)
app f Refl = Refl

