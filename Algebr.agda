module Algebr where

open import PropositionalEquality
open import TypeConstructions

IsSemiGroup : (S : Set) → (S → S → S) → Set
IsSemiGroup S op = (x y z : S) → (op x (op y z)) == (op (op x y) z)

IsMonoid : (S : Set) → (S → S → S) → Set
IsMonoid S op = IsSemiGroup S op × (S Σ λ (e : S) -> (n : S) → op n e == n × op e n == n)


