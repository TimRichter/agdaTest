module Parametrized where
  --open import Nat
  open import Main
  open Main.Nat
  open import Data.Bool
  open import Data.List

  module Sort (A : Set)(_≤_ : A → A → Bool) where
   insert : A → List A → List A
   insert x  [] = (x ∷ [])
   insert x (y ∷ ys) with x ≤ y
   insert x (y ∷ ys)    | true  = x ∷ y ∷ ys
   insert x (y ∷ ys)    | false = y ∷ insert x ys

   sort : List A → List A
   sort []         = []
   sort (x ∷ xs) = insert x (sort xs)
