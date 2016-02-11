module Yoneda where

open import TypeConstructions
open import PropositionalEquality


SetFunctorOn : Set → Set
SetFunctorOn A = A → Set

{- natural transformations between Setfunctors -}

{-
NTFBetween : {A : Set} → (F G : SetFunctorOn A) → Set
NTFBetween F G = (Π ) Σ (λ σ
-}
