module List where

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

_+_ : {A : Set} → List A → List A → List A
[] + L2 = L2
(l1 ∷ L1) + L2 = l1 ∷ (L1 + L2)

{- Wie löst man hier das head-Problem?
head : {A : Set} → List A → A
head (l ∷ L) = l -}

tail : {A : Set} → List A → List A
tail [] = []
tail (l ∷ L) = L

mirror : {A : Set} → List A → List A
mirror [] = []
mirror (l ∷ L) = (mirror L) + (l ∷ [])
