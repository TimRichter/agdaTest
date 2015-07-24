module NatDisplay where

open import Nat

{- Funktionen zur Darstellung von ℕ -}

data Digit : Set where
  0- : Digit
  1- : Digit
  2- : Digit
  3- : Digit
  4- : Digit
  5- : Digit
  6- : Digit
  7- : Digit
  8- : Digit
  9- : Digit

ℕToDigit : ℕ → Digit
ℕToDigit Zero = 0-
ℕToDigit (Suc Zero) = 1-
ℕToDigit (Suc (Suc Zero)) = 2-
ℕToDigit (Suc (Suc (Suc Zero))) = 3-
ℕToDigit (Suc (Suc (Suc (Suc Zero)))) = 4-
ℕToDigit (Suc (Suc (Suc (Suc (Suc Zero))))) = 5-
ℕToDigit (Suc (Suc (Suc (Suc (Suc (Suc Zero)))))) = 6-
ℕToDigit (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero))))))) = 7-
ℕToDigit (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero)))))))) = 8-
ℕToDigit (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero))))))))) = 9-
ℕToDigit (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc n)))))))))) = ℕToDigit n

DigitToℕ : Digit → ℕ
DigitToℕ 0- = Zero
DigitToℕ 1- = Suc Zero
DigitToℕ 2- = Suc (Suc Zero)
DigitToℕ 3- = Suc (Suc (Suc Zero))
DigitToℕ 4- = Suc (Suc (Suc (Suc Zero)))
DigitToℕ 5- = Suc (Suc (Suc (Suc (Suc Zero))))
DigitToℕ 6- = Suc (Suc (Suc (Suc (Suc (Suc Zero)))))
DigitToℕ 7- = Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero))))))
DigitToℕ 8- = Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero)))))))
DigitToℕ 9- = Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero))))))))
