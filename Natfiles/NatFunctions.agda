module Natfiles.NatFunctions where

open import Natfiles.NatDataDef

open import PropositionalEquality

open import Bool

open import Natfiles.NatSizelessFunctions public

open import Natfiles.NatSizeComparison





{- Addition und Beweise -}

{- Definition Addition -}
_+_ : ℕ → ℕ → ℕ
n + Zero = n
n + (Suc m) = Suc (n + m)

infix 5 _+_

{- Die folgenden beiden Beweise sichern, dass wir die Rekursion auch nach der ersten Komponente führen können -}
ZeroPlusNisN : (n : ℕ) → ((Zero + n) == n)
ZeroPlusNisN Zero  = Refl
ZeroPlusNisN (Suc n) = app Suc (ZeroPlusNisN n)

SucNPlusMisSucNPlusM : (n m : ℕ) → (((Suc n) + m) == (Suc (n + m)))
SucNPlusMisSucNPlusM n Zero    = Refl
SucNPlusMisSucNPlusM n (Suc m) = app Suc (SucNPlusMisSucNPlusM n m)





{- Subtraktion und Beweise -}

{- Definition Subtraktion -}
_-_ : ℕ → ℕ → ℕ
n - Zero = n
Zero - m = Zero
(Suc n) - (Suc m) = n - m

infix 5 _-_

{- Beweis, dass für n ≤ m gilt, dass n + (m - n) == m -}
MinusIsInvers : (n m : ℕ) → ((n ≤ m) == True) -> ((n + ( m - n)) == m)
MinusIsInvers Zero m _ = ZeroPlusNisN m -- Zero + (m - Zero) = Zero + m == m
MinusIsInvers (Suc n) Zero () -- Suc n ≤ Zero = False Verschiedene Konstruktoren 
                              -- stimmen aber nie überein, so dass von () den Rest regelt. 
MinusIsInvers (Suc n) (Suc m) p = 
   ==trans  (SucNPlusMisSucNPlusM n (m - n)) -- n' + (m' - n') == (n + (m - n))' 
            (app Suc (MinusIsInvers n m p))  --                == m'





{- Multiplikation -}

{- Definition der Multiplikation -}
_*_ : ℕ → ℕ → ℕ
n * Zero = Zero
n * (Suc m) = (n * m) + n

infix 6 _*_





{- Division -}

{- Definition der Division -}
_div_ :  ℕ → ℕ → ℕ
Zero div _ = Zero
(Suc n) div m = if (decTo𝔹(decEqℕ ((n div m) * m + m) (Suc n)))
    then Suc (n div m)
    else (n div m)

infix 6 _div_

{- Definition der Restfunktion -}
_remainder_ : ℕ → ℕ → ℕ
n remainder m = n - ((n div m) * m) 





{- Potenz -}

{- Definition der Potenz -}
_^_ : ℕ → ℕ → ℕ
n ^ Zero = Suc Zero
n ^ (Suc m) = (n ^ m) * n

infix 7 _^_


