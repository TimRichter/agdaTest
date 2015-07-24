module Natfiles.NatSizelessFunctions where

open import Natfiles.NatDataDef

{- Die Vorgängerfunktion, die als Vorgänger von 0 die 0 nimmt -}
pred : ℕ → ℕ
pred Zero = Zero
pred (Suc n) = n

constzero : ℕ → ℕ
constzero Zero = Zero
constzero(Suc n) = Zero

negInNat : ℕ → ℕ
negInNat Zero = Suc Zero
negInNat n = Zero

double : ℕ → ℕ
double Zero = Zero
double(Suc n) = Suc(Suc(double n))

{- functionLeftShift(f) soll eine Funktion f' liefern mit f'(n)=f(n+1) -}

functionLeftShift : (ℕ → ℕ) → (ℕ → ℕ)
functionLeftShift f = f' where
  f' : ℕ → ℕ
  f' n = f (Suc n)

{- functionChangeEntry(i,n,f) soll eine Funktion f' liefern, so dass f'(j)=f(j) für j ≠ i und f'(i)=n 
   Zu beachten ist, dass g : ℕ → ℕ nochmals angegeben werden muss. -}

functionChangeEntry : ℕ → ℕ → (ℕ → ℕ) → (ℕ → ℕ)
functionChangeEntry Zero n f = f' where
  f' : ℕ → ℕ
  f' Zero = n
  f' (Suc m) = f (Suc m)
functionChangeEntry (Suc i) n f = f'' where
  f'' : ℕ → ℕ
  f'' Zero = f Zero
  f'' (Suc j) = functionChangeEntry i n (functionLeftShift f) j

