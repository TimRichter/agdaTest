module Natfiles.NatSizeComparison where

open import Natfiles.NatDataDef

open import PropositionalEquality

open import Bool

open import Natfiles.NatSizelessFunctions

{- Gleichheit in ℕ ist entscheidbar: Die Funktion liefert für jedes Paar n,m eine Entscheidung und Beweis bzw. eine Widerlegung von n == m -}
decEqℕ : (n m : ℕ) → Dec (n == m)
decEqℕ Zero Zero = Yes Refl
decEqℕ (Suc n) Zero = No f where
  f : {n : ℕ} -> ((Suc n) == Zero) → ⊥
  f ()
decEqℕ Zero (Suc m) = No f where
  f : {m : ℕ} -> (Zero == (Suc m)) → ⊥
  f ()
decEqℕ (Suc n) (Suc m) with (decEqℕ n m)
decEqℕ (Suc n) (Suc m) | (Yes nEqm)  = Yes (app Suc nEqm)
decEqℕ (Suc n) (Suc m) | (No  ¬nEqm) = No (¬nEqm ∘ f) where
               f : (Suc n == Suc m) → (n == m)
               f snEqsm = (app pred snEqsm)

{- Die Größenrelationen auf ℕ -}

_==ℕ_ : ℕ → ℕ → 𝔹 
Zero ==ℕ Zero = True
(Suc n) ==ℕ Zero = False
Zero ==ℕ (Suc m) = False
(Suc n) ==ℕ (Suc m) = n ==ℕ m

leibnizid==ℕ : (A : ℕ → Set) → (n m : ℕ) → ((n ==ℕ m) == True) → A n → A m
leibnizid==ℕ _ Zero Zero _ q = q
leibnizid==ℕ _ Zero (Suc m) () _
leibnizid==ℕ _ (Suc n) Zero () _
leibnizid==ℕ A (Suc n) (Suc m) p q = leibnizid==ℕ B n m p q where
  B : ℕ → Set
  B n = A (Suc n)

_≤_ : ℕ → ℕ → 𝔹 
Zero ≤ m = True
(Suc n) ≤ Zero = False
(Suc n) ≤ (Suc m) = n ≤ m

==ℕto≤ : {n m : ℕ} → ((n ==ℕ m) == True) → ((n ≤ m) == True)
==ℕto≤ {Zero} {_} _ = Refl
==ℕto≤ {Suc n} {Zero} ()
==ℕto≤ {Suc n} {Suc m} p = ==ℕto≤ {n} {m} p

{- Ungleichheit in ℕ ist entscheidbar: Die Funktion liefert für jedes Paar n,m eine Entscheidung und Beweis bzw. eine Widerlegung von n ≤ m == True -}
dec[n≤m] : (n m : ℕ) → Dec ((n ≤ m) == True)
dec[n≤m] Zero _ = Yes Refl
dec[n≤m] (Suc n) Zero = No f where
  f : (False == True) → ⊥
  f ()
dec[n≤m] (Suc n) (Suc m) = dec[n≤m] n m

refl≤ : (n : ℕ) → ((n ≤ n) == True)
refl≤ Zero = Refl
refl≤ (Suc n) = refl≤ n

antisym≤ : (n m : ℕ) → ((n ≤ m) == True) → ((m ≤ n) == True) → (n == m)
antisym≤ Zero Zero _ _ = Refl
antisym≤ (Suc n) Zero () _ -- Beim Unirechner funzt antisym≤ (Suc n) Zero ()
antisym≤ Zero (Suc m) _ ()
antisym≤ (Suc n) (Suc m) p q = app Suc (antisym≤ n m p q)

trans≤ : {n m l : ℕ} → ((n ≤ m) == True) → ((m ≤ l) == True) → ((n ≤ l) == True)
trans≤ {Zero} {_} {_} _ _ = Refl
trans≤ {Suc n} {Zero} {_} () _ -- s.o.
trans≤ {Suc n} {Suc m} {Zero} _ ()
trans≤ {Suc n} {Suc m} {Suc l} p q = trans≤ {n} {m} {l} p q

dicho≤ : (n m : ℕ) → (((n ≤ m) ∨ (m ≤ n)) == True)
dicho≤ Zero _ = Refl
dicho≤ (Suc n) Zero = Refl
dicho≤ (Suc n) (Suc m) = dicho≤ n m

_<_ : ℕ → ℕ → 𝔹
n < m = (Suc n) ≤ m

<to≤ : (n m : ℕ) → ((n < m) == True) → ((n ≤ m) == True)
<to≤ Zero _ _ = Refl
<to≤ (Suc n) Zero ()
<to≤ (Suc n) (Suc m) p = <to≤ n m p

tricho< : (n m : ℕ) → ((n < m) == True) +Set (((n ==ℕ m) == True) +Set ((m < n) == True))
tricho< Zero Zero = Inr (Inl Refl)
tricho< Zero (Suc m) = Inl Refl
tricho< (Suc n) Zero = Inr (Inr Refl)
tricho< (Suc n) (Suc m) = tricho< n m

_≥_ : ℕ → ℕ → 𝔹
n ≥ m = m ≤ n

≤≥to==ℕ : (n m : ℕ) → ((n ≤ m) == True) → ((n ≥ m) == True) → ((n ==ℕ m) == True)
≤≥to==ℕ Zero Zero _ _ = Refl
≤≥to==ℕ Zero (Suc m) _ ()
≤≥to==ℕ (Suc n) Zero () _
≤≥to==ℕ (Suc n) (Suc m) p q = ≤≥to==ℕ n m p q

_>_ : ℕ → ℕ → 𝔹
n > m = m < n
