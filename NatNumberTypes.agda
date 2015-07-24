module NatNumberTypes where

open import Natfiles.Nat renaming (_+_ to _+ℕ_)

open import PropositionalEquality

open import Bool

data Fin (n : ℕ) : Set where
  FinC : (m : ℕ) → ((m < n) == True) → Fin n


_+_ : {n : ℕ} → Fin n → Fin n → Fin n
_+_ {n} (FinC m p) (FinC l q) with (dec[n≤m] (Suc (m +ℕ l)) n) --((m +ℕ l) < n)
_+_ {n} (FinC m p) (FinC l q) | Yes proof[m+ℕl]<n = FinC (m +ℕ l) proof[m+ℕl]<n
_+_ {n} (FinC m p) (FinC l q) | No _ = FinC ...

-- dec[n≤m] : (n m : ℕ) → Dec ((n ≤ m) == True)

oneborrowsuffices : (n m k : ℕ) → (m ≤ n) == True → (k ≤ n) == True → (((m +ℕ k) - n) ≤ n) == True
oneborrowsuffices n m k proofm≤n proofk≤n = trans≤ {(m +ℕ k) - n} {(n +ℕ n) - n} {n} proof[[m+ℕk]-n]≤[[n+ℕn]-n] proof[[n+ℕn]-n]≤n where
  proof[[m+ℕk]-n]≤[[n+ℕn]-n] = monotonicity≤- (m +ℕ k) (n +ℕ n) n n proof[m+ℕk]≤[n+ℕn] (refl≤ n) where
    proof[m+ℕk]≤[n+ℕn] = monotonicity≤+ m n k n proofm≤n proofk≤n
  proof[[n+ℕn]-n]≤n = ==ℕto≤ {(n +ℕ n) - n} {n} (==to==ℕ (proof[n+ℕn]-nisn)) where
    proof[n+ℕn]-nisn = ==trans ([n+m]-lisn+[m-l]for[m≥l] n n n (refl≤ n)) (MinusIsInvers n n (refl≤ n))



-- Erstmal allgemein zeigen dass m+l - n < n

-- if ((m +ℕ l) ≤ 2) then (FinC 1 Refl) else (FinC m p)

-- _+_ : {n : ℕ} → Fin n → Fin n → Fin n
-- (FinC m p) + (FinC l _)  = if ((m +ℕ l) ≤ 5) then (FinC (m +ℕ l) (Refl True)) else (FinC m p)
