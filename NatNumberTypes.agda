module NatNumberTypes where

open import Natfiles.Nat renaming (_+_ to _+ℕ_)

open import PropositionalEquality

open import Bool

data Fin (n : ℕ) : Set where
  FinC : (m : ℕ) → ((m < n) == True) → Fin n

oneborrowsuffices : (n m k : ℕ) → (m ≤ n) == True → (k ≤ n) == True → (((m +ℕ k) - n) ≤ n) == True
oneborrowsuffices n m k proofm≤n proofk≤n = trans≤ {(m +ℕ k) - n} {(n +ℕ n) - n} {n} proof[[m+ℕk]-n]≤[[n+ℕn]-n] proof[[n+ℕn]-n]≤n where
  proof[[m+ℕk]-n]≤[[n+ℕn]-n] = monotonicity≤- (m +ℕ k) (n +ℕ n) n n proof[m+ℕk]≤[n+ℕn] (refl≤ n) where
    proof[m+ℕk]≤[n+ℕn] = monotonicity≤+ m n k n proofm≤n proofk≤n
  proof[[n+ℕn]-n]≤n = ==ℕto≤ {(n +ℕ n) - n} {n} (==to==ℕ (proof[n+ℕn]-nisn)) where
    proof[n+ℕn]-nisn = ==trans ([n+m]-lisn+[m-l]for[m≥l] n n n (refl≤ n)) (MinusIsInvers n n (refl≤ n))

_+_ : {n : ℕ} → Fin n → Fin n → Fin n
_+_ {n} (FinC m proof[m<n]) (FinC l proof[l<n]) with (dec[n≤m] (Suc (m +ℕ l)) n) --((m +ℕ l) < n)
_+_ {n} (FinC m proof[m<n]) (FinC l proof[l<n]) | Yes proof[m+ℕl]<n = FinC (m +ℕ l) proof[m+ℕl]<n
_+_ {n} (FinC m proof[m<n]) (FinC l proof[l<n]) | No ¬proof[m+ℕl]<n = FinC ((m +ℕ l) - n) proof[[m+ℕl]-n<n] where
  proof[[m+ℕl]-n<n] = trans≤ {Suc ((m +ℕ l) - n)} {(m +ℕ (Suc l)) - n} {n} 
    proof[Suc[[m+ℕl]-n]≤[m+ℕSuc[l]]-n] proof[[m+ℕSuc[l]]-n≤n] where
    proof[Suc[[m+ℕl]-n]≤[m+ℕSuc[l]]-n] = ==ℕto≤ {Suc ((m +ℕ l) - n)} {(m +ℕ (Suc l)) - n} 
        (==to==ℕ (==sym {ℕ} {(m +ℕ (Suc l)) - n} {Suc ((m +ℕ l) - n)} 
           ([Sucn]-misSuc[n-m]for[n≥m] (m +ℕ l) n proof[m+ℕl≥n]))) where
      proof[m+ℕl≥n] = fcases (tricho< (m +ℕ l) n) where
        fcases : (((m +ℕ l) < n) == True) +Set ((((m +ℕ l) ==ℕ n) == True) +Set 
                 ((n < (m +ℕ l)) == True)) → ((m +ℕ l) ≥ n) == True
        fcases (Inl proof[m+ℕl<n]) = ⊥-elim {((m +ℕ l) ≥ n) == True} (¬proof[m+ℕl]<n proof[m+ℕl<n])
        fcases (Inr (Inl proof[m+ℕl==ℕn])) = ==ℕto≤ {n} {m +ℕ l} (sym==ℕ {m +ℕ l} {n} proof[m+ℕl==ℕn])
        fcases (Inr (Inr proof[n<[m+ℕl]])) = <to≤ n (m +ℕ l) proof[n<[m+ℕl]]
    proof[[m+ℕSuc[l]]-n≤n] = oneborrowsuffices n m (Suc l) (<to≤ m n proof[m<n]) proof[l<n]

