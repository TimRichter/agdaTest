module Rat where

open import Natfiles.Nat
open import TypeConstructions
open import PropositionalEquality
open import Bool

data ℚ : Set where
  ℚC : ℕ → (m : ℕ) → ¬ (m == Zero) → ℚ

-- data _∣_ (n : ℕ)  (m : ℕ) : Set where
  -- MaxZero : n ∣ Zero

¬[n<n] : (n : ℕ) → ((n < n) == True) → ⊥
¬[n<n] Zero ()
¬[n<n] (Suc n) p = ¬[n<n] n p

boundedSearch∣ : (n k m : ℕ) → Dec (ℕ Σ (λ (l : ℕ) -> ((l ≤ k) == True) × ((n * l) == m)))
boundedSearch∣ n Zero m = g n m where
  g : (n m : ℕ) → Dec (ℕ Σ (λ (l : ℕ) -> ((l ≤ Zero) == True) × ((n * l) == m)))
  g n Zero = Yes << Zero , < Refl , Refl > >>
  g n (Suc m) = No ¬pr[n*Zero]==[Suc[m]] where
    ¬pr[n*Zero]==[Suc[m]] : ℕ Σ (λ (l : ℕ) -> ((l ≤ Zero) == True) × ((n * l) == (Suc m))) → ⊥
    ¬pr[n*Zero]==[Suc[m]] << Zero , < _ , () > >>
    ¬pr[n*Zero]==[Suc[m]] << (Suc l) , < () , _ > >>
boundedSearch∣ n (Suc k) m with (boundedSearch∣ n k m)
boundedSearch∣ n (Suc k) m | Yes << l , < pr[l≤k] , pr[n*l==m] > >> = Yes << l , < (<to≤ l (Suc k) pr[l≤k]) , pr[n*l==m] > >>
boundedSearch∣ n (Suc k) m | No ¬pr[n*≤k==m] with (decEqℕ (n * (Suc k)) m)
boundedSearch∣ n (Suc k) m | No ¬pr[n*≤k==m] | Yes pr[n*Suc[k]==m] = Yes << (Suc k) , < (refl≤ (Suc k)) , pr[n*Suc[k]==m] > >>
boundedSearch∣ n (Suc k) m | No ¬pr[n*≤k==m] | No ¬pr[n*Suc[k]==m] = No ¬pr[n*≤Suc[k]==m] where
  ¬pr[n*≤Suc[k]==m] : ℕ Σ (λ (l : ℕ) -> ((l ≤ (Suc k)) == True) × ((n * l) == m)) → ⊥
  ¬pr[n*≤Suc[k]==m] << l , < pr[l≤Suc[k]] , pr[n*l==m] > >> = ¬tricho< (tricho< l (Suc k)) where
    ¬tricho< : ((l < (Suc k)) == True) +Set (((l ==ℕ (Suc k)) == True) +Set ((l > (Suc k)) == True)) → ⊥
    ¬tricho< (Inl pr[l<Suc[k]]) = ¬pr[n*≤k==m] (<< l , < pr[l<Suc[k]] , pr[n*l==m] > >>)
    ¬tricho< (Inr (Inl pr[l==ℕSuc[k]])) = ¬pr[n*Suc[k]==m] (n * (Suc k) ==〈 app (_*_ n) (==sym (==ℕto== {l} {Suc k} (pr[l==ℕSuc[k]]))) 〉 n * l ==〈 pr[n*l==m] 〉 m qed)
    ¬tricho< (Inr (Inr pr[l>Suc[k]])) = ¬[n<n] l (trans≤ {Suc l} {Suc (Suc k)} {l} pr[l≤Suc[k]] pr[l>Suc[k]])



dec∣ : (n m : ℕ) → Dec (ℕ Σ (λ (l : ℕ) -> n * l == m))
dec∣ Zero Zero = Yes << Zero , Refl >>
dec∣ Zero (Suc m) = No ¬pr[Zero*l==Suc[m]] where
  ¬pr[Zero*l==Suc[m]] : (ℕ Σ (λ (l : ℕ) -> Zero * l == Suc m)) → ⊥
  ¬pr[Zero*l==Suc[m]] << l , pr[Zero*l==Suc[m]] >> = f (Zero ==〈 bydef 〉 l * Zero ==〈 comm* l Zero 〉 Zero * l ==〈 pr[Zero*l==Suc[m]] 〉 Suc m qed) where
    f : Zero == Suc m → ⊥
    f ()
dec∣ (Suc n) m with (boundedSearch∣ (Suc n) m m)
dec∣ (Suc n) m | Yes << l , < pr[l≤m] , pr[[Suc[n]]*l==m] > >> = Yes << l , pr[[Suc[n]]*l==m] >>
dec∣ (Suc n) m | No ¬pr[[Suc[n]]*≤m==m] = No ¬pr[[Suc[n]]*l==m] where
  ¬pr[[Suc[n]]*l==m] : (ℕ Σ (λ (l : ℕ) -> (Suc n) * l == m)) → ⊥
  ¬pr[[Suc[n]]*l==m] << l , pr[[Suc[n]]*l==m] >> = g (tricho< l m) where
    g : (l < m == True) +Set (l ==ℕ m == True) +Set (l > m == True) → ⊥
    g (Inl pr[l<m]) = ¬pr[[Suc[n]]*≤m==m] (<< l , < (<to≤ l m pr[l<m]) , pr[[Suc[n]]*l==m] > >>)
    g (Inr (Inl pr[l==ℕm])) = ¬pr[[Suc[n]]*≤m==m] (<< l , < (==ℕto≤ {l} {m} pr[l==ℕm]) , pr[[Suc[n]]*l==m] > >>)
    g (Inr (Inr pr[l>m])) = ¬[n<n] m (trans≤ {Suc m} {l * (Suc n)} {m} (trans≤ {Suc m} {l} {l * (Suc n)} pr[l>m] pr[l≤l*[Suc[n]]]) pr[l*[Suc[n]]≤m]) where
      pr[l≤l*[Suc[n]]] = trans≤ {l} {Zero + l} {l * (Suc n)}(==to≤ l (Zero + l) (l ==〈 bydef 〉 l + Zero ==〈 comm+ l Zero 〉 Zero + l qed)) (monotonicity≤+ Zero (l * n) l l Refl (refl≤ l))
      pr[l*[Suc[n]]≤m] = ==to≤ (l * (Suc n)) m (l * (Suc n) ==〈 comm* l (Suc n) 〉 (Suc n) * l ==〈 pr[[Suc[n]]*l==m] 〉 m qed)
      

-- (n k m : ℕ) → Dec (ℕ Σ (λ (l : ℕ) -> ((l ≤ k) == True) × ((n * l) == m)))


{-  
dec∣ : (n : ℕ) → (m : ℕ) → Dec (ℕ Σ (λ (k : ℕ) -> n * k == m))
dec∣ _ Zero = Yes (<< Zero , Refl >>)
dec∣ Zero (Suc m) = No ¬Zero∣Suc[m] where
  ¬Zero∣Suc[m] : (ℕ Σ (λ (k : ℕ) -> Zero * k == (Suc m))) → ⊥
  ¬Zero∣Suc[m] (<< k , pr[Zero*k]==[Suc[m]] >>) = g pr[Zero==Suc[m]] where
    g : Zero == (Suc m) → ⊥
    g ()
    pr[Zero==Suc[m]] =
      Zero
      ==〈 bydef 〉 k * Zero
      ==〈 comm* k Zero 〉 Zero * k
      ==〈 pr[Zero*k]==[Suc[m]] 〉 (Suc m) qed
-}
