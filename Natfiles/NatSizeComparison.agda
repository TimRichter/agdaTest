module Natfiles.NatSizeComparison where

open import Natfiles.NatDataDef

open import PropositionalEquality
  
open import Bool

open import Natfiles.NatSizelessFunctions

{- Gleichheit in ℕ ist entscheidbar -}

decEqℕ : {n m : ℕ} → Dec (n == m)
decEqℕ {Zero} {Zero} = Yes Refl
decEqℕ {Suc n} {Zero} = No f where
  f : {n : ℕ} -> ((Suc n) == Zero) → ⊥
  f ()
decEqℕ {Zero} {Suc m} = No f where
  f : {m : ℕ} -> (Zero == (Suc m)) → ⊥
  f ()
decEqℕ {Suc n} {Suc m} with (decEqℕ {n} {m})
decEqℕ {Suc n} {Suc m} | (Yes nEqm)  = Yes (ap Suc nEqm)
decEqℕ {Suc n} {Suc m} | (No  ¬nEqm) = No (¬nEqm ∘ f) where
               f : (Suc n == Suc m) → (n == m)
               f snEqsm = (ap pred snEqsm)


{- Definition von ≤ als Datentyp -}

data _≤_ : ℕ → ℕ → Set where
  ZeroInit : {m : ℕ} → Zero ≤ m
  Suc≤ : {n m : ℕ} → n ≤ m → Suc n ≤ Suc m

infix 11 _≤_


{- Rückwärtsargumentation für ≤ -}

pred≤ : {n m : ℕ} → n ≤ m → (pred n) ≤ (pred m)
pred≤ {Zero} {m} _ = ZeroInit
pred≤ {Suc n} {Zero} ()
pred≤ {Suc n} {Suc m} (Suc≤ pr[n≤m]) = pr[n≤m]


{- Ungleichheit in ℕ ist entscheidbar -}

dec[n≤m] : (n m : ℕ) → Dec (n ≤ m)
dec[n≤m] Zero m = Yes ZeroInit
dec[n≤m] (Suc n) Zero = No ¬pr[Suc[n]≤Zero] where
  ¬pr[Suc[n]≤Zero] : Suc n ≤ Zero → ⊥
  ¬pr[Suc[n]≤Zero] ()
dec[n≤m] (Suc n) (Suc m) with (dec[n≤m] n m)
dec[n≤m] (Suc n) (Suc m) | Yes pr[n≤m] = Yes (Suc≤ pr[n≤m])
dec[n≤m] (Suc n) (Suc m) | No ¬pr[n≤m] = No ¬pr[Suc[n]≤Suc[m]] where
  ¬pr[Suc[n]≤Suc[m]] : Suc n ≤ Suc m → ⊥
  ¬pr[Suc[n]≤Suc[m]] pr[Suc[n]≤Suc[m]] = ¬pr[n≤m] (pred≤ pr[Suc[n]≤Suc[m]])


{- ≤ ist eine lineare Ordnung -}

refl≤ : {n : ℕ} → n ≤ n
refl≤ {Zero} = ZeroInit
refl≤ {Suc n} = Suc≤ (refl≤ {n})


antisym≤ : {n m : ℕ} → n ≤ m → m ≤ n → (n == m)
antisym≤ {Zero} {Zero} _ _ = Refl
antisym≤ {Suc n} {Zero} () _ 
antisym≤ {Zero} {Suc m} _ ()
antisym≤ {Suc n} {Suc m} pr[Suc[n]≤Suc[m]] pr[Suc[m]≤Suc[n]]  = ap Suc (antisym≤ {n} {m} (pred≤ pr[Suc[n]≤Suc[m]]) (pred≤ pr[Suc[m]≤Suc[n]]))


trans≤ : {n m l : ℕ} → n ≤ m → m ≤ l → n ≤ l
trans≤ {Zero} {_} {l} _ _ = ZeroInit
trans≤ {Suc n} {Zero} {_} () _
trans≤ {Suc n} {Suc m} {Zero} _ ()
trans≤ {Suc n} {Suc m} {Suc l} pr[Suc[n]≤Suc[m]] pr[Suc[m]≤Suc[l]] = Suc≤ (trans≤ {n} {m} {l} (pred≤ pr[Suc[n]≤Suc[m]]) (pred≤ pr[Suc[m]≤Suc[l]]))


dicho≤ : {n m : ℕ} → n ≤ m +Set m ≤ n
dicho≤ {Zero} {m} = Inl ZeroInit
dicho≤ {Suc n} {Zero} = Inr ZeroInit
dicho≤ {Suc n} {Suc m} with (dicho≤ {n} {m})
dicho≤ {Suc n} {Suc m} | Inl pr[n≤m] = Inl (Suc≤ pr[n≤m])
dicho≤ {Suc n} {Suc m} | Inr pr[m≤n] = Inr (Suc≤ pr[m≤n])


{- Definition von < über ≤ -}

_<_ : ℕ → ℕ → Set
n < m = (Suc n) ≤ m

infix 11 _<_


{- Zusammenhänge von < und ≤ -}

≤↔<∨== : {n m : ℕ} → n ≤ m ↔ n < m +Set n == m
≤↔<∨== {Zero} {Zero} = < f , g > where
  f : Zero ≤ Zero → Zero < Zero +Set Zero == Zero
  f _ = Inr Refl
  g : Zero < Zero +Set Zero == Zero → Zero ≤ Zero
  g (Inl ())
  g (Inr _) = ZeroInit
≤↔<∨== {Suc n} {Zero} = < f , g > where
  f : Suc n ≤ Zero → Suc n < Zero +Set Suc n == Zero
  f ()
  g : Suc n < Zero +Set Suc n == Zero → Suc n ≤ Zero
  g (Inl ())
  g (Inr ())
≤↔<∨== {Zero} {Suc m} = < f , g > where
  f : Zero ≤ Suc m → Zero < Suc m +Set Zero == Suc m
  f _ = Inl (Suc≤ ZeroInit)
  g : Zero < Suc m +Set Zero == Suc m → Zero ≤ Suc m
  g (Inl _) = ZeroInit
  g (Inr ())
≤↔<∨== {Suc n} {Suc m} = < f , g > where
  f : Suc n ≤ Suc m → Suc n < Suc m +Set Suc n == Suc m
  f pr[Suc[n]≤Suc[m]] with ((pr1× (≤↔<∨== {n} {m})) (pred≤ pr[Suc[n]≤Suc[m]]))
  f pr[Suc[n]≤Suc[m]] | Inl pr[n<m] = Inl (Suc≤ pr[n<m])
  f pr[Suc[n]≤Suc[m]] | Inr pr[n==m] = Inr (ap Suc pr[n==m])
  g : Suc n < Suc m +Set Suc n == Suc m → Suc n ≤ Suc m
  g (Inl pr[Suc[n]<Suc[m]]) = Suc≤ ((pr2× (≤↔<∨== {n} {m})) (Inl (pred≤ pr[Suc[n]<Suc[m]])))
  g (Inr pr[Suc[n]==Suc[m]]) = Suc≤ ((pr2× (≤↔<∨== {n} {m})) (Inr (ap pred pr[Suc[n]==Suc[m]])))


<to≤ : {n m : ℕ} → n < m → n ≤ m
<to≤ {Zero} {_} _ = ZeroInit
<to≤ {Suc n} {Zero} ()
<to≤ {Suc n} {Suc m} pr[Suc[Suc[n]]≤Suc[m]] = trans≤ (f (Suc n)) pr[Suc[Suc[n]]≤Suc[m]] where
  f : (n : ℕ) → n ≤ Suc n
  f Zero = ZeroInit
  f (Suc n) = Suc≤ (f n)


{- < ist eine nichtreflexive lineare Ordnung -}

irrefl< : {n : ℕ} → ¬ (n < n)
irrefl< {Zero} = ¬pr[Zero<Zero] where
  ¬pr[Zero<Zero] : Zero < Zero → ⊥
  ¬pr[Zero<Zero] () 
irrefl< {Suc n} =  ¬pr[Suc[n]<Suc[n]] where
  ¬pr[Suc[n]<Suc[n]] : Suc n < Suc n → ⊥
  ¬pr[Suc[n]<Suc[n]] pr[Suc[n]<Suc[n]] = irrefl< {n} (pred≤ pr[Suc[n]<Suc[n]])


trans< : {n m l : ℕ} → n < m → m < l → n < l
trans< {n} {_} {_} pr[n<m] pr[m<l] = trans≤ (<to≤ pr[Suc[n]<Suc[Suc[n]]]) (trans≤ (Suc≤ pr[n<m]) pr[m<l]) where
  pr[Suc[n]<Suc[Suc[n]]] = refl≤


asym< : {n m : ℕ} → n < m → ¬ (m < n)
asym< {n} {m} pr[n<m] = ¬pr[m<n] where
  ¬pr[m<n] : m < n → ⊥
  ¬pr[m<n] pr[m<n] = irrefl< (trans< pr[n<m] pr[m<n])


tricho< : (n m : ℕ) → n < m +Set n == m +Set m < n
tricho< n m = f (dicho≤) where
  f : {n m : ℕ} → n ≤ m +Set m ≤ n → n < m +Set n == m +Set m < n
  f {n} {m} (Inl pr[n≤m]) with ((pr1× ≤↔<∨==) pr[n≤m])
  f {n} {m} (Inl pr[n≤m]) | Inl pr[n<m] = Inl pr[n<m]
  f {n} {m} (Inl pr[n≤m]) | Inr pr[n==m] = Inr (Inl pr[n==m])
  f {n} {m} (Inr pr[m≤n]) with ((pr1× ≤↔<∨==) pr[m≤n])
  f {n} {m} (Inr pr[m≤n]) | Inl pr[m<n] = Inr (Inr pr[m<n])
  f {n} {m} (Inr pr[m≤n]) | Inr pr[m==n] = Inr (Inl (sym== pr[m==n]))


{- Definition von ≥ über ≤ -}

_≥_ : ℕ → ℕ → Set
n ≥ m = m ≤ n

infix 11 _≥_

{- Zusammenhang von ≤, ≥ und == -}

≤∧≥↔== : {n m : ℕ} → (n ≤ m) × (m ≤ n) ↔ n == m
≤∧≥↔== = < ≤∧≥→== , ≤∧≥←== > where
  ≤∧≥→== : {n m : ℕ} → (n ≤ m) × (m ≤ n) → n == m
  ≤∧≥→== < pr[n≤m] , pr[m≤n] > = antisym≤ pr[n≤m] pr[m≤n]
  ≤∧≥←== : {n m : ℕ} → n == m → (n ≤ m) × (m ≤ n)
  ≤∧≥←== {n} {.n} Refl = < refl≤ , refl≤ >

==ℕto≤ : {n m : ℕ} → (n == m) → (n ≤ m)
==ℕto≤ {n} {m} pr[n==m] = pr1× ((pr2× ≤∧≥↔==) pr[n==m])

≤∧≥to==ℕ : {n m : ℕ} → (n ≤ m) × (m ≤ n) → n == m
≤∧≥to==ℕ = (pr1× ≤∧≥↔==)

{- Definition von > über < -}

_>_ : ℕ → ℕ → Set
n > m = m < n

infix 11 _>_

