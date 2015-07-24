module Natfiles.NatInd where

open import Natfiles.NatDataDef

open import Natfiles.NatSizeComparison

open import TypeConstructions

open import PropositionalEquality

open import Bool

{- Induktionsprinzip auf ℕ -}
ℕInd : {A : ℕ → Set} → (A Zero) → ((n : ℕ) → A n → A (Suc n)) → (l : ℕ) → A l
ℕInd ia is Zero = ia
ℕInd ia is (Suc n) = is n (ℕInd ia is n)


Accum : (ℕ → Set) → (ℕ → Set)
Accum A Zero    = A Zero
Accum A (Suc n) = (Accum A n) × (A (Suc n))


accumprop : {A : ℕ → Set} → (n : ℕ) → Accum A n → (l : ℕ) → ((l ≤ n) == True) → A l
accumprop Zero p Zero _ = p
accumprop Zero p (Suc n) ()
accumprop {A} (Suc n) p l _ with (tricho< l n)
accumprop {A} (Suc n) p l _ | Inl q = accumprop n (pr1× p) l (<to≤ l n q) 
accumprop {A} (Suc n) p l _ | Inr (Inl q) = accumprop n (pr1× p) l (==ℕto≤ {l} {n} q) 
accumprop {A} (Suc n) p l r | Inr (Inr q) = leibnizid==ℕ A (Suc n) l (≤≥to==ℕ (Suc n) l q r) (pr2× p)

ℕInd< : {A : ℕ → Set} → 
         ((n : ℕ) → ((m : ℕ) → ((m < n) == True) → A m) → A n) → 
         ((l : ℕ) → A l)
ℕInd< {A} b = p ◑ (ℕInd {Accum A} aaz aas) where
  p : {l : ℕ} → Accum A l → A l
  p {l} q = accumprop l q l (refl≤ l)
  aaz : Accum A Zero
  aaz = b Zero f where
   f : (m : ℕ) → ((m < Zero) == True) → A m
   f _ ()
  aas : (n : ℕ) → Accum A n → Accum A (Suc n) 
  aas n p = < p , b (Suc n) f > where
    f : (m : ℕ) → ((m < (Suc n)) == True) → A m
    f m q = accumprop n p m q
