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

infixl 13 _+_


{- (ℕ,+) ist ein kommutativer Monoid (mit Einselement Zero)  -}

assoc+ : (n m k : ℕ) → ((n + m) + k) == (n + (m + k))
assoc+ n m Zero = Refl
assoc+ n m (Suc k) = app Suc (assoc+ n m k)

comm+ : (n m : ℕ) → n + m == m + n 
comm+ n Zero = sym== (f n) where
  f : (n : ℕ) → Zero + n == n
  f Zero  = Refl
  f (Suc n) = app Suc (f n)
comm+ n (Suc m) = n + Suc m 
                ==⟨ bydef ⟩ Suc (n + m) 
                ==⟨ app Suc (comm+ n m) ⟩ Suc (m + n) 
                ==⟨ sym== (g m n) ⟩ Suc m + n qed where
  g : (n m : ℕ) → Suc n + m == Suc (n + m)
  g n Zero    = Refl
  g n (Suc m) = app Suc (g n m)

∃e+ : ℕ Σ (λ (e : ℕ) -> (n : ℕ) → (e + n == n) × (n + e == n))
∃e+ = << Zero , f >> where
  f : (n : ℕ) → (Zero + n == n) × (n + Zero == n)
  f n = < g n , h n > where
    g : (n : ℕ) → Zero + n == n
    g n = Zero + n 
        ==⟨ comm+ Zero n ⟩ n + Zero 
        ==⟨ bydef ⟩ n qed
    h : (n : ℕ) → n + Zero == n
    h n = n + Zero 
        ==⟨ bydef ⟩ n qed

{-
≤↔+ : (n m : ℕ) → n ≤ m ↔ ℕ Σ (λ (l : ℕ) -> n + l == m)
≤↔+ n m = < (≤→+ n m) , (+→≤ n m) > where 
  ≤→+ : (n m : ℕ) → n ≤ m → ℕ Σ (λ (l : ℕ) -> n + l == m)
  ≤→+ n m pr[n≤m] = << m - n , MinusIsInvers n m pr[n≤m] >>
  +→≤ : (n m : ℕ) → ℕ Σ (λ (l : ℕ) -> n + l == m → n ≤ m
  +→≤ Zero m _ = ZeroInit
  +→≤ (Suc n) Zero << l , pr[Suc[n]+l==Zero] >> = (g ∘ f) pr[Suc[n]+l==Zero] where
    f : ((Suc n) + l) == Zero → (Suc (n + l)) == Zero
    f pr[Suc[n]+l==Zero] = Suc (n + l)
                         ==⟨ app Suc (comm+ n l) ⟩ Suc (l + n)
                         ==⟨ bydef ⟩ l + Suc n
                         ==⟨ comm+ l (Suc n) ⟩ Suc n + l
                         ==⟨ pr[Suc[n]+l==Zero] ⟩ Zero qed
    g : Suc (n + l) == Zero → Suc n ≤ Zero
    g ()
  +→≤ (Suc n) (Suc m) << l , pr[Suc[n]+l==Suc[m]] >> = 

+→≤ n m << l , app pred (==trans (==sym (SucNPlusMisSucNPlusM n l)) p) >>
-}

{- Definition Subtraktion -}

_-_ : ℕ → ℕ → ℕ
n - Zero = n
Zero - m = Zero
(Suc n) - (Suc m) = n - m

infixl 13 _-_


{- Rechenregeln Subtraktion -}

--extractSucfromMinuend : (n m : ℕ) → (Suc n) - m == Suc (n - m)
--extractSucfromMinuend n Zero = (Suc n) - Zero ==⟨ bydef ⟩ (Suc n) ==⟨ bydef ⟩ Suc (n - Zero) qed
--extractSucfromMinuend n (Suc m) = (Suc n) - (Suc m) ==⟨ bydef ⟩ n - m

extractSucfromSubtrahent : (n m : ℕ) → n - Suc m == pred (n - m)
extractSucfromSubtrahent Zero Zero = Zero - Suc Zero 
                                   ==⟨ bydef ⟩ Zero 
                                   ==⟨ bydef ⟩ pred Zero 
                                   ==⟨ bydef ⟩ pred (Zero - Zero) qed
extractSucfromSubtrahent Zero (Suc m) = Zero - (Suc (Suc m))
                                      ==⟨ bydef ⟩ Zero
                                      ==⟨ bydef ⟩ pred Zero
                                      ==⟨ bydef ⟩ pred (Zero - Suc m) qed
extractSucfromSubtrahent (Suc n) (Zero) = (Suc n) - Suc Zero
                                        ==⟨ bydef ⟩ n - Zero
                                        ==⟨ bydef ⟩ n
                                        ==⟨ bydef ⟩ pred (Suc n)
                                        ==⟨ bydef ⟩ pred (Suc n - Zero) qed
extractSucfromSubtrahent (Suc n) (Suc m) = (Suc n) - (Suc (Suc m))
                                         ==⟨ bydef ⟩ n - Suc m
                                         ==⟨ extractSucfromSubtrahent n m ⟩ pred (n - m)
                                         ==⟨ bydef ⟩ pred (Suc n - Suc m) qed


{- Beweis, dass für n ≤ m gilt, dass n + (m - n) == m -}

--assoc+-forposdiff : (n m l : ℕ) → m ≥ l → n + (m - l) = (n + m) - l


MinusIsInvers : (n m : ℕ) → n ≤ m → n + (m - n) == m
MinusIsInvers Zero m _ = Zero + m ==⟨ comm+ Zero m ⟩ m + Zero ==⟨ bydef ⟩ m qed
MinusIsInvers (Suc n) Zero () 
MinusIsInvers (Suc n) (Suc m) pr[Suc[n]≤Suc[m]] = Suc n + (Suc m - Suc n) 
                                                ==⟨ comm+ (Suc n) (Suc m - Suc n) ⟩ Suc m - Suc n + Suc n
                                                ==⟨ bydef ⟩ Suc (Suc m - Suc n + n)
                                                ==⟨ bydef ⟩ Suc (m - n + n)
                                                ==⟨ app Suc (comm+ (m - n) n) ⟩ Suc (n + (m - n))
                                                ==⟨ app Suc (MinusIsInvers n m (pred≤ pr[Suc[n]≤Suc[m]])) ⟩ Suc m qed





{- Multiplikation -}

{- Definition der Multiplikation -}
_*_ : ℕ → ℕ → ℕ
n * Zero = Zero
n * (Suc m) = (n * m) + n

infixl 14 _*_





{- Division -}

{- Definition der Division -}
_div_ :  ℕ → ℕ → ℕ
Zero div _ = Zero
(Suc n) div m with (decEqℕ {(n div m) * m + m} {Suc n})
(Suc n) div m | Yes _ = Suc (n div m)
(Suc n) div m | No _ = n div m

infixl 14 _div_

{- Definition der Restfunktion -}
_mod_ : ℕ → ℕ → ℕ
n mod m = n - ((n div m) * m) 

infixl 14 _mod_



{- Potenz -}

{- Definition der Potenz -}
_^_ : ℕ → ℕ → ℕ
n ^ Zero = Suc Zero
n ^ (Suc m) = (n ^ m) * n

infixl 15 _^_


