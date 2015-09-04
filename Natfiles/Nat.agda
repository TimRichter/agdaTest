{- Mit ctrl-c ctrl-l nicht alle bis auf bisheriges Fenster schließen 
   Programme schreiben, die man von der Konsole aus aufrufen kann
   Daten aus Exceltabelle ziehen, als Eingabe mit Agda verwurschten, Ausgabe 
         produzieren und diese in Tex File schicken (und ggf. gleich das pdf erstellen)
   Ist Teiltyp ohne 0 einführbar?  
   Benutzung von Holes ??
-}

{-  -- C-c C-,   zeige Goaltype -}

module Natfiles.Nat where

open import Natfiles.NatDataDef public

open import Natfiles.NatInd public

open import Natfiles.NatFunctions public

open import Natfiles.NatSizeComparison public 

open import PropositionalEquality public
{-
decEqℕ : (n m : ℕ) → Dec (n == m)
_==ℕ_ : ℕ → ℕ → 𝔹 
leibnizid==ℕ : (A : ℕ → Set) → (n m : ℕ) → ((n ==ℕ m) == True) → A n → A m
_≤_ : ℕ → ℕ → 𝔹 
==ℕto≤ : (n m : ℕ) → ((n ==ℕ m) == True) → ((n ≤ m) == True)
decLeqℕ : (n m : ℕ) → Dec ((n ≤ m) == True)
refl≤ : (n : ℕ) → ((n ≤ n) == True)
antisym≤ : (n m : ℕ) → ((n ≤ m) == True) → ((m ≤ n) == True) → (n == m)
trans≤ : (n m l : ℕ) → ((n ≤ m) == True) → ((m ≤ l) == True) → ((n ≤ l) == True)
dicho≤ : (n m : ℕ) → (((n ≤ m) ∨ (m ≤ n)) == True)
_<_ : ℕ → ℕ → 𝔹
<to≤ : (n m : ℕ) → ((n < m) == True) → ((n ≤ m) == True)
tricho< : (n m : ℕ) → ((n < m) == True) +Set (((n ==ℕ m) == True) +Set ((m < n) == True))
_≥_ : ℕ → ℕ → 𝔹
≤≥to==ℕ : (n m : ℕ) → ((n ≤ m) == True) → ((n ≥ m) == True) → ((n ==ℕ m) == True)
_>_ : ℕ → ℕ → 𝔹
-}




-- Aus ℕInd< folgt Wohlordnung

{- Die Kleinergleichrelation ist eine Wohlordnung -}

--wellord≤ : {B : ℕ → Set} → (ℕ Σ B) → ((ℕ Σ B) Σ helpB)

open import PropositionalEquality

open import Bool

open import TypeConstructions

≤↔+ : (n m : ℕ) → ((n ≤ m) == True) ↔ (ℕ Σ (λ (l : ℕ) -> ((n + l) == m)))
≤↔+ n m = < (≤→+ n m) , (+→≤ n m) > where 
  ≤→+ : (n m : ℕ) → ((n ≤ m) == True) → ℕ Σ (λ (l : ℕ) -> ((n + l) == m))
  ≤→+ n m p = << m - n , MinusIsInvers n m p >>
  +→≤ : (n m : ℕ) → ℕ Σ (λ (l : ℕ) -> ((n + l) == m)) → ((n ≤ m) == True)
  +→≤ Zero m _ = Refl
  +→≤ (Suc n) Zero (<< l , p >>) = (g ∘ f) p where
    f : ((Suc n) + l) == Zero → (Suc (n + l)) == Zero
    f p = trans== (sym== (comm+ (Suc n) l)) p
    g :  (Suc (n + l)) == Zero → (((Suc n) ≤ Zero) == True)
    g ()
  +→≤ (Suc n) (Suc m) << l , p >> = +→≤ n m << l , app pred (trans== (sym== (comm+ (Suc n) l)) p) >>

distr : (n m k : ℕ) → n * (m + k) == (n * m) + (n * k)
distr n m Zero = Refl
distr n m (Suc k) = trans== proof[[n*[m+k]]+n]is[[[n*m]+[n*k]]+n] proof[[[n*m]+[n*k]]+n]is[[n*m]+[[n*k]+n]] where
  proof[[n*[m+k]]+n]is[[[n*m]+[n*k]]+n] = trans== proof[[n*[m+k]]+n]is[n+[n*[m+k]]]
                                        (trans== proof[n+[n*[m+k]]]is[n+[[n*m]+[n*k]]] proof[n+[[n*m]+[n*k]]]is[[[n*m]+[n*k]]+n]) where
    proof[[n*[m+k]]+n]is[n+[n*[m+k]]] = comm+ (n * (m + k)) n
    proof[n+[n*[m+k]]]is[n+[[n*m]+[n*k]]] = app (_+_ n) (distr n m k)
    proof[n+[[n*m]+[n*k]]]is[[[n*m]+[n*k]]+n] = comm+ n ((n * m) + (n * k))
  proof[[[n*m]+[n*k]]+n]is[[n*m]+[[n*k]+n]] = assoc+ (n * m) (n * k) n

assoc* : (n m k : ℕ) → ((n * m) * k) == (n * (m * k))
assoc* n m Zero = Refl
assoc* n m (Suc k) = trans== proof[[[n*m]*k]+[n*m]]is[[n*m]+[[n*m]*k]] (trans== proof[[n*m]+[[n*m]*k]]is[[n*m]+[n*[m*k]]] 
                     (trans== proof[[n*m]+[n*[m*k]]]is[[n*[m*k]]+[n*m]] proof[[n*[m*k]]+[n*m]]is[n*[[m*k]+m]])) where
  proof[[[n*m]*k]+[n*m]]is[[n*m]+[[n*m]*k]] = comm+ ((n * m) * k) (n * m)
  proof[[n*m]+[[n*m]*k]]is[[n*m]+[n*[m*k]]] = app (_+_ (n * m)) (assoc* n m k)
  proof[[n*m]+[n*[m*k]]]is[[n*[m*k]]+[n*m]] = comm+ (n * m) (n * (m * k))
  proof[[n*[m*k]]+[n*m]]is[n*[[m*k]+m]] = sym== (distr n (m * k) m)

zeroisidin[ℕ,*] : (n : ℕ) → ((Zero * n) == Zero) × ((n * Zero) == Zero)
zeroisidin[ℕ,*] Zero = < Refl , Refl >
zeroisidin[ℕ,*] (Suc n) = < (pr1× (zeroisidin[ℕ,*] n)) , Refl >

fun[Suc[n]*m==[n*m]+m] : (n m : ℕ) → ((Suc n) * m) == ((n * m) + m)
fun[Suc[n]*m==[n*m]+m] n Zero = Refl
fun[Suc[n]*m==[n*m]+m] n (Suc m) = 
  (Suc n) * (Suc m) 
  ==〈 bydef 〉 ((Suc n) * m) + (Suc n)
  ==〈 bydef 〉 Suc (((Suc n) * m) + n)
  ==〈 app Suc (comm+ ((Suc n) * m) n) 〉 Suc (n + ((Suc n) * m))
  ==〈 app Suc (app (_+_ n) (fun[Suc[n]*m==[n*m]+m] n m)) 〉 Suc (n + ((n * m) + m))
  ==〈 app Suc (==sym (assoc+ n (n * m) m)) 〉 Suc ((n + (n * m)) + m)
  ==〈 app Suc (comm+ (n + (n * m)) m) 〉 Suc (m + (n + (n * m)))
  ==〈 app Suc (app (_+_ m) (comm+ n (n * m))) 〉 Suc (m + ((n * m) + n))
  ==〈 app Suc (app (_+_ m) {(n * m) + n} {n * (Suc m)} Refl)  〉 Suc (m + (n * (Suc m)))
  ==〈 app Suc (comm+ m (n * (Suc m))) 〉 Suc ((n * (Suc m)) + m)
  ==〈 bydef 〉 ((n * (Suc m)) + (Suc m)) qed

comm* : (n m : ℕ) → (n * m) == (m * n)
comm* n Zero = ==sym (pr1× (zeroisidin[ℕ,*] n)) 
comm* n (Suc m) =
  n * (Suc m)
  ==〈 bydef 〉 n * m + n
  ==〈 comm+ (n * m) n 〉 n + n * m
  ==〈 app (_+_ n) (comm* n m) 〉 n + m * n
  ==〈 comm+ n (m * n) 〉 (m * n) + n
  ==〈 ==sym (fun[Suc[n]*m==[n*m]+m] m n) 〉 (Suc m) * n qed

==+== : (n m l k : ℕ) → n == m → l == k → (n + l) == (m + k) 
==+== n m l k p q = ==trans (==trans (==trans (comm+ n l) (app (_+_ l) p)) (comm+ l m)) (app (_+_ m) q)

monotonicity≤+ : (n m k l : ℕ) → ((n ≤ m) == True) → ((k ≤ l) == True)  → 
                 (((n + k) ≤ (m + l)) == True)
monotonicity≤+ n m k l r s = gapex (n + k) (m + l) (<< p + q , p17 >>) where
  gapex :  (n m : ℕ) → (ℕ Σ (λ (l : ℕ) -> ((n + l) == m))) → ((n ≤ m) == True) 
  gapex n m r with (≤↔+ n m)
  gapex n m r | ↔proof < f , g > = g r
  gapsize :  (n m : ℕ) → ((n ≤ m) == True) → (ℕ Σ (λ (l : ℕ) -> ((n + l) == m)))
  gapsize n m r with (≤↔+ n m)
  gapsize n m r | ↔proof < f , g > = f r
  p = pr1Σ (gapsize n m r)
  q = pr1Σ (gapsize k l s)
  p17 = ==trans p14 p57 where
    p14 = ==trans p12 p34 where
      p12 = ==trans p1 p2 where
        p1 = ==sym (assoc+ (n + k) p q)
        p2 = ==+== ((n + k) + p) (n + (k + p)) q q (assoc+ n k p) Refl
      p34 = ==trans p3 p4 where
        p3 = ==+== (n + (k + p)) (n + (p + k)) q q (==+== n n (k + p) (p + k) Refl (comm+ k p)) Refl
        p4 = ==+== (n + (p + k)) ((n + p) + k) q q (==sym (assoc+ n p k)) Refl
    p57 = ==trans p56 p7 where
      p56 = ==trans p5 p6 where
        p5 = ==+== ((n + p) + k) (m + k) q q (==+== (n + p) m k k (pr2Σ (gapsize n m r)) Refl) Refl
        p6 = assoc+ m k q
      p7 = ==+== m m (k + q) l Refl (pr2Σ (gapsize k l s))
  {- vielleicht equational reasoning implementieren und benutzen...? -}

==to==ℕ : {n m : ℕ} → n == m → (n ==ℕ m) == True
==to==ℕ {Zero} {Zero} _ = Refl
==to==ℕ {Suc n} {Zero} ()
==to==ℕ {Zero} {Suc m} ()
==to==ℕ {Suc n} {Suc m} p = ==to==ℕ {n} {m} (app pred p)

==ℕto== : {n m : ℕ} → (n ==ℕ m) == True → n == m
==ℕto== {Zero} {Zero} _ = Refl
==ℕto== {Zero} {Suc m} ()
==ℕto== {Suc n} {Zero} ()
==ℕto== {Suc n} {Suc m} p = app Suc (==ℕto== {n} {m} p)
  
h : (n m k : ℕ) → ((n - m) ≤ k) == True → (n ≤ (k + m)) == True
h Zero _ _ _ = Refl
h _ Zero _ p = p
h (Suc n) (Suc m) k p = monotonicity≤+ n (k + m) (Suc Zero) (Suc Zero) (h n m k proofn-m≤k) Refl where
  proofn-m≤k = trans≤ {n - m} {(Suc n) - (Suc m)} {k} proofn-m≤n'-m' p where
    proofn-m≤n'-m' = ==ℕto≤ {n - m} {(Suc n) - (Suc m)} (==to==ℕ {n - m} {(Suc n) - (Suc m)} Refl)        

NMinusSucMisPredNMinusM : (n m : ℕ) → n - (Suc m) == pred (n - m)
NMinusSucMisPredNMinusM Zero Zero = Refl
NMinusSucMisPredNMinusM Zero (Suc m) = Refl
NMinusSucMisPredNMinusM (Suc n) (Zero) = Refl
NMinusSucMisPredNMinusM (Suc n) (Suc m) = NMinusSucMisPredNMinusM n m

monotonicityPred : (n m : ℕ) → (n ≤ m) == True → ((pred n) ≤ (pred m)) == True
monotonicityPred Zero _ _ = Refl
monotonicityPred (Suc n) Zero ()
monotonicityPred (Suc Zero) _ _ = Refl
monotonicityPred (Suc (Suc n)) (Suc Zero) ()
monotonicityPred (Suc (Suc n)) (Suc (Suc m)) proofn''≤m'' = monotonicityPred (Suc n) (Suc m)  proofn''≤m'' 


monotonicity≤- : (n m k l : ℕ) → (n ≤ m) == True → (k ≥ l) == True → ((n - k) ≤ (m - l)) == True
monotonicity≤- n m k Zero proofn≤m _ = trans≤ {n - k} {n} {m} proofn-k≤n proofn≤m where
  proofn-k≤n : ((n - k) ≤ n) == True {- probieren, ob diese Deklaration auch in anderer Agda-Version funktioniert -}
  proofn-k≤n = f n k where
    f : (n m : ℕ) → ((n - m) ≤ n) == True
    f n Zero = refl≤ n
    f Zero (Suc m) = Refl
    f (Suc n) (Suc m) = trans≤ {n - m} {n} {Suc n} (f n m) (monotonicity≤+ n n Zero (Suc Zero) (refl≤ n) Refl)
monotonicity≤- n m Zero (Suc l) _ () 
monotonicity≤- n m (Suc k) (Suc l) proofn≤m proofk'≥l' = trans≤ {n - (Suc k)} {pred (m - l)} {m - (Suc l)} proofn-k'≤predofm-l proofpredofm-l≤m-l' where
  proofn-k'≤predofm-l = trans≤ {n - (Suc k)} {pred (n - k)} {pred (m - l)} proofn-k'≤predofn-k proofpredofn-k≤predofm-l where
    proofn-k'≤predofn-k = ==ℕto≤ {n - (Suc k)} {pred (n - k)} (==to==ℕ {n - (Suc k)} {pred (n - k)} (NMinusSucMisPredNMinusM n k))
    proofpredofn-k≤predofm-l = monotonicityPred (n - k) (m - l) (monotonicity≤- n m k l proofn≤m proofk'≥l')
  proofpredofm-l≤m-l' = ==ℕto≤ {pred (m - l)} {m - (Suc l)} (==to==ℕ  {pred (m - l)} {m - (Suc l)} (==sym (NMinusSucMisPredNMinusM m l)))

Suc[pred[n-m]]is[n-m]for[n>m] : (n m : ℕ) → (n > m) == True → Suc (pred (n - m)) == n - m
Suc[pred[n-m]]is[n-m]for[n>m] Zero _ ()
Suc[pred[n-m]]is[n-m]for[n>m] (Suc n) Zero _ = Refl
Suc[pred[n-m]]is[n-m]for[n>m] (Suc n) (Suc m) proofn>m = Suc[pred[n-m]]is[n-m]for[n>m] n m proofn>m

[Sucn]-misSuc[n-m]for[n≥m] : (n m : ℕ) → (n ≥ m) == True → (Suc n) - m == Suc (n - m)
[Sucn]-misSuc[n-m]for[n≥m] n Zero _ = Refl
[Sucn]-misSuc[n-m]for[n≥m] n (Suc m) proofn≥Sucm = ==trans proof[n-m]isSuc[pred[n-m]] proofSuc[pred[n-m]]isSuc[n-[Sucm]] where
  proof[n-m]isSuc[pred[n-m]] = ==sym (Suc[pred[n-m]]is[n-m]for[n>m] n m proofn≥Sucm)
  proofSuc[pred[n-m]]isSuc[n-[Sucm]] = app Suc (==sym (NMinusSucMisPredNMinusM n m))

[n+m]-lisn+[m-l]for[m≥l] : (n m l : ℕ) → (m ≥ l) == True → ((n + m) - l) == (n + (m - l))
[n+m]-lisn+[m-l]for[m≥l] n m Zero _ = Refl
[n+m]-lisn+[m-l]for[m≥l] n Zero (Suc l) ()
[n+m]-lisn+[m-l]for[m≥l] n (Suc m) (Suc l) proofSucm≥Sucl = ==trans proof[n+[Sucm]]-[Sucl]isn+[m-l] (==sym (proofn+[[Sucm-Sucl]]isn+[m-l])) where
  proof[n+[Sucm]]-[Sucl]isn+[m-l] = ==trans proof[n+[Sucm]]-[Sucl]ispred[n+[[Sucm]-l]] proofpred[n+[[Sucm]-l]]ispred[n+[Suc[m-l]]] where
    proof[n+[Sucm]]-[Sucl]ispred[n+[[Sucm]-l]] = ==trans (NMinusSucMisPredNMinusM (n + (Suc m)) l) (app pred ([n+m]-lisn+[m-l]for[m≥l] n (Suc m) l proofSucm≥l)) where
      proofSucm≥l = trans≤ {l} {Suc l} {Suc m} proofl≤Sucl proofSucm≥Sucl where
        proofl≤Sucl = monotonicity≤+ l l Zero (Suc Zero) (refl≤ l) Refl
    proofpred[n+[[Sucm]-l]]ispred[n+[Suc[m-l]]] = app pred (app (_+_ n) ([Sucn]-misSuc[n-m]for[n≥m] m l proofSucm≥Sucl)) 
  proofn+[[Sucm-Sucl]]isn+[m-l] = ==trans proofn+[[Sucm-Sucl]]isn+pred[[Sucm-l]] proofn+pred[[Sucm-l]]isn+pred[Suc[m-l]] where
    proofn+[[Sucm-Sucl]]isn+pred[[Sucm-l]] = app (_+_ n) (NMinusSucMisPredNMinusM (Suc m) l)
    proofn+pred[[Sucm-l]]isn+pred[Suc[m-l]] = app (_+_ n) (app pred ([Sucn]-misSuc[n-m]for[n≥m] m l proofSucm≥Sucl))
