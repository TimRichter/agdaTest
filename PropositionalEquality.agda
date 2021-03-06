{-# OPTIONS --without-K #-}

module PropositionalEquality where

--open import TypeConstructions public
open import TypeConstructions

data _==_ {A : Set} (x : A) : A → Set where
  Refl : x == x

infix 5 _==_

{----------- contents --------------------------

refl : {A : Set} → (x : A) → x == x

{- path induction principle -}
pI : {A : Set} → (P : {x y : A} → x == y → Set) →
    (d : (x : A) → P (refl x)) →
    {x y : A} → (p : x == y) → P p

{- based path induction -}
bpI : {A : Set} → {a : A} → 
      (P : {x : A} → a == x → Set) →
      (d : P (refl a)) →
      {x : A} → (p : a == x) → P p

{- == is an equivalence relation -}
refl== : {A : Set} → {x : A} → (x == x)
sym== : {A : Set} → {x y : A} → (x == y) → (y == x)
trans== : {A : Set} → {x y z : A}  → (x == y) → (y == z) → (x == z)

{- equational reasoning -}
_==⟨_⟩_ : {A : Set} → (x : A) → {y z : A} → x == y → y == z → x == z
_qed : {A : Set} → (x : A) → x == x
bydef : {A : Set} → {x : A} → x == x

{- contractability -}
isContr : Set → Set

{- Refl is left unit -}
leftUnit==Refl : {A : Set} → {x y : A} → (p : x == y) →
                 trans== (refl x) p == p

{- Refl is right unit -}
rightUnit==Refl : {A : Set} → {x y : A} → (p : x == y) →
                  trans== p (refl y) == p

{- transport -}
transp : {A : Set} → (B : A → Set) →
         {x y : A} → x == y → B x → B y

{- transporting along refl is identity -}
transpRefl : {A : Set} → (B : A → Set) →
             {x : A} → (b : B x) →
             transp B (refl x) b == b

{- applying functions to equalities -}
ap : {A B : Set} → (f : A -> B) → {x y : A} → (x == y) → (f x == f y)

{- (ap f) maps refl to refl -}
apRefl : {A B : Set} → (f : A → B) → (x : A) → ap f (refl x) == refl (f x)

{- (ap id) is id -}
apId : {A : Set} → {x y : A} → (p : x == y) → ap id p == p

{- applying dependent functions to equalities -}
apd : {A : Set} → {B : A → Set} → (f : (x : A) -> B x) → {x y : A} → (x == y) → (f x == f y)

{- apd maps refl to refl -}
apdRefl : {A : Set} → {B : A → Set} → (f : (x : A) → B x) →
          (x : A) → apd f (refl x) == refl (f x)

{- characterization of equality in Σ types -}
equalityΣ : {A : Set} → {B : A → Set} →
            (ω1 ω2 : A Σ B) →
            ((pr1Σ ω1 == pr1Σ ω2) Σ λ p -> transp B p (pr2Σ ω1) == pr2Σ ω2) →
            ω1 == ω2

{- transporting along refl is identity -} 
transpRefl : {A : Set} → (B : A → Set) →
             {x : A} → (b : B x) →
             transp B (refl x) b == b 

{- Lemma 2.11.2 a HoTT-book -}
transpEqLemma : {A : Set} → {a x1 x2 : A} →
                (p : x1 == x2) → (q : a == x1) →
                transp (λ (x : A) -> a == x) p q == trans== q p

{- Lemma 2.11.2 b HoTT-book -}
transpEqLemmb : {A : Set} → {a x1 x2 : A} →
                (p : x1 == x2) → (q : x1 == a) →
                transp (λ x -> x == a) p q == trans== (sym== p) q

{- Lemma 2.11.2 c HoTT-book -}
transpEqLemmc : {A : Set} → {x1 x2 : A} →
                (p : x1 == x2) → (q : x1 == x1) →
                transp (λ x -> x == x) p q == trans== (trans== (sym== p) q) p

{- Lemma 2.11.4 HoTT-book -}
transpEqDepFun : {A : Set} → {B : A → Set} → (f g : (x : A) → B x) →
                 {a0 a1 : A} → (p : a0 == a1) → (q : f a0 == g a0) →
                 transp (λ x -> f x == g x) p q ==  (apd f p)≀ · ap (transp B p) q · apd g p

{- Lemma 3.11.8 -}
pathSpaceContractible : {A : Set} → (a : A) →
              isContr (A Σ λ x -> a == x)

{- no longer provable (--without-K)
uip : {A : Set} → {x y : A} → (p q : x == y) → p == q
uip Refl Refl = Refl
-}

------------------------------------------------}
refl : {A : Set} → (x : A) → x == x
refl x = Refl

{- path induction principle -}
pI : {A : Set} → (P : {x y : A} → x == y → Set) →
    (d : (x : A) → P (refl x)) →
    {x y : A} → (p : x == y) → P p
pI P d {x} {.x} Refl = d x


{- == is an equivalence relation -}
refl== : {A : Set} → {x : A} → (x == x)
refl== {_} {x} = refl x

sym== : {A : Set} → {x y : A} → (x == y) → (y == x)
sym== {A} = pI P d where
  P : {x y : A} → (x == y) → Set
  P {x} {y} _ = y == x
  d : (x : A) → P (refl x)
  d x = refl x

{- symbol for inverse path: \wr -}
_≀ : {A : Set} → {x y : A} → (x == y) → (y == x)
_≀ = sym==

infix 8 _≀

trans== : {A : Set} → {x y z : A}  → (x == y) → (y == z) → (x == z)
trans== {A} {x} {y} {z} p = (pI P' d') {x} {y} p {z} where
   P' : {x y : A} → x == y → Set
   P' {x} {y} p = {z : A} → y == z → x == z
   d' : (x : A) → P' {x} {x} (refl x)
   d' x = id

{- symbol for path concatenation: \cdot -}
_·_ : {A : Set} → {x y z : A}  → (x == y) → (y == z) → (x == z)
_·_  = trans== 

infixr 7 _·_

{- for equational reasoning -}
_==⟨_⟩_ : {A : Set} → (x : A) → {y z : A} → x == y → y == z → x == z
x ==⟨ p ⟩ q = trans== p q

infixr 2 _==⟨_⟩_

_qed : {A : Set} → (x : A) → x == x
x qed = refl== {_} {x}

infixr 2 _qed

bydef : {A : Set} → {x : A} → x == x
bydef {A} {x} = refl x

{- transport -}
transp : {A : Set} → (B : A → Set) →
         {x y : A} → x == y → B x → B y
transp {A} B = pI P d where
   P : {x y : A} → (x == y) → Set
   P {x} {y} _ = B x → B y
   d : (x : A) → P (refl x)
   d x = id

{- transporting along refl is identity -}
transpRefl : {A : Set} → (B : A → Set) →
             {x : A} → (b : B x) →
             transp B (refl x) b == b
transpRefl B b = (refl b)

{- applying functions to equalities -}
ap : {A B : Set} → (f : A → B) → {x y : A} → (x == y) → (f x == f y)
ap {A} {B} f = pI P d where
  P : {x y : A} → x == y → Set
  P {x} {y} p = f x == f y
  d : (x : A) → P {x} {x} (refl x)
  d x = refl (f x)

{- (ap f) maps refl to refl -}
apRefl : {A B : Set} → (f : A → B) → (x : A) → ap f (refl x) == refl (f x)
apRefl {A} {B} f x =
  ap f (refl x) ==⟨ refl (refl (f x)) ⟩ refl (f x) qed

{- (ap id) is id -}
apId : {A : Set} → {x y : A} → (p : x == y) → ap id p == p
apId {A} = pI P d where
  P : {x y : A} → x == y → Set
  P p = ap id p == p
  d : (x : A) → P (refl x)
  d x =
    ap id (refl x) ==⟨ refl (refl x) ⟩ (refl x) qed

{- applying dependent functions to equalities -}
apd : {A : Set} → {B : A → Set} → (f : (x : A) → B x) →
      {x y : A} → (p : x == y) → (transp B p (f x) == f y)
apd {A} {B} f = pI P d where
  P : {x y : A} → x == y → Set
  P {x} {y} p = transp B p (f x) == f y
  d : (x : A) → P {x} {x} (refl x)
  d x = (transp B (refl x) (f x)) ==⟨ transpRefl B (f x) ⟩ (f x) qed

{- apd maps refl to refl -}
apdRefl : {A : Set} → {B : A → Set} → (f : (x : A) → B x) →
          (x : A) → apd f (refl x) == refl (f x)
apdRefl {A} {B} f x =
  apd f (refl x) ==⟨ refl (refl (f x)) ⟩ refl (f x) qed

leftUnit==Refl : {A : Set} → {x y : A} → (p : x == y) →
                 trans== (refl x) p == p
leftUnit==Refl {A} p = pI P d p where
  P : {x y : A} → x == y → Set
  P {x} p = trans== (refl x) p == p
  d : (x : A) → P (refl x)
  d x = refl (refl x)

rightUnit==Refl : {A : Set} → {x y : A} → (p : x == y) →
                  trans== p (refl y) == p
rightUnit==Refl {A} p = pI P d p where
  P : {x y : A} → x == y → Set
  P {_} {y} p = trans== p (refl y) == p
  d : (x : A) → P (refl x)
  d x = refl (refl x)

{- Lemma 2.11.2 a HoTT-book -}

transpEqLemma : {A : Set} → {a x1 x2 : A} →
                (p : x1 == x2) → (q : a == x1) →
                transp (λ (x : A) -> a == x) p q == trans== q p
transpEqLemma {A} {a} = pI P d where
  P : {x1 x2 : A} → x1 == x2 → Set
  P {x1} {x2} p = (q : a == x1) →
    transp (λ (x : A) -> a == x) p q == trans== q p
  d : (x : A) → P (refl x)
  d x q =
    (transp (λ (x : A) -> a == x) (refl x) q)
      ==⟨ transpRefl (λ (x : A) -> a == x) q ⟩
    q
      ==⟨ sym== (rightUnit==Refl q) ⟩
    (trans== q (refl x))
      qed

{- contractability -}

isContr : Set → Set
isContr A = A Σ (λ a -> (a' : A) → a == a')  

{- characterization of equality in Σ types -}

equalityΣ : {A : Set} → {B : A → Set} →
            (ω1 ω2 : A Σ B) →
            ((pr1Σ ω1 == pr1Σ ω2) Σ λ p -> transp B p (pr2Σ ω1) == pr2Σ ω2) →
            ω1 == ω2
equalityΣ {A} {B} << a1 , b1 >> << a2 , b2 >> << p , q >> =
   h2 {A} B {a1} {a2} p b1 b2 q where
   h1 : {A : Set} → (B : A → Set) → (a : A) →
        (b1 b2 : B a) → transp B (refl a) b1 == b2 →
        explicitSigma B a b1 == << a , b2 >>
   h1 B a b1 b2 p = pI P d {b1} {b2} (trans== (sym== (transpRefl B b1)) p) where
     P : {b1 b2 : B a} → b1 == b2 → Set
     P {b1} {b2} _ = << a , b1 >> == << a , b2 >>
     d : (b : B a) → P (refl b)
     d b = refl << a , b >>
   h2 : {A : Set} → (B : A → Set) →
        {a1 a2 : A} → (p : a1 == a2) →
        (b1 : B a1) → (b2 : B a2) →
        transp B p b1 == b2 → explicitSigma B a1 b1 == << a2 , b2 >>
   h2 {A} B = pI P d where
     P : {a1 a2 : A} → a1 == a2 → Set
     P {a1} {a2} p = (b1 : B a1) → (b2 : B a2) →
                     transp B p b1 == b2 →
                     explicitSigma B a1 b1 == << a2 , b2 >>
     d : (a : A) → P (refl a)
     d a = h1 B a
   
{- Lemma 3.11.8 -}

pathSpaceContractible : {A : Set} → (a : A) →
              isContr (A Σ λ x -> a == x)
pathSpaceContractible {A} a = << << a , refl a >> , f >> where
  f : (ω : A Σ λ x -> a == x) → << a , refl a >> == ω
  f << x , p >> =
    equalityΣ << a , refl a >> << x , p >> << p , q >> where
    q : transp (λ x -> a == x) p (refl a) == p
    q =
      transp (λ x -> a == x) p (refl a)
       ==⟨ transpEqLemma p (refl a) ⟩
      trans== (refl a) p
       ==⟨ leftUnit==Refl p ⟩
      p
       qed

{- based path induction -}

bpI : {A : Set} → {a : A} → 
      (P : {x : A} → a == x → Set) →
      (d : P (refl a)) →
      {x : A} → (p : a == x) → P p
bpI {A} {a} P d {x} p =
   f {A} {a} P' d << x , p >>  where
   P' : (A Σ λ x -> a == x) → Set
   P' << x , p >> =  P {x} p
   f : {A : Set} → {a : A} →
       (P' : (A Σ λ x -> a == x) → Set) →
       (d : P' << a , (refl a) >> ) →
       (ω : (A Σ λ x -> a == x)) →
       P' ω
   f {A} {a} P' d ω = transp P' pathToω d where
     pathToω : << a , refl a >> == ω
     pathToω =
       << a , refl a >>
        ==⟨ bydef ⟩
       pr1Σ (pathSpaceContractible a)
        ==⟨ pr2Σ (pathSpaceContractible a) ω ⟩
       ω
        qed


{- Lemma 2.11.2 b HoTT-book -}

transpEqLemmb : {A : Set} → {a x1 x2 : A} →
                (p : x1 == x2) → (q : x1 == a) →
                transp (λ x -> x == a) p q == trans== (sym== p) q
transpEqLemmb {A} {a} {x1} =
  bpI {A} {x1} P d where
  P : {x2 : A} → x1 == x2 → Set
  P p = (q : x1 == a) → transp (λ x -> x == a) p q == trans== (sym== p) q 
  d : P (refl x1)
  d q =
    transp (λ x -> x == a) (refl x1) q
     ==⟨ transpRefl (λ x -> x == a) q ⟩
    q
     ==⟨ sym== (leftUnit==Refl q) ⟩
    trans== (refl x1) q
     ==⟨ bydef ⟩
    trans== (sym== (refl x1)) q
     qed

  
{- Lemma 2.11.2 c HoTT-book -}

transpEqLemmc : {A : Set} → {x1 x2 : A} →
                (p : x1 == x2) → (q : x1 == x1) →
                transp (λ x -> x == x) p q == trans== (trans== (sym== p) q) p
transpEqLemmc {A} {x1} =
  bpI {A} {x1} P d where
  P : {x2 : A} → x1 == x2 → Set
  P p = (q : x1 == x1) → transp (λ x -> x == x) p q == trans== (trans== (sym== p) q) p 
  d : P (refl x1)
  d q =
    transp (λ x -> x == x) (refl x1) q
     ==⟨ transpRefl (λ x -> x == x) q ⟩
    q
     ==⟨ sym== (leftUnit==Refl q) ⟩
    trans== (refl x1) q
     ==⟨ bydef ⟩
    trans== (sym== (refl x1)) q
     ==⟨ sym== (rightUnit==Refl (trans== (sym== (refl x1)) q)) ⟩
    trans== (trans== (sym== (refl x1)) q) (refl x1)
     qed


{- Lemma 2.11.4 HoTT-book -}

transpEqDepFun : {A : Set} → {B : A → Set} → (f g : (x : A) → B x) →
                 {a0 a1 : A} → (p : a0 == a1) → (q : f a0 == g a0) →
                 transp (λ x -> f x == g x) p q ==  (apd f p)≀ · ap (transp B p) q · apd g p
transpEqDepFun {A} {B} f g = pI P d where
  P : {a0 a1 : A} → a0 == a1 → Set
  P {a0} {a1} p = (q : f a0 == g a0) → transp (λ x -> f x == g x) p q ==  (apd f p)≀ · ap (transp B p) q · apd g p
  d : (a0 : A) → P (refl a0)
  d a0 q =
    transp (λ x -> f x == g x) (refl a0) q
    ==⟨ transpRefl (λ x -> f x == g x) q ⟩
    q
    ==⟨ sym== (apId q) ⟩
    ap id q
    ==⟨ (rightUnit==Refl (ap id q))≀ ⟩
    (ap id q) · refl (g a0)
    ==⟨ ap (trans== (ap id q)) (apdRefl g a0)≀ ⟩
    (ap id q) · apd g (refl a0)
    ==⟨ (leftUnit==Refl ((ap id q) · apd g (refl a0)))≀ ⟩
    refl (f a0) · (ap id q) · apd g (refl a0)
    ==⟨ bydef ⟩
    (refl (f a0))≀ · (ap id q) · apd g (refl a0)
    ==⟨ ap (λ π -> (π)≀ · (ap id q) · apd g (refl a0)) (apdRefl f a0)≀ ⟩
    (apd f (refl a0))≀ · (ap id q) · apd g (refl a0)
    ==⟨ bydef ⟩
    (apd f (refl a0))≀ · (ap (transp B (refl a0)) q) · apd g (refl a0)
    qed




