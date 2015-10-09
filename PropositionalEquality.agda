{-# OPTIONS --without-K #-}

module PropositionalEquality where

open import TypeConstructions public

data _==_ {A : Set} (x : A) : A → Set where
  Refl : x == x

infix 5 _==_

refl : {A : Set} → (x : A) → x == x
refl x = Refl

{- path induction principle -}
pI : {A : Set} → (P : {x y : A} → x == y → Set) →
    (d : (x : A) → P (refl x)) →
    {x y : A} → (p : x == y) → P p
pI P d {x} {.x} Refl = d x

{- based path induction -}
{-
bpI : {A : Set} → {a : A} → (P : {x : A} → a == x → Set) →
    (d : P Refl) →
    {x : A} → (p : a == x) → P p
bpI P d Refl = d
-}

{- Klappt nicht wegen universe levels
bpI {A} {a} P d {x} p = f {a} {x} p P d where
    P' : {x y : A} → (x == y) → Set
    P' {x} p = (Q : {z : A} → (x == z) → Set) → Q Refl → Q p
    d' : (x : A) → P' {x} Refl
    d' x _ r = r
    f : {x y : A} → (p : x == y) →
               (Q : {z : A} → (x == z) → Set) →
               Q Refl → Q p
    f = pI P' d'
-}

sym== : {A : Set} → {x y : A} → (x == y) → (y == x)
sym== {A} = pI P d where
  P : {x y : A} → (x == y) → Set
  P {x} {y} _ = y == x
  d : (x : A) → P (refl x)
  d x = refl x

trans== : {A : Set} → {x y z : A}  → (x == y) → (y == z) → (x == z)
trans== {A} {x} {y} {z} p = (pI P' d') {x} {y} p {z} where
   P' : {x y : A} → x == y → Set
   P' {x} {y} p = {z : A} → y == z → x == z
   d' : (x : A) → P' {x} {x} (refl x)
   d' x = id

{- for equational reasoning -}
_==⟨_⟩_ : {A : Set} → (x : A) → {y z : A} → x == y → y == z → x == z
x ==⟨ p ⟩ q = trans== p q

infixr 2 _==⟨_⟩_

_qed : {A : Set} → (x : A) → x == x
x qed = refl x

infixr 2 _qed

bydef : {A : Set} → {x : A} → x == x
bydef {A} {x} = refl x


{- applying functions to equalities -}
app : {A B : Set} → (f : A -> B) → {x y : A} → (x == y) → (f x == f y)
app {A} {B} f = pI P d where
  P : {x y : A} → x == y → Set
  P {x} {y} p = f x == f y
  d : (x : A) → P {x} {x} (refl x)
  d x = refl (f x)

{- transport -}
transp : {A : Set} → (B : A → Set) → {x y : A} → x == y → B x → B y
transp {A} B = pI P d where
   P : {x y : A} → (x == y) → Set
   P {x} {y} _ = B x → B y
   d : (x : A) → P (refl x)
   d x = id

transpRefl : {A : Set} → (B : A → Set) → {x : A} → (b : B x) → transp B (refl x) b == b
transpRefl B b = (refl b)

{- no longer provable (--without-K)
uip : {A : Set} → {x y : A} → (p q : x == y) → p == q
uip Refl Refl = Refl
-}

leftUnit==Refl : {A : Set} → {x y : A} → (p : x == y) → trans== Refl p == p
leftUnit==Refl {A} p = pI P d p where
  P : {x y : A} → x == y → Set
  P p = trans== Refl p == p
  d : (x : A) → P Refl
  d x = Refl

rightUnit==Refl : {A : Set} → {x y : A} → (p : x == y) → trans== p Refl == p
rightUnit==Refl {A} p = pI P d p where
  P : {x y : A} → x == y → Set
  P p = trans== p Refl == p
  d : (x : A) → P Refl
  d x = Refl

{- Lemma 2.11.2 HoTT-book -}

transpEqLemma : {A : Set} → {a x1 x2 : A} → (p : x1 == x2) →
  (q : a == x1) → transp (λ (x : A) -> a == x) p q == trans== q p
transpEqLemma {A} {a} = pI P d where
  P : {x1 x2 : A} → x1 == x2 → Set
  P {x1} {x2} p = (q : a == x1) → transp (λ (x : A) -> a == x) p q == trans== q p
  d : (x : A) → P (refl x)
  d x q =
    (transp (λ (x : A) -> a == x) (refl x) q)  ==⟨ transpRefl (λ (x : A) -> a == x) q ⟩
    q                                          ==⟨ sym== (rightUnit==Refl q) ⟩
    (trans== q (refl x))                       qed


{-
    bpI {A} {a} P d {x1} q p where
    P : {x : A} → a == x → Set
    P {x} q = (p : x == x2) → transp (λ (y : A) -> a == y) p q == trans== q p
    d : P Refl
    d p = Refl
-}

{- contractability -}

isContr : Set → Set
isContr A = A Σ (λ a -> (a' : A) → a == a')  

{- towards Lemma 3.11.8 -}

{- characterization of equality in Σ types -}

equalityΣ : {A : Set} → {B : A → Set} → (ω1 ω2 : A Σ B) →
   (pr1Σ ω1 == pr1Σ ω2 Σ λ p -> transp B p (pr2Σ ω1) == pr2Σ ω2) → ω1 == ω2
equalityΣ {A} {B} << a1 , b1 >> << a2 , b2 >> << p , q >> =
   h2 {A} B {a1} {a2} p b1 b2 q where
   h1 : {A : Set} → (B : A → Set) → (a : A) →
    (b1 b2 : B a) → transp B (refl a) b1 == b2 → explicitSigma B a b1 == << a , b2 >>
   h1 B a b1 b2 p = pI P d {b1} {b2} (trans== (sym== (transpRefl B b1)) p) where
     P : {b1 b2 : B a} → b1 == b2 → Set
     P {b1} {b2} _ = << a , b1 >> == << a , b2 >>
     d : (b : B a) → P (refl b)
     d b = refl << a , b >>
   h2 : {A : Set} → (B : A → Set) → {a1 a2 : A} → (p : a1 == a2) →
     (b1 : B a1) → (b2 : B a2) → transp B p b1 == b2 → explicitSigma B a1 b1 == << a2 , b2 >>
   h2 {A} B = pI P d where
     P : {a1 a2 : A} → a1 == a2 → Set
     P {a1} {a2} p = (b1 : B a1) → (b2 : B a2) → transp B p b1 == b2 →
       explicitSigma B a1 b1 == << a2 , b2 >>
     d : (a : A) → P (refl a)
     d a = h1 B a
   
