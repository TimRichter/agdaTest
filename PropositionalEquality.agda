{-# OPTIONS --without-K #-}

module PropositionalEquality where

open import TypeConstructions public

data _==_ {A : Set} (x : A) : A → Set where
  Refl : x == x

infix 5 _==_

refl : {A : Set} → (x : A) → x == x
refl x = Refl

{- for equational reasoning -}
_==⟨_⟩_ : {A : Set} → (x : A) → {y z : A} → x == y → y == z → x == z
x ==⟨ Refl ⟩ Refl = Refl

infixr 2 _==⟨_⟩_

_qed : {A : Set} → (x : A) → x == x
x qed = Refl

infixr 2 _qed

bydef : {A : Set} → {x : A} → x == x
bydef = Refl

{- path induction principle -}
pI : {A : Set} → (P : {x y : A} → x == y → Set) →
    (d : (x : A) → P Refl) →
    {x y : A} → (p : x == y) → P p
pI P d {x} {.x} Refl = d x

{- based path induction -}
bpI : {A : Set} → {a : A} → (P : {x : A} → a == x → Set) →
    (d : P Refl) →
    {x : A} → (p : a == x) → P p
bpI P d Refl = d

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
  d : (x : A) → P Refl
  d x = Refl

trans== : {A : Set} → {x y z : A}  → (x == y) → (y == z) → (x == z)
{- trans== Refl Refl = Refl -}
trans== {A} {x} {y} {z} p = (pI P' d') {x} {y} p {z} where
   P' : {x y : A} → x == y → Set
   P' p = {z : A} → y == z → x == z
   d' : (x : A) → P' {x} {x} Refl
   d' x = id  {- das geht nicht? warum nicht? -}

app : {A B : Set} → (f : A -> B) → {x y : A} → (x == y) → (f x == f y)
app f Refl = Refl

transp : {A : Set} → (B : A → Set) → {x y : A} → x == y → B x → B y
transp {A} B = pI P d where
   P : {x y : A} → (x == y) → Set
   P {x} {y} _ = B x → B y
   d : (x : A) → P Refl
   d x = id

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
{-
transpEqLemma : {A : Set} → {a x1 x2 : A} → (p : x1 == x2) →
    (q : a == x1) → transp (λ (x : A) -> a == x) p q == trans== q p
transpEqLemma {A} {a} {x1} {x2} p q =
    bpI {A} {a} P d {x1} q p where
    P : {x : A} → a == x → Set
    P {x} q = (p : x == x2) → transp (λ (y : A) -> a == y) p q == trans== q p
    d : P Refl
    d p = Refl
-}



