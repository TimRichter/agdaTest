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

sym== : {A : Set} → {x y : A} → (x == y) → (y == x)
sym== Refl = Refl

trans== : {A : Set} → {x y z : A}  → (x == y) → (y == z) → (x == z)
trans== Refl Refl = Refl

app : {A B : Set} → (f : A -> B) → {x y : A} → (x == y) → (f x == f y)
app f Refl = Refl

transp : {A : Set} → (B : A → Set) → {x y : A} → x == y → B x → B y
transp B {x} {.x} Refl pr[Bx] = pr[Bx]

{- no longer provable (--without-K)
uip : {A : Set} → {x y : A} → (p q : x == y) → p == q
uip Refl Refl = Refl
-}

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

typecheckt noch nicht...

-}
