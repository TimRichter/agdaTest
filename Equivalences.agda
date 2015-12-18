module Equivalences where

open import TypeConstructions
open import PropositionalEquality
 
{- homotopy of two functions -}

_∼_  : {A B : Set} → (f g : A → B) → Set
_∼_ {A} f g = (a : A) → f a == g a

infix 6 _∼_

{- logical equivalence and properties -}

_↔_ : (A B : Set) → Set
A ↔ B = (A → B) × (B → A)

infixr 1 _↔_

refl↔ : {A : Set} → A ↔ A
refl↔ {A} = < id , id >

symm↔ : {A B : Set} → A ↔ B → B ↔ A
symm↔ < f , g > = < g , f >

trans↔ : {A B C : Set} → A ↔ B → B ↔ C → A ↔ C
trans↔ < f1 , g1 > < f2 , g2 > = < f2 ∘ f1 , g1 ∘ g2 >

{- inverses -}

qinv : {A B : Set} → (f : A → B) → Set
qinv {A} {B} f = (B → A) Σ λ g -> g ∘ f ∼ id × f ∘ g ∼ id

linv : {A B : Set} → (f : A → B) → Set
linv {A} {B} f = (B → A) Σ (λ g -> g ∘ f ∼ id)

rinv : {A B : Set} → (f : A → B) → Set
rinv {A} {B} f = (B → A) Σ (λ h -> f ∘ h ∼ id)

biinv : {A B : Set} → (f : A → B) → Set
biinv f = linv f × rinv f

{- coherence -}

coherent : {A B : Set} → (f : A → B) → (g : B → A) →
           g ∘ f ∼ id → f ∘ g ∼ id → Set
coherent {A} f g η ε = (x : A) → ap f (η x) == ε (f x)

lcoh : {A B : Set} → (f : A → B) → linv f → Set
lcoh f << g , η >> = f ∘ g ∼ id Σ λ ε -> coherent g f ε η
{- lcoh {A} {B} f << g , η >> =  f ∘ g ∼ id Σ (λ ε -> (y : B) → ap g (ε y) == η (g y)) -}

rcoh : {A B : Set} → (f : A → B) → rinv f → Set
rcoh f << g , ε >> = g ∘ f ∼ id Σ λ η -> coherent f g η ε
{- rcoh {A} {B} f << g , ε >> =  g ∘ f ∼ id Σ (λ η -> (x : A) → ap f (η x) == ε (f x)) -}

{- half adjoint equivalence: -}
{- f is a half adjoint equivalence if it has a quasiinverse that 
   satisfies one coherence condition                                -}

ishae : {A B : Set} → (f : A → B) → Set
ishae {A} {B} f = qinv f Σ λ q -> coherent f (pr1Σ q) (pr1× (pr2Σ q)) (pr2× (pr2Σ q)) 

{-              = qinv f Σ λ << g , < η , ε > >> -> coherent f g η ε  -} 


isequiv : {A B : Set} → (f : A → B) → Set
isequiv = ishae

_≃_ : Set → Set → Set
A ≃ B = (A → B) Σ (λ f -> isequiv f)

{- propositions -}

{- Äquivalenzrelation von allen Äquivalenzdefinitionen zeigen -}

transpEqEquiv : {A : Set} → {a0 a1 : A} → (p : a0 == a1) → (q : a0 == a0) → (r : a1 == a1)
                → ( transp (λ (x : A) -> x == x) p q == r ) ≃ (q · p == p · r)
transpEqEquiv {A} = pI P d where
  P : {a0 a1 : A} → a0 == a1 → Set
  P {a0} {a1} p = (q : a0 == a0) → (r : a1 == a1)
                  → ( transp (λ (x : A) -> x == x) p q == r ) ≃ (q · p == p · r)
  d : (a : A) → (q : a == a) → (r : a == a) → ( q == r ) ≃ ( q · (refl a) == r )
  d a q r = transp (λ (q' : a == a) -> ( q == r ) ≃ ( q' == r)) (sym== (rightUnit==Refl q)) (d' a q r)
    where
      d' : (a : A) → (q : a == a) → (r : a == a) → ( q == r ) ≃ ( q == r )
      d' a q r = << id , << << id , < refl , refl > >> , (λ x -> refl (refl x)) >> >>

{- TODO :
   2.3.5, 2.3.8, 2.3.10, 2.3.11, Ex. 2.4.9, 2.6.4, Formel 2.9.4, Formel 2.9.5, 2.9.6, 2.9.7, 2.10.5 
   und transport in coproducts vor Kap. 2.13
-}
