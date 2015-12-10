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

ishae : {A B : Set} → (f : A → B) → Set
ishae {A} {B} f = (B → A) Σ (λ g ->
                              g ∘ f ∼ id Σ (λ η -> f ∘ g ∼ id Σ (λ ε -> (x : A) → ap f (η x) == ε (f x))))

isequiv : {A B : Set} → (f : A → B) → Set
isequiv = ishae

_≃_ : Set → Set → Set
A ≃ B = (A → B) Σ (λ f -> isequiv f)

{- coherences -}

lcoh : {A B : Set} → (f : A → B) → linv f → Set
lcoh {A} {B} f << g , η >> =  f ∘ g ∼ id Σ (λ ε -> (y : B) → ap g (ε y) == η (g y))

rcoh : {A B : Set} → (f : A → B) → rinv f → Set
rcoh {A} {B} f << g , ε >> =  g ∘ f ∼ id Σ (λ η -> (x : A) → ap f (η x) == ε (f x))

{- propositions -}

{- Äquivalnezrelation von allen Äquivalenzdefinitionen zeigen -}

transpEqEquiv : {A : Set} → {a0 a1 : A} → (p : a0 == a1) → (q : a0 == a0) → (r : a1 == a1)
                → transp (λ (x : A) -> x == x) p q == r ≃ q · p == p · r
transpEqEquiv...                
