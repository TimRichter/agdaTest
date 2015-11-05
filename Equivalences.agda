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
                              g ∘ f ∼ id Σ (λ η -> f ∘ g ∼ id Σ (λ ε -> (x : A) → app f (η x) == ε (f x))))

{- coherences -}

lcoh : {A B : Set} → (f : A → B) → linv f → Set
lcoh {A} {B} f << g , η >> =  f ∘ g ∼ id Σ (λ ε -> (y : B) → app g (ε y) == η (g y))

rcoh : {A B : Set} → (f : A → B) → rinv f → Set
rcoh {A} {B} f << g , ε >> =  g ∘ f ∼ id Σ (λ η -> (x : A) → app f (η x) == ε (f x))




