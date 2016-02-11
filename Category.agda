module Category where

open import TypeConstructions
open import PropositionalEquality
open import Agda.Primitive

Cat : {n : Level} → Set (lsuc n)
Cat {n} = (Set n) Σ (λ Ob -> ( ((a b : Ob) → (Set n)) Σ λ Hom -> ( ((a : Ob) → Hom a a) Σ 
                                                                       λ id -> ((a b c : Ob) → (f : Hom b c) → (g : Hom a b) → Hom a c) Σ
                                            λ comp -> ((a b : Ob) → (f : Hom a b) → (comp (id b) f == f) × (comp f (id a) == f)) ×
                                                      ((a b c d : Ob) → (f : Hom c d) → (g : Hom b c) → (h : Hom a b) →
                                                         comp f (comp g h) == comp (comp f g) h
                                                      )
                                                          
                                                          
                                                      )
                     )
            )
