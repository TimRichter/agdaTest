module Category where

open import TypeConstructionsL
open import PropositionalEqualityL
open import Agda.Primitive

data nat {n : Level} : Set n where
  Z : nat
  S : nat → nat

Cat : {n m : Level} → Set ((lsuc n) ⊔ (lsuc m))
Cat {n} {m} = (Set n) Σ λ Ob -> (
 ((a b : Ob) → (Set m)) Σ λ Hom -> (
  ((a : Ob) → Hom a a) Σ λ idC -> (
   ((a b c : Ob) → (f : Hom b c) → (g : Hom a b) → Hom a c) Σ λ comp -> (
    ((a b : Ob) → (f : Hom a b) → (comp a b b (idC b) f == f) × (comp a a b f (idC a) == f)) ×
     ((a b c d : Ob) → (f : Hom c d) → (g : Hom b c) → (h : Hom a b) → comp a c d f (comp a b c g h) == comp a b d (comp b c d f g) h)
                                                            ))))

