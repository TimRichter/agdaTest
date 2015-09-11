module Algebr where

open import PropositionalEquality
open import TypeConstructions


IsSemigroup : (S : Set) → (S → S → S) → Set
IsSemigroup S op = (x y z : S) → (op x (op y z)) == (op (op x y) z)

AssociativeSemigroupOp : {S : Set} → {op : S → S → S} →
                         IsSemigroup S op →
                         (x y z : S) → (op x (op y z)) == (op (op x y) z)
AssociativeSemigroupOp p = p

IsMonoid : (M : Set) → (M → M → M) → Set
IsMonoid M op = IsSemigroup M op ×                  --
                (M Σ λ (e : M) -> (n : M) → op n e == n × op e n == n)

Monoid→Semigroup : {M : Set} → {op : M → M → M} →
                     IsMonoid M op →
                     IsSemigroup M op
Monoid→Semigroup = pr1×

HasUnitMonoidOp : {M : Set} → {op : M → M → M} →
                  IsMonoid M op →
                  (M Σ λ (e : M) -> (n : M) → op n e == n × op e n == n)
HasUnitMonoidOp = pr2×

AssociativeMonoidOp : {M : Set} → {op : M → M → M} →
                      IsMonoid M op →
                      (x y z : M) →
                      (op x (op y z)) == (op (op x y) z)

AssociativeMonoidOp {M} {op} proofIsMonoid =
                      AssociativeSemigroupOp {M} {op} (Monoid→Semigroup proofIsMonoid)

