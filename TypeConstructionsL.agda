module TypeConstructionsL where

-- module TypeConstructions with explicit Level handling

open import Agda.Primitive

-- empty type (see Data.Empty)


{- Identitäten -}
id : {n : Level} -> {A : Set n} → A → A
id x = x  

{- Leerer Typ; daher ohne Konstruktoren -}
data ⊥ (n : Level) : Set n where

{- Ex falso quodlibet  -}
⊥-elim : {n : Level} → {A : Set n} → ⊥ n → A
⊥-elim ()

data _×_ {n m : Level} (A : Set n) (B : Set m) : Set (n ⊔ m) where
  <_,_> : A → B → A × B

infixr 4 _×_

pr1× : {n m : Level} → {A : Set n} → {B : Set m} → A × B → A
pr1× < a , b > = a

pr2× : {n m : Level} → {A : Set n} → {B : Set m} → A × B → B
pr2× < a , b > = b

data _+_ {n m : Level} (A : Set n) (B : Set m) : Set (n ⊔ m) where
  Inl : A → A + B
  Inr : B → A + B

infixr 3 _+_

data _Σ_ {n m : Level} (A : Set n) (B : A →  Set m) : Set (n ⊔ m)   where
  <<_,_>> : (a : A) → (B a) → (A Σ B) 

infixr 2 _Σ_ 

pr1Σ : {n m : Level} → {A : Set n} → {B : A → Set m} → (A Σ B) → A
pr1Σ << a , _ >> = a

pr2Σ : {n m : Level} → {A : Set n} → {B : A → Set m} → (ω : (A Σ B)) → B (pr1Σ ω)
pr2Σ << a , b >> = b

explicitSigma : {n m : Level} → {A : Set n} -> (B : A → Set m) → (a : A) → B a → (A Σ B)
explicitSigma B a b = << a , b >>

{- Nur mal zum Nachdenken der Selbstbezug
data _→eigenheimer_ (A B : Set) : Set where
  Funktion_ : (A → B) → (A →eigenheimer B)

data _Π_ (A : Set) (B : A → Set) : Set where
  λ : ((a : A) → B a) → A Π B   -- sollte das λ heissen?  
-}


{- Funktionenkomposition -}
_∘_ : {n m l : Level} →
      {A : Set n} → {B : Set m} → {C : Set l} →
      (g : B → C) → (f : A → B) → (A → C)
(g ∘ f) a = g (f a)

infixr 7 _∘_


_●_ : {n m l : Level} →
      {A : Set n} → {B : A → Set m} → {C : {a : A} → B a → Set l} →
       (g : {a : A} → (b : B a) → C b ) →  (f : (a : A) → B a) → ((a : A) → C (f a))
(g ● f) a = g ( f a )

infixr 7 _●_


_◐_ : {n m : Level} →
      {A B : Set n} → {C : B → Set m} →
      (g : (b : B) → C b ) → (f : A → B ) → ((a : A) → C (f a))
(g ◐ f) a = g ( f a )

infixr 7 _◐_

_◑_ : {n m l : Level} →
      {A : Set n} → {B : A → Set m} → {C : A → Set l} → 
      (g : {a : A} → B a → C a ) → (f : (a : A) → B a ) → ((a : A) → C a)
(g ◑ f) a = g ( f a )

infixr 7 _◑_


{- Negation eines Typs -}
¬_ : {n : Level} → Set n → Set n
¬_ {n} P = P → ⊥ n

infix 8 ¬_

{- Dec A als Typ, dessen Elemente allesamt Beweise von A oder Widerlegungen von A sind -}
data Dec {n : Level} (A : Set n) : Set n where
  Yes : ( a :   A) → Dec A
  No  : (¬a : ¬ A) → Dec A

