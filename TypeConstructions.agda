module TypeConstructions where

-- empty type (see Data.Empty)


{- Identitäten -}
id : {A : Set} → A → A
id x = x  

{- Leerer Typ; daher ohne Konstruktoren -}
data ⊥ : Set where

{- Ex falso quodlibet  -}
⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

data _×_ (A B : Set) : Set where
  <_,_> : A → B → A × B

infixr 4 _×_

pr1× : {A B : Set} → A × B → A
pr1× < a , b > = a

pr2× : {A B : Set} → A × B → B
pr2× < a , b > = b

data _+_ (A B : Set) : Set where
  Inl : A → A + B
  Inr : B → A + B

infixr 3 _+_

data _Σ_ (A : Set) (B : A →  Set) : Set where
  <<_,_>> : (a : A) → (B a) → (A Σ B) 

infixr 2 _Σ_ 

pr1Σ : {A : Set} → {B : A → Set} → (A Σ B) → A
pr1Σ << a , _ >> = a

pr2Σ : {A : Set} → {B : A → Set} → (ω : (A Σ B)) → B (pr1Σ ω)
pr2Σ << a , b >> = b

explicitSigma : {A : Set} -> (B : A → Set) → (a : A) → B a → (A Σ B)
explicitSigma B a b = << a , b >>

{- Nur mal zum Nachdenken der Selbstbezug
data _→eigenheimer_ (A B : Set) : Set where
  Funktion_ : (A → B) → (A →eigenheimer B)

data _Π_ (A : Set) (B : A → Set) : Set where
  λ : ((a : A) → B a) → A Π B   -- sollte das λ heissen?  
-}


{- Funktionenkomposition -}
_∘_ : {A B C : Set} → (g : B → C) → (f : A → B) → (A → C)
(g ∘ f) a = g (f a)

infixr 7 _∘_


_●_ : {A : Set} → {B : A → Set} → {C : {a : A} → B a → Set} →
       (g : {a : A} → (b : B a) → C b ) →  (f : (a : A) → B a) → ((a : A) → C (f a))
(g ● f) a = g ( f a )

infixr 7 _●_


_◐_ : {A B : Set} → { C : B → Set } →
       (g : (b : B) → C b ) → (f : A → B ) → ((a : A) → C (f a))
(g ◐ f) a = g ( f a )

infixr 7 _◐_


_◑_ : {A : Set} → {B C : A → Set} → 
       (g : {a : A} → B a → C a ) → (f : (a : A) → B a ) → ((a : A) → C a)
(g ◑ f) a = g ( f a )

infixr 7 _◑_


{- Negation eines Typs -}
¬_ : Set → Set
¬ P = P → ⊥

infix 8 ¬_

{- Dec A als Typ, dessen Elemente allesamt Beweise von A oder Widerlegungen von A sind -}
data Dec (A : Set) : Set where
  Yes : ( a :   A) → Dec A
  No  : (¬a : ¬ A) → Dec A

