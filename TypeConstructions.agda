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

pr1× : {A B : Set} → A × B → A
pr1× < a , b > = a

pr2× : {A B : Set} → A × B → B
pr2× < a , b > = b

data _+Set_ (A B : Set) : Set where
  Inl : A → A +Set B
  Inr : B → A +Set B

data _Σ_ (A : Set) (B : A →  Set) : Set where
  <<_,_>> : (a : A) → (B a) → (A Σ B)

pr1Σ : {A : Set} → {B : A → Set} → (A Σ B) → A
pr1Σ << a , _ >> = a

pr2Σ : {A : Set} → {B : A → Set} → (ω : (A Σ B)) → B (pr1Σ ω)
pr2Σ << a , b >> = b

{- Nur mal zum Nachdenken der Selbstbezug
data _→eigenheimer_ (A B : Set) : Set where
  Funktion_ : (A → B) → (A →eigenheimer B)

data _Π_ (A : Set) (B : A → Set) : Set where
  λ : ((a : A) → B a) → A Π B   -- sollte das λ heissen?  
-}




{- Funktionenkomposition -}
_∘_ : {A B C : Set} → (g : B → C) → (f : A → B) → (A → C)
(g ∘ f) a = g (f a)

infix 3 _∘_

_●_ : {A : Set} → { B : A → Set } → { C : {a : A} → B a → Set } →
       (g : {a : A} → (b : B a) → C b ) →  (f : (a : A) → B a) → ((a : A) → C (f a))
(g ● f) a = g ( f a )

_◐_ : {A B : Set} → { C : B → Set } →
       (g : (b : B) → C b ) → (f : A → B ) → ((a : A) → C (f a))
(g ◐ f) a = g ( f a )

_◑_ : {A : Set} → {B C : A → Set} → 
       (g : {a : A} → B a → C a ) → (f : (a : A) → B a ) → ((a : A) → C a)
(g ◑ f) a = g ( f a )








data _↔_ (A B : Set) : Set where
  ↔proof : (A → B) × (B → A) → A ↔ B

refl↔ : {A : Set} → A ↔ A
refl↔ = ↔proof (< id , id >)

symm↔ : {A B : Set} → A ↔ B → B ↔ A
symm↔ (↔proof p) = ↔proof (< (pr2× p) , (pr1× p) >)

trans↔ : {A B C : Set} → A ↔ B → B ↔ C → A ↔ C
trans↔ (↔proof p) (↔proof q) = ↔proof < ((pr1× q) ∘ (pr1× p)) , ((pr2× p) ∘ (pr2× q)) >


{- Negation eines Typs -}
¬_ : Set → Set
¬ P = P → ⊥

infix 3 ¬_

{- Dec A als Typ, dessen Elemente allesamt Beweise von A oder Widerlegungen von A sind -}
data Dec (A : Set) : Set where
  Yes : ( a :   A) → Dec A
  No  : (¬a : ¬ A) → Dec A




