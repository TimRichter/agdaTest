module Bool where
open import TypeConstructions


data 𝔹 : Set where
  False : 𝔹
  True : 𝔹

_∧_ : 𝔹 → 𝔹 → 𝔹
True ∧ True = True
_ ∧ _ = False

_∨_ : 𝔹 → 𝔹 → 𝔹
False ∨ False = False
_ ∨ _ = True

if_then_else_ : {A : Set} → 𝔹 → A → A → A
if True then a1 else a2 = a1
if False then a1 else a2 = a2

-- 

decTo𝔹 : {A : Set} → Dec A → 𝔹
decTo𝔹 (Yes _) = True
decTo𝔹 (No _)  = False

