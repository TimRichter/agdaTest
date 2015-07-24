 {-
 module Main where

   data Nat : Set where
     zero : Nat
     suc  : Nat → Nat

   module B where
     private f : Nat → Nat
             f n = suc n

   f : Nat -> Nat
   f n = n

   -- open B

   ff : Nat → Nat
   ff x = f (f x) where open B
 -}

 module Main where


  data Nat : Set where
      zero : Nat
      suc  : Nat → Nat
 
  data Void : Set where

  module A where

    private IsZero’ : Nat → Set
            IsZero’ zero    = Void
            IsZero’ (suc n) = Nat

    IsZero : Nat → Set
    IsZero n = IsZero’ n

    prf : Nat -> Nat
    prf x = suc (suc x)

    module B where
      pred : Nat -> Nat
      pred zero = zero
      pred (suc n) = n

    open B public
    
  open A renaming (prf to lala)

  lulu : Nat -> Nat
  lulu n = suc (pred n)

  --prf : (n : Nat) → IsZero n
  --prf n = {!!} 




 
