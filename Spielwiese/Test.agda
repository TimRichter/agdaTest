module Test where

data Bool : Set where
  true  : Bool
  false : Bool



f : Bool → Bool
f true = false
f false = true
