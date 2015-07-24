module TestIO where

open import IO
open import Data.String
open import Foreign.Haskell

{-
postulate
  getLine : IO String

{-# COMPILED getLine getLine #-}
-}

main = run (
       (readFiniteFile "testInput.txt")
       >>= ( λ x → putStrLn "Hallo, " ++ x ++ "!" ))
