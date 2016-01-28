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


{- compilation mit:

   agda -c TestIO.agda -i. -i/home/tim/projects/agda-prelude/src

-}
