module Natfiles.NatDataDef where

data ℕ : Set where
  Zero : ℕ
  Suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}
