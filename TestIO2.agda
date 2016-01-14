open import Prelude

getLn : IO String
getLn = {- Idee mittels CharList zu String und einzelnem getChar einlesen -}


main : IO Unit
{-main = getChar >>=
       λ (c : Char) -> putChar c-}

{- main = return "Hallo" >>= putStrLn-}


       
{- putStrLn schreibt und macht neue Zeile; >> >>= Setzt zusammen -}


