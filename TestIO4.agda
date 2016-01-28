open import Prelude

getLnMax : Nat ->  IO (List Char)
getLnMax zero = return []
getLnMax (suc n) = getChar >>=
        λ (c : Char) -> (decideFinished c) where
  decideFinished : Char -> IO (List Char)
  decideFinished c with (c == (natToChar 10))
  ... | (yes _) = return []
  ... | (no _)  = (getLnMax n) >>= λ (cs : (List Char)) -> return (c ∷ cs)

getLn : IO String
getLn = getLnMax 2000 >>=
        λ (cs : List Char) -> return (primStringFromList cs)




{- Idee mittels CharList zu String und einzelnem getChar einlesen -}


main : IO Unit
main = putStrLn "Hallo! Wer bist denn Du?" >>
       getLn >>=
       λ name -> putStrLn ("Guten Tag, " & name & "!")


{-  next to do: 
     = do 
        putStrLn "Hallo, Bitte Eingabe!" ;;     IOUnit
        name <- getLn ;;                        String <- IOString
        putStrLn ("Hallo, Du " & name")         IOUnit
       
        
        putStrLn "Hallo, Bitte Eingabe!" >>                                   IOUnit
        getLn >>=                                                             IOString
        λ name -> putStrLn ("Guten Tag, " & name & "!")                       String -> IOUnit
        

-}

{- main = return "Hallo" >>= putStrLn-}


       
{- putStrLn schreibt und macht neue Zeile; >> >>= Setzt zusammen -}


