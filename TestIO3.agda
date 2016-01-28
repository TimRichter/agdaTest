open import Prelude

{-
Test readFile/writeFile
-}

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


{- s "ist" der Inhalt der Datei. Beachte: am Ende steht immer ein newline! -}

worker : String -> String
worker s = s & "noch eine Zeile"

main : IO Unit
main =
{-
  writeFile "/home/tim/projects/TimRichter/agdaTest/testoutput.txt" "ein etwas längerer Text, sogar mit Ümläuten!"
-}

{-
  readFile path1 >>=
  (λ s -> return (s & "\n wird das eine neue Zeile??")) >>=
  (λ s -> putStrLn s)   where
  path1 = "/home/tim/projects/TimRichter/agdaTest/testoutput.txt"
  path2 = "/home/tim/projects/TimRichter/agdaTest/testoutput2.txt"
-}

   getLn >>=
   (λ fname -> readFile (dirpath & fname)) >>=
   (λ s -> putStrLn (worker s))  where
   dirpath = "/home/tim/projects/TimRichter/agdaTest/"

