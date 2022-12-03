{-@ LIQUID "--max-case-expand=4" @-}
  
module Main (main) where

import LoadLines
import Data.String
import Data.Set
import Data.Maybe
import Control.Monad
import Data.Char

{-@ splitRucksack :: {r:String | (len r) mod 2 = 0}  ->
   ({c1:String | (len c1) * 2 = len r},
    {c2:String | (len c2) * 2 = len r}) @-}
splitRucksack :: String -> (String,String)
splitRucksack s = let l = (length s) `div` 2 in ((Prelude.take l s),(Prelude.drop l s))

-- Why don't sets have a cardinality in the specfication?
{-@ assume toList :: s:Set a -> {x:[{e:a | member e s}] | listElts x = s} @-}

{-@ sameCharacter :: a:Set Char -> b:Set Char -> {c:Maybe Char |
  (isJust c => member (fromJust c ) a && member (fromJust c) b)}
  @-}
sameCharacter :: Set Char -> Set Char -> Maybe Char
sameCharacter a b = let i = toList (intersection a b) in  
  if length i == 1 then
    Just $ i !! 0
  else
    Nothing

{-@ sameCharacter3 :: a:Set Char -> b:Set Char -> c:Set Char -> {d:Maybe Char |
  (isJust d => member (fromJust d) a && member (fromJust d) b && member (fromJust d) c)}
  @-}
sameCharacter3 :: Set Char -> Set Char -> Set Char -> Maybe Char
sameCharacter3 a b c = let i = toList (a `intersection` b `intersection` c) in  
  if length i == 1 then
    Just $ i !! 0
  else
    Nothing

{-@ splitIntoThrees :: {x:[String] | (len x) mod 3 = 0 } -> {y:[[String]] | len x = 3 * len y } @-}
splitIntoThrees :: [String] -> [[String]]
splitIntoThrees [] = []
splitIntoThrees l = [(Prelude.take 3 l)] ++ splitIntoThrees (Prelude.drop 3 l)

{-@ assume ord :: c:Char -> {i:Int |
  (c = lit "97" Char => i=97) &&
  (c = lit "122" Char => i=122) &&
  (c = lit "65" Char => i=65) &&
  (c = lit "90" Char => i=90)
} @-}

{-@ assume isAsciiLower :: c:Char -> {b:Bool |
  (c = lit "97" Char => b) &&
  (c = lit "122" Char => b) &&
  (c = lit "65" Char => not b) &&
  (c = lit "90" Char => not b)
} @-}

{-@ assume isAsciiUpper :: c:Char -> {b:Bool |
  (c = lit "97" Char => not b) &&
  (c = lit "122" Char => not b) &&
  (c = lit "65" Char => b) &&
  (c = lit "90" Char => b)
} @-}

{-@ valueOfChar :: c:Char -> {v:Int |
 (c = lit "97" Char => v = 1) &&
 (c = lit "122" Char => v = 26) &&
 (c = lit "65" Char => v = 27) &&
 (c = lit "90" Char => v = 52)
} @-}
valueOfChar :: Char -> Int
valueOfChar c | isAsciiLower c = ord c - ord 'a' + 1
valueOfChar c | isAsciiUpper c = ord c - ord 'A' + 27
valueOfChar _ = 0

valueOfRucksack :: String -> Maybe Int
valueOfRucksack s =
  if length s `mod` 2 /= 0 then Nothing else
  let (c1,c2) = splitRucksack s in
  liftM valueOfChar $ sameCharacter (fromList c1) (fromList c2)

valueOfTriple :: [String] -> Maybe Int
valueOfTriple s =
  if length s /= 3 then Nothing else
    liftM valueOfChar $ sameCharacter3 (fromList (s !! 0)) (fromList (s !! 1)) (fromList (s !! 2))
  
part1 :: [String] -> IO ()
part1 input = do
  putStrLn "Part 1"
  print $ sum (mapMaybe valueOfRucksack input)

part2 :: [String] -> IO ()
part2 input = do
  putStrLn "Part 2"
  if length input `mod` 3 /= 0 then
    putStrLn "Bad input"
  else
    print $ sum (mapMaybe valueOfTriple (splitIntoThrees input))
              
main :: IO ()
main = runOnLines part1 part2
