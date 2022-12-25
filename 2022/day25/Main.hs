module Main (main) where

import LoadLines

snafuDigit :: Char -> Int
snafuDigit '1' = 1
snafuDigit '2' = 2
snafuDigit '0' = 0
snafuDigit '=' = (-2)
snafuDigit '-' = (-1)
snafuDigit _ = 0

snafuToDecimal :: String -> Int
snafuToDecimal s = s2d (reverse s) where
  s2d [] = 0
  s2d (x:xs) = snafuDigit x + 5 * (s2d xs)
  
-- If we have a number in base 5, then
-- ABCDE
-- we can add 2 to each digit, and the subtract 2
-- from each digit, as an identity function.
-- But if we add with carry, but subtract without
-- carry, then the result is between -2 and 2.

{-@ decimalToBase5 :: {n:Int | n >= 0} -> Base5Digits @-}
decimalToBase5 :: Int -> [Int]
decimalToBase5 n = reverse (d2f n) where
  {-@ d2f :: {n:Int | n >= 0} -> Base5Digits / [n] @-}
  d2f :: Int -> [Int]
  d2f 0 = []
  d2f x = (x `mod` 5):(d2f (x `div` 5))

{-@ decimalToSnafu :: {n:Int | n >= 0} -> SnafuDigits @-}
decimalToSnafu :: Int -> [Int]
decimalToSnafu n = reverse (d2f n) where
  {-@ d2f :: {n:Int | n >= 0} -> SnafuDigits / [n] @-}
  d2f :: Int -> [Int]
  d2f 0 = []
  d2f x = let y = (x `mod` 5) in
    if y <= 2 then
      y:(d2f (x `div` 5))
    else
      -5+y:(d2f (1 + (x `div` 5)))

{-@ type Base5Digit = {n:Nat | n < 5} @-}
{-@ type SnafuDigit = {n:Int | -2 <= n && n <= 2} @-}
{-@ type Base5Digits = [{n:Nat | n < 5}] @-}
{-@ type SnafuDigits = [{n:Int | -2 <= n && n <= 2}] @-}

{-@ digitSnafu :: {n:Int | n >= (-2) && n <= 2} -> Char @-}
digitSnafu :: Int -> Char
digitSnafu 1 = '1'
digitSnafu 2 = '2'
digitSnafu 0 = '0'
digitSnafu (-2) = '='
digitSnafu (-1) = '-'

{-@ base5ToSnafu :: Base5Digits -> String @-}
base5ToSnafu :: [Int] -> String
base5ToSnafu ds = (let (c,r) = addWithCarry ds in
  if c == 0 then
    map digitSnafu (subtractWithoutBorrow r)
  else
    map digitSnafu (subtractWithoutBorrow (c:r))) where
  {-@ addWithCarry :: Base5Digits -> ({n:Nat | n <= 1},Base5Digits) @-}
  addWithCarry :: [Int] -> (Int, [Int] )
  addWithCarry [] = (0, [])
  addWithCarry (d:ds) =
    let (carry, rest) = addWithCarry ds
        out = (carry + d + 2) `mod` 5
        newCarry = (carry + d + 2) `div` 5 in
      (newCarry, (out:rest))
  {-@ subtract2 :: Base5Digit -> SnafuDigit @-}
  subtract2 :: Int -> Int
  subtract2 d = d - 2
  {-@ subtractWithoutBorrow :: Base5Digits -> SnafuDigits @-}
  subtractWithoutBorrow :: [Int] -> [Int]
  subtractWithoutBorrow ds = map subtract2 ds
   

part1 :: [String] -> IO ()
part1 input = do
  putStrLn "Part 1"
  let nums = map snafuToDecimal input in do
    print $ nums
    let ss = sum nums in do
      print $ ss
      if ss >= 0 then
        print $ map digitSnafu $ decimalToSnafu ss
      else
        putStrLn "Oops, negative"
    

part2 :: [String] -> IO ()
part2 _ = do
  putStrLn ""

main :: IO ()
main = runOnLines part1 part2

