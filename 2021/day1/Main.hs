module Main (main) where

import System.Environment

larger :: (Int,Int) -> Int
larger (x,y) | x > y = 1
             | otherwise = 0

numIncreases :: [Int] -> Int
numIncreases l@(_:xs) = sum $ map larger $ zip xs l
numIncreases _ = 0

{-@ assume zipWith3 :: (a->b->c->d) -> as:[a] -> bs:[b] -> cs:[c] -> { ds:[d] |
   (len as <= len cs && len as <= len bs => len ds == len ds) &&
   (len bs <= len cs && len bs <= len as => len bs == len ds) &&
   (len cs <= len as && len cs <= len bs => len ds == len cs)
}
@-}

{-@ window :: x:[Int] -> {y:[Int] | len x > 2 => len y = len x - 2}   @-}
window :: [Int] -> [Int]
window l@(_:b:cs) = zipWith3 (\x y z -> x + y + z) l (b:cs) cs
window _ = []

readInt :: String -> Int
readInt = read

part1 :: [Int] -> IO ()
part1 input = do
  putStrLn "Part 1"
  print (numIncreases input)

part2 :: [Int] -> IO ()
part2 input = do
  putStrLn "Part 2"
  print (numIncreases (window input))
  
main :: IO ()
main = do
  args <- getArgs
  if length args == 1 then do
    contents <- readFile (args !! 0)    
    let input = map readInt (words contents) in
      part1 input >> part2 input
  else
    putStrLn "Must specify exactly one input file."

  
