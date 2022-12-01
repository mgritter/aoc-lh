module Main (main) where

import System.Environment
import Data.Sort (sortBy)

parseInput :: [String] -> [[Int]]
parseInput lines = foldr addToList [[]] lines where
  addToList "" existing  = [] : existing
  addToList item (x:xs)  = ( (read item) : x ) : xs 

largestSum :: [[Int]] -> Int
largestSum elves = maximum $ map sum elves

{-@ assume sortBy :: (a -> a -> Ordering) -> x:[a] -> {y:[a] | len y = len x} @-}
{-@ largestThreeSums :: {x:[[Int]] | len x >= 3} -> Int @-}
largestThreeSums :: [[Int]] -> Int
largestThreeSums elves = let top = sortBy (flip compare) (map sum elves) in
  (top !! 0) + (top !! 1) + (top !! 2)

part1 :: [String] -> IO ()
part1 input = do
  putStrLn "Part 1"
  print (largestSum (parseInput input))

part2 :: [String] -> IO ()
part2 input = do
  putStrLn "Part 2"
  let elves = parseInput input in
    if length elves >= 3 then
      print $ largestThreeSums elves
    else
      putStrLn "Less than three elves!"
  
main :: IO ()
main = do
  args <- getArgs
  if length args == 1 then do
    contents <- readFile (args !! 0)    
    let input = lines contents in
      part1 input >> part2 input
  else
    putStrLn "Must specify exactly one input file, Mark."

