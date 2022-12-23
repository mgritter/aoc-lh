module Main (main) where

import LoadLines
import Puzzle

part1 :: [String] -> IO ()
part1 input = do
  putStrLn "Part 1"
  print $ solvePart1 input
  
part2 :: [String] -> IO ()
part2 input = do
  putStrLn "Part 2"
  print $ solvePart2 input

main :: IO ()
main = runOnLines part1 part2

