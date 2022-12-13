module Main (main) where

import Puzzle

{-@ assume iterate :: (a -> a) -> a -> {l:[a] | len l >= 1000000 } @-}

part1 :: () -> IO ()
part1 _ = do
  putStrLn "Part 1"
  let m1 = computeModulus example in do
    putStrLn $ "Working mod " ++ show m1
    let allRounds = iterate (Puzzle.round 4 3 m1) example in
      print $ allRounds !! 20
    
  let m2 = computeModulus input in do
    putStrLn $ "Working mod " ++ show m2    
    let allRounds2 = iterate (Puzzle.round 8 3 m2) input in
      print $ allRounds2 !! 20

part2 :: () -> IO ()
part2 _ = do
  putStrLn "Part 2"
  let m1 = computeModulus example in do
    putStrLn $ "Working mod " ++ show m1
    let allRounds = iterate (Puzzle.round 4 1 m1) example in do
      print $ allRounds !! 1000
      print $ allRounds !! 2000
      print $ allRounds !! 3000
      print $ allRounds !! 4000
      print $ allRounds !! 5000
      print $ allRounds !! 6000
      print $ allRounds !! 7000
      print $ allRounds !! 8000
      print $ allRounds !! 9000
      print $ allRounds !! 10000
      
  let m2 = computeModulus input in do
    putStrLn $ "Working mod " ++ show m2    
    let allRounds2 = iterate (Puzzle.round 8 1 m2) input in
      print $ allRounds2 !! 10000

main :: IO ()
main = part1 () >> part2 ()
