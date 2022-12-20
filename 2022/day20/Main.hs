module Main (main) where

import LoadLines
import Data.List

data ListEntry = LE {
  originalIndex :: Int,
  value :: Int
}

{-@ assume findIndex :: (a -> Bool) -> xs:[a] -> Maybe {i:Nat | i < len xs} @-}

{-@ findOriginalIndex :: Int -> le:[ListEntry]
  -> Maybe {i:Nat | i < len le} @-}
findOriginalIndex :: Int -> [ListEntry] -> Maybe Int
findOriginalIndex oi le =
   findIndex (\e -> originalIndex e == oi) le

--     XXXXXAYYBXXXXXXX
--          5  8   (+3)
--     XXXXXYYBAXXXXXXX
--
--     XXBYYAXXXXXXXXXX
--       2  5      (-3)
--     XXABYYXXXXXXXXXX
--
--
--      XBYYAXXXXXXXXXX
--                 (+12)
--      XABYYXXXXXXXXXX
--
--  And, of course, A = B

-- Move the entry at position "from" to position "to"
{-@ moveToIndex :: l1:[a]
  -> {from:Nat | from < len l1}
  -> {to:Nat | to < len l1}
  -> {l2:[a] | len l2 = len l1} @-}
-- to prove:   ((from = 0 && to = 1) =>
--               (head (tail l2)) = (head l1)) 
moveToIndex :: [a] -> Int -> Int -> [a]
moveToIndex le from to =
  if from == to then
    le
  else if from < to then
    let (left,rest) = splitAt from le
        myElem = head rest
        (between,right) = splitAt (to - from) (tail rest) in
      left ++ between ++ [myElem] ++ right
  else -- to < from
    let (left,rest) = splitAt to le
        (between,right) = splitAt (from - to) rest
        myElem = head right in
      left ++ [myElem] ++ between ++ (tail right)

{-@ euclideanMod :: Int -> {m:Nat | m /= 0} -> {n:Nat | n < m} @-}
euclideanMod :: Int -> Int -> Int
euclideanMod a m = let x = a `mod` m in
  if x < 0 then x + m else x

-- 4, -2, 5, 6, 7, 8, 9
-- 4, 5, 6, 7, 8, -2, 9 | 
-- 4, -2, 5, 6, 7, 8, 9 | 4, -2, 5, 6, 7, 8, 9
-- 0   1  2  3  4  5  6   0   1  2  3  4  5  6
--                 ^ right by 2
--                            ^ = (+3 mod 7) or (+2 mod 6)
--                            ^ left by 3
--                 ^ = 5 = (-3 mod 7) or (-2 mod 6) 
-- FIGURE THIS OUT WHEN LESS TIRED!
-- (Tired mark says: you're not wrapping around all N elements because you don't
-- leave a blank, you're wrapping around the N-1 elements still there.)

-- when using `mod` the newPos could be negative.  Why wasn't LH catching this?
-- TODO: build a small test case
-- Resolved: local experimentation was using -2 `mod` 5, not (-2) `mod` 5
{-@ processEntry :: {xs:[ListEntry] | len xs > 1}
  -> Int -> Int
  -> {ys:[ListEntry] | len ys = len xs} @-}
processEntry :: [ListEntry] -> Int -> Int -> [ListEntry]
processEntry xs originalIndex value =
  case findOriginalIndex originalIndex xs of
    Nothing -> xs
    Just currPos -> let
      newPos = (currPos + value) `euclideanMod` (length xs - 1) in
      moveToIndex xs currPos newPos

intRange :: Int -> Int -> Int -> [Int]
intRange s e step = enumFromThenTo s (s + step) e
{-@ assume intRange :: start:Int -> end:Int -> {step:Int | step /= 0} ->
   {l:[ {x:Int | if step > 0 then (x >= start && x <= end) else (x <= start && x >= end) }]
    | len l = (end - start)/step + 1  } @-}

{-@ findCoordinates :: {xs:[ListEntry] | len xs > 1} -> [Int] @-}
findCoordinates :: [ListEntry] -> [Int]
findCoordinates le =
  case findIndex (\e -> value e == 0) le of
    Nothing -> []
    Just zeroIndex ->
      [ value ( le !! (( zeroIndex + 1000) `mod` (length le))),
        value ( le !! (( zeroIndex + 2000) `mod` (length le))),
        value ( le !! (( zeroIndex + 3000) `mod` (length le)))]
   
printLE :: [ListEntry] -> IO ([ListEntry])
printLE l = do
  print $ (map value l)
  return l

part1 :: [String] -> IO ()
part1 input = do
  putStrLn "Part 1"
  if length input > 1 then
    let nums = map read input
        enumerate = zip (intRange 0 (length nums - 1) 1) nums 
        startList = map (uncurry LE) enumerate
        finalList = foldl (\l (i,v) -> processEntry l i v) startList enumerate in do
      print $ findCoordinates finalList
      print $ sum $ findCoordinates finalList
  else
    putStrLn "Empty input"
       
part2 :: [String] -> IO ()
part2 input = do
  putStrLn "Part 2"
  if length input > 1 then
    let nums = map read input
        enumerate = zip (intRange 0 (length nums - 1) 1) (map (\x -> 811589153 * x) nums)
        startList = map (uncurry LE) enumerate
        enumerate10 = (take (10 * length input) (cycle enumerate))
        finalList = foldl (\l (i,v) -> processEntry l i v) startList enumerate10 in do
      print $ findCoordinates finalList
      print $ sum $ findCoordinates finalList
  else
    putStrLn "Empty input"

main :: IO ()
main = runOnLines part1 part2
