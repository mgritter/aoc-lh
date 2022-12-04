module Main (main) where

import LoadLines
import Data.List.Split
import Data.Maybe

data Range =
  Bounds Int Int
  
{-@ measure start @-}
start :: Range -> Int
start (Bounds a b) = a

{-@ measure end @-}
end :: Range -> Int
end (Bounds a b) = b

{-@ using (Range) as {v:Range | start v <= end v} @-}

{-@ list4ToRanges :: {r:[Int] | len r = 4} -> Maybe (Range,Range) @-}
list4ToRanges :: [Int] -> Maybe (Range,Range)
list4ToRanges (a:b:c:d:[]) = if a <= b && c <=d then Just (Bounds a b,Bounds c d) else Nothing

{-@ lineToRanges :: String -> Maybe (Range,Range) @-}
lineToRanges :: String -> Maybe (Range,Range)
lineToRanges s = let x = splitOneOf ",-" s in
  if length x /= 4 then Nothing
  else list4ToRanges $ map read x


{-@ inline contains @-}
{-@ contains :: x:Range -> y:Range -> Bool @-}
-- contains X Y is true if X contains range Y
contains :: Range -> Range -> Bool
-- contains (s1,e1) (s2,e2) = s1 <= s2 && e2 <= e1
contains outer inner = start outer <= start inner && end inner <= end outer

-- For all n, if n is in the range y, then whenever contains x y is true, the
-- n should be in the range x.
{-@ containsCorrect :: x:Range -> y:Range -> {n:Int | start y <= n && n <= end y} ->
{b:Bool | b => start x <= n && n <= end x }
 @-}
containsCorrect :: Range -> Range -> Int -> Bool
containsCorrect x y _ = contains x y

{-@ inline overlapsLong @-}
overlapsLong :: Range -> Range -> Bool
overlapsLong x y = 
  (start x <= start y && start y <= end x ) ||
  (start x <= end y  && end y <= end x ) ||
  (start y <= start x && start x <= end y ) ||
  (start y <= end x && end x <= end y )

-- overlaps X Y is true if X and Y have any number in common
-- start X <= C <= end X
-- and start Y <= C <= end Y
--
-- iff
-- start Y <= end X AND start X <= end Y
{-@ overlaps :: x:Range -> y:Range -> {b:Bool | b = overlapsLong x y } @-}
overlaps :: Range -> Range -> Bool
overlaps x y = start x <= end y && start y <= end x

containsEither :: (Range,Range) -> Bool
containsEither (x,y) = contains x y || contains y x

part1 :: [String] -> IO ()
part1 input = do
  putStrLn "Part 1"
  print $ length (filter containsEither (catMaybes (map lineToRanges input)))

-- (a -> a -> b) -> ((a,a) -> b)
takePair :: (a->a->b) -> ((a,a) -> b)
takePair f = \p -> f (fst p) (snd p)

part2 :: [String] -> IO ()
part2 input = do
  putStrLn "Part 2"
  print $ length (filter (takePair overlaps) (catMaybes (map lineToRanges input)))

main :: IO ()
main = runOnLines part1 part2
