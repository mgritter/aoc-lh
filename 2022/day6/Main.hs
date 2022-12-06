module Main (main) where

import LoadLines
import Control.Monad
import Data.Maybe

{-@ data DistinctList a = Empty
                        | Unique { dlHead :: a, dlTail :: DoesNotInclude a dlHead }
@-}
{-@ type DoesNotInclude a H = DistinctList {v:a | v /= H} @-}
data DistinctList a =
   Empty |
   Unique { dlHead :: a, dlTail :: DistinctList a}

{-@ measure dlLen @-}
dlLen :: DistinctList a -> Int
dlLen Empty = 0
dlLen (Unique _ ys) = 1 + dlLen ys

{-@ dlMember :: x:a -> xs:DistinctList a ->
   Maybe ({dl:(DoesNotInclude a x) | dlLen dl = dlLen xs}) @-}
dlMember :: Ord a => a -> DistinctList a -> Maybe (DistinctList a)
dlMember x (Unique y ys) | x == y = Nothing
                  | otherwise = liftM (Unique y) (dlMember x ys)
dlMember _ Empty = Just Empty

{-@ toDistinctList :: xs:[a] -> Maybe {dl:(DistinctList a) | dlLen dl = len xs} @-}
toDistinctList :: Ord a => [a] -> Maybe (DistinctList a)
toDistinctList [] = Just Empty
toDistinctList (x:xs) = case toDistinctList xs of
  Nothing -> Nothing
  Just dl -> case (dlMember x dl) of
    Nothing -> Nothing
    Just dl' -> Just (Unique x dl')

showDl :: DistinctList a -> String
showDl _ = "witness!"

instance Show (DistinctList a) where show = showDl

-- Returns the number of characters consumed up to and including the marker
{-@ startOfPacketMarker :: {n:Int | n >= 1} -> s:String ->
  Maybe (Int, {dl:DistinctList Char | dlLen dl = n }) / [len s] @-}
startOfPacketMarker :: Int -> String -> Maybe (Int, DistinctList Char)
startOfPacketMarker n s | length s < n = Nothing
                        | otherwise = case (toDistinctList (Prelude.take n s)) of
                            Just dl -> Just (n, dl)
                            Nothing -> case (startOfPacketMarker n (tail s)) of
                                    Just (i, dl) -> Just (i+1, dl)
                                    Nothing -> Nothing                                    


part1 :: [String] -> IO ()
part1 input = do
  putStrLn "Part 1"
  if length input == 1 then
    print $ startOfPacketMarker 4 (head input)
  else
    putStrLn "Must have exactly one line in input"

part2 :: [String] -> IO ()
part2 input = do
  putStrLn "Part 2"
  if length input == 1 then
    print $ startOfPacketMarker 14 (head input)
  else
    putStrLn "Must have exactly one line in input"
      
main :: IO ()
main = runOnLines part1 part2
