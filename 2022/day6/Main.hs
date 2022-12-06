module Main (main) where

import LoadLines
import Control.Monad

{-@ allDifferent :: w:a -> x:a -> y:a -> z:a ->
{b:Bool | b <=> ( w /= x && w /= y && w /= z && x /= y && x /= z && y /= z ) } @-}
{-@ inline allDifferent @-}
allDifferent :: Eq a => a -> a -> a -> a -> Bool
allDifferent w x y z = w /= x && w /= y && w /= z && x /= y && x /= z && y /= z

{-@ predicate AllDifferentAtStart S = ((4 <= (len S)) && allDifferent (head S) (head (tail S)) (head (tail (tail S))) (head (tail (tail (tail S))))) @-}

-- Returns the number of characters consumed up to and including the marker
{-@ startOfPacketMarker :: s:String -> {p:Maybe Int |
  if (AllDifferentAtStart s) then (isJust p && fromJust p = 4) else (not isJust p || fromJust p > 4) }
@-} 
startOfPacketMarker :: String -> Maybe Int
startOfPacketMarker packet@(w:x:y:z:_) =
  if allDifferent w x y z then Just 4 else
    case startOfPacketMarker (tail packet) of
      Nothing -> Nothing
      Just x -> Just (x + 1)
startOfPacketMarker _ = Nothing

part1 :: [String] -> IO ()
part1 input = do
  putStrLn "Part 1"
  if length input == 1 then
    print $ startOfPacketMarker (head input)
  else
    putStrLn "Must have exactly one line in input"

part2 :: [String] -> IO ()
part2 input = do
  putStrLn "Part 2"
      
main :: IO ()
main = runOnLines part1 part2
