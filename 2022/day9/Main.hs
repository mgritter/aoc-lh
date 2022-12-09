module Main (main) where

import LoadLines
import Data.List.Split
import qualified Data.Set as Set
import Data.Maybe

data Move =
  R Int |
  U Int |
  L Int |
  D Int

parseMove :: String -> Maybe Move
parseMove s = case (splitOneOf " " s) of
  ("R":n:[]) -> Just $ R (read n)
  ("U":n:[]) -> Just $ U (read n)
  ("L":n:[]) -> Just $ L (read n)
  ("D":n:[]) -> Just $ D (read n)
  _ -> Nothing

type Coord = (Int,Int)

yCoord :: Coord -> Int
yCoord (y,x) = y

xCoord :: Coord -> Int
xCoord (y,x) = x
{-@ measure yCoord @-}
{-@ measure xCoord @-}

{-
-- Doesn't work, why?
absVal :: Int -> Int
absVal i = if i < 0 then (0 - i) else i
{-@ measure absVal @-}
-}

withinOne :: Int -> Bool
withinOne 1 = True
withinOne 0 = True
withinOne (-1) = True
withinOne _ = False
{-@ inline withinOne @-}
-- NOTE: if it's a measure instead, then moveOneStep fails type-checking with a long error

withinTwo :: Int -> Bool
withinTwo 2 = True
withinTwo 1 = True
withinTwo 0 = True
withinTwo (-1) = True
withinTwo (-2) = True
withinTwo _ = False
{-@ inline withinTwo @-}

{-@ data Sim = Rope {
  headPos :: Coord,
  tailPos :: {c:Coord | withinOne ( yCoord c - yCoord headPos )  &&
                            withinOne ( xCoord c - xCoord headPos ) },
  tailLocations :: {s:Set.Set (Int,Int) | Set_mem tailPos s}
} @-}
data Sim = Rope {
  headPos :: (Int,Int),
  tailPos :: (Int,Int),
  tailLocations :: Set.Set (Int,Int)
}

{-@ nextPosition :: Move -> c:Coord ->
{d:Coord | ((xCoord c = xCoord d && yCoord c /= yCoord d) ||
            (xCoord c /= xCoord d && yCoord c = yCoord d)) &&
           withinOne (yCoord c - yCoord d) &&
           withinOne (xCoord c - xCoord d) } @-}
nextPosition :: Move -> Coord -> Coord
nextPosition (D _) (y,x) = (y - 1, x)
nextPosition (U _) (y,x) = (y + 1, x)
nextPosition (L _) (y,x) = (y, x - 1)
nextPosition (R _) (y,x) = (y, x + 1)

{-@ assume signum :: Num a => x:a  ->
    {z:a | ( if x = 0 then z = 0 else True ) &&
           ( if x > 0 then z = 1 else True ) &&
           ( if x < 0 then z = 0 - 1 else True )}
@-}
-- Given the head position and the tail position, describe the next position for the tail
{-@ nextTailPosition :: headPos:Coord ->
   {t:Coord | withinTwo ( yCoord t - yCoord headPos )  &&
              withinTwo ( xCoord t - xCoord headPos ) } ->
   {t2:Coord | withinOne ( yCoord t2 - yCoord headPos ) &&
               withinOne ( xCoord t2 - xCoord headPos ) &&
               (withinOne ( yCoord t - yCoord headPos ) &&
                withinOne ( xCoord t - xCoord headPos ) =>
                  ( yCoord t = yCoord t2 && xCoord t = xCoord t2)) }
@-}
nextTailPosition :: Coord -> Coord -> Coord
nextTailPosition h t =
  let xDiff = xCoord h - xCoord t
      yDiff = yCoord h - yCoord t
      xSign = signum xDiff
      ySign = signum yDiff
      moreThanOneAway = ( xDiff /= xSign || yDiff /= ySign )
  in if moreThanOneAway then
    (yCoord t + ySign, xCoord t + xSign)
  else
    t

{-@ moveOneStep :: Move -> Sim -> Sim @-}
moveOneStep :: Move -> Sim -> Sim
moveOneStep m sim =
  let nextHead = nextPosition m (headPos sim)
      nextTail = nextTailPosition nextHead (tailPos sim) in
    Rope { headPos = nextHead, tailPos = nextTail,
          tailLocations = (tailLocations sim) `Set.union` (Set.singleton nextTail) }

numMoves :: Move -> Int
numMoves (D n) = n
numMoves (L n) = n
numMoves (R n) = n
numMoves (U n) = n

-- iterate's type doesn't indicate that the length is unbounded?
{-@ ignore moveCompleteStep @-}
moveCompleteStep :: Sim -> Move -> Sim
moveCompleteStep sim m = (iterate (moveOneStep m) sim) !! (numMoves m)

-- Set.singleton (0,0) does not have member (0,0) true, but why?
startPos :: Sim
startPos = let z = (0,0) in
  Rope { headPos = z, tailPos = z,
         tailLocations = Set.singleton z }
 
part1 :: [String] -> IO ()
part1 input = do
  putStrLn "Part 1"
  let moves = mapMaybe parseMove input in
    let lastLoc = foldl moveCompleteStep startPos moves in do
      print $ Set.toList (tailLocations lastLoc)
      print $ Set.size (tailLocations lastLoc)
  
part2 :: [String] -> IO ()
part2 input = do
  putStrLn "Part 2"

main :: IO ()
main = runOnLines part1 part2

-- [(-2,-1),(-1,-2),(-1,-1),(-1,0),(0,-2),(0,-1),(0,0),(0,1),(1,-2),(2,-1),(2,0),(2,1)]
--
-- .....
-- .....
-- .....
-- .....
-- s#...
 
