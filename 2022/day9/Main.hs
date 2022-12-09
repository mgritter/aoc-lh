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


origin :: Coord
origin = (0,0)

-- Set.singleton (0,0) does not have member (0,0) true, but why?
{-@ startPos :: {s:Sim | True } @-}
startPos :: Sim
startPos =
  Rope { headPos = origin, tailPos = origin,
         tailLocations = Set.singleton origin }
 
part1 :: [String] -> IO ()
part1 input = do
  putStrLn "Part 1"
  let moves = mapMaybe parseMove input in
    let lastLoc = foldl moveCompleteStep startPos moves in do
      print $ Set.toList (tailLocations lastLoc)
      print $ Set.size (tailLocations lastLoc)

{-
-- How can we express the relationship between these?
-- This is fails because the Liquid specification is inconsistent with Haskell,
-- which permits an arbitrary type!
-- Or if we use SimPart2 Sim, then it still fails to unify
{-@ data SimPart2 a =
   Empty |
   Chain { headSim :: a ,
           remainingSim :: SimPart2 {s:Sim | headPos s = tailPos headSim } }
@-}
data SimPart2 a =
  Empty |
  Chain { headSim :: a,
          remainingSim :: SimPart2 a }
-}

{-
{-@ startPosN :: {n:Int | n >= 1} -> SimPart2 @-}
startPosN :: Int -> SimPart2
startPosN 1 = Chain startPos Nothing
startPosN n = let tail = (startPosN (n-1)) in
  Chain (Rope {headPos = (headPos (headSim tail)),
               tailPos = (tailPos (headSim tail)),
               tailLocations = (tailLocations (headSim tail)) }) (Just tail)

firstSim :: SimPart2 -> Sim
firstSim (Chain s _) = s
{-@ measure firstSim @-}

-}

{-@ startPosN :: n:Nat -> {l:[Sim] | len l  = n } @-}
startPosN :: Int -> [Sim]
startPosN n = replicate n startPos

{-@ moveTailN :: Coord -> s:[Sim] -> {t:[Sim] | len t = len s} @-}
moveTailN :: Coord -> [Sim] -> [Sim]
moveTailN _ [] = []
moveTailN newHeadPos (x:xs) =
  if withinTwo ( yCoord newHeadPos - yCoord (tailPos x) ) &&
     withinTwo ( xCoord newHeadPos - xCoord (tailPos x) ) then
    let nextTail = nextTailPosition newHeadPos (tailPos x)
        newFirst = Rope { headPos = newHeadPos,
                          tailPos = nextTail,
                          tailLocations = (tailLocations x) `Set.union` (Set.singleton nextTail) }
    in newFirst:(moveTailN nextTail xs)
  else
    (x:xs)    
   
{-@ moveOneStepN :: Move -> {s:[Sim] | len s > 0} -> {t:[Sim] | len t = len s} @-}
moveOneStepN :: Move -> [Sim] -> [Sim]
moveOneStepN m (x:xs) =
  let newHead = moveOneStep m x in
    newHead : (moveTailN (tailPos newHead) xs )

{-@ ignore moveCompleteStepN @-}
{-@ moveCompleteStepN :: {s:[Sim] | len s > 0} -> Move -> {t:[Sim] | len t = len s} @-}
moveCompleteStepN :: [Sim] -> Move -> [Sim]
moveCompleteStepN sims m = (iterate (moveOneStepN m) sims) !! (numMoves m)

part2 :: [String] -> IO ()
part2 input = do
  putStrLn "Part 2"
  let moves = mapMaybe parseMove input in
    let lastKnots = foldl moveCompleteStepN (startPosN 9) moves in
      if length lastKnots /= 9 then
        putStrLn "Missing knots!"
      else let lastLoc = last lastKnots in do
        print $ Set.toList (tailLocations lastLoc)
        print $ Set.size (tailLocations lastLoc)


main :: IO ()
main = runOnLines part1 part2
 
