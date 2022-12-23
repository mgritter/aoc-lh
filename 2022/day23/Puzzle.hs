module Puzzle (solvePart1, solvePart2) where
{-
  startPosition, singleRound,
               Coord(Point,xCoord,yCoord),
               Grove(G,elves,proposals),
               showGrove,
               countEmpty
               ) where
-}
{-@ LIQUID "--higherorder" @-}

import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.List hiding (null)
import Data.Maybe
import Prelude hiding (null)
import GHC.List (null)
import Data.List.Split

{-@ data Coord = Point { xCoord :: Int, yCoord :: Int } @-}
data Coord = Point { xCoord :: Int, yCoord :: Int }
  deriving (Eq)

-- Replace default order with y-coordinate first
compareCoord :: Coord -> Coord -> Ordering
compareCoord (Point x1 y1) (Point x2 y2) = compare (y1,x1) (y2,x2)

showCoord :: Coord -> String
showCoord (Point x y) = "(" ++ (show x) ++ "," ++ (show y) ++ ")"

instance Show Coord where show = showCoord
instance Ord Coord where compare = compareCoord

parseInput :: [String] -> [Coord]
parseInput xs = scanForElves 0 xs where
  scanForElves _ [] = []
  scanForElves y (row:rest) =
    (map (\x -> Point x y) (elemIndices '#' row)) ++ (scanForElves (y+1) rest)

noElf :: Grove -> Coord -> Bool
noElf g c = not $ Set.member c (elves g)
  
emptyNeighborhood :: Grove -> Coord -> Bool
emptyNeighborhood g (Point x y) =
  noElf g (Point (x-1) (y-1)) && noElf g (Point x (y-1)) && noElf g (Point (x+1) (y-1)) &&
  noElf g (Point (x-1) y) && noElf g (Point (x+1) y) &&
  noElf g (Point (x-1) (y+1)) && noElf g (Point x (y+1)) && noElf g (Point (x+1) (y+1))
  
northProposal :: Proposal
northProposal g (Point x y) =
  if noElf g (Point (x-1) (y-1)) && noElf g (Point x (y-1)) && noElf g (Point (x+1) (y-1)) then
    Just (Point x (y-1))
  else Nothing

southProposal :: Proposal
southProposal g (Point x y) =
  if noElf g (Point (x-1) (y+1)) && noElf g (Point x (y+1)) && noElf g (Point (x+1) (y+1)) then
    Just (Point x (y+1))
  else Nothing

westProposal :: Proposal
westProposal g (Point x y) =
  if noElf g (Point (x-1) (y-1)) && noElf g (Point (x-1) y) && noElf g (Point (x-1) (y+1)) then
    Just (Point (x-1) y)
  else Nothing

eastProposal :: Proposal
eastProposal g (Point x y) =
  if noElf g (Point (x+1) (y-1)) && noElf g (Point (x+1) y) && noElf g (Point (x+1) (y+1)) then
    Just (Point (x+1) y)
  else Nothing

makeProposal :: Grove -> Coord -> Maybe Coord
makeProposal g elf =
  if emptyNeighborhood g elf then Nothing
  else let moves = mapMaybe (\p -> p g elf) (proposals g) in
    if null moves then Nothing else Just $ head moves

-- Originally tried Grove -> Coord -> Maybe Coord
-- but this caused illegal specification for constructor G
--
-- After moving to Puzzle package, complains about unknown type constructor
-- {-@ type Proposal = Grove -> Coord -> Maybe Coord @-}
type Proposal = Grove -> Coord -> Maybe Coord

-- Need higher-order-functions flag just to reason about Proposal
--
-- Giving up and making this an index?
{-@
data Grove = G {
    proposals :: {ps:[Grove -> (Coord -> Maybe Coord)] | len ps = 4},
    elves :: Set.Set Coord
  }
@-}
data Grove = G {
    proposals :: [Proposal],
    elves :: Set.Set Coord
  }

boundingRectangle :: Grove -> (Int,Int,Int,Int)
boundingRectangle g =
  (minimum $ map xCoord (Set.toList (elves g)),
   maximum $ map xCoord (Set.toList (elves g)),
   minimum $ map yCoord (Set.toList (elves g)),
   maximum $ map yCoord (Set.toList (elves g)))

showGrove :: Grove -> String
showGrove g =
  let (xMin,xMax,yMin,yMax) = boundingRectangle g
      char x y = if noElf g (Point x y) then '.' else '#'
      chars = [ char x y | y <- [yMin..yMax], x <- [xMin..xMax] ]
  in
    unlines $ chunksOf (xMax - xMin + 1) chars

instance Show Grove where show = showGrove

startPosition :: [String] -> Grove
startPosition xs =
  G { elves = Set.fromList (parseInput xs),
      proposals = [ northProposal, southProposal, westProposal, eastProposal ] }

singleRound :: Grove -> Grove
singleRound g =
  let proposedLocations = mapMaybe (makeProposal g) (Set.toList (elves g))
      duplicates = filterDuplicates proposedLocations in
    G {
       elves = moveElves g duplicates,
       proposals = (tail (proposals g)) ++ [head (proposals g)]
      }

-- Find the set of all duplicate proposals
filterDuplicates :: [Coord] -> Set.Set Coord
filterDuplicates cs =
  let originals = map (\c -> Map.singleton c (1::Int)) cs  -- list of map with count 1 per coord
      counts = foldl1 (Map.unionWith (+)) originals -- map with total count per coord
      dups = Map.filter (\n -> n > 1) counts in     -- only those coords with count > 1
    Set.fromList (Map.keys dups)
      
-- Return new locations of all elves, letting them move to their proposed position
-- if not in the duplicate set.
moveElves :: Grove -> Set.Set Coord -> Set.Set Coord
moveElves g duplicates =
  Set.map moveIfNotInDuplicates (elves g) where
  moveIfNotInDuplicates pos =
    case makeProposal g pos of
      Nothing -> pos
      Just newPos -> if Set.member newPos duplicates then pos
        else newPos

countEmpty :: Grove -> Int
countEmpty g = 
  let (xMin,xMax,yMin,yMax) = boundingRectangle g
      numElves = Set.size (elves g) in
    (yMax - yMin + 1) * (xMax - xMin + 1) - numElves

{-@ assume iterate :: (a -> a) -> a -> {l:[a] | len l >= 1000000 } @-}

solvePart1 :: [String] -> Int
solvePart1 input =
    let start = startPosition input 
        states = iterate singleRound start in
    countEmpty (states !! 10)

solvePart2 :: [String] -> Int
solvePart2 input =
    let start = startPosition input 
        states = iterate singleRound start
        offsetStates = zip states (tail states)
        same = findIndex (\(a,b) -> (elves a) == (elves b)) offsetStates in
      case same of
        Nothing -> 0
        Just x -> x + 1
    

