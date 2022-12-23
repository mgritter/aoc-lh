module Main (main) where
{-@ LIQUID "--higherorder" @-}

import LoadLines
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.List hiding (null)
import Data.Maybe
import Prelude hiding (null)
import GHC.List (null)
import Data.List.Split

data Tile = Elf | Empty

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

noElf :: Set.Set Coord -> Coord -> Bool
noElf g c = not $ Set.member c g
  
emptyNeighborhood :: Set.Set Coord -> Coord -> Bool
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
  if emptyNeighborhood (elves g) elf then Nothing
  else let moves = mapMaybe (\p -> p (elves g) elf) (proposals g) in
    if null moves then Nothing else Just $ head moves

-- Originally tried Grove -> Coord -> Maybe Coord
-- but this caused illegal specification for constructor G
{-@ type Proposal = Set.Set Coord -> Coord -> Maybe Coord @-}
type Proposal = Set.Set Coord -> Coord -> Maybe Coord

-- Need higher-order-functions flag just to reason about Proposal
{-@
data Grove = G {
    proposals :: {ps:[Proposal] | len ps = 4},
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
      char x y = if noElf (elves g) (Point x y) then '.' else '#'
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
  let originals = map (\c -> Map.singleton c 1) cs  -- list of map with count 1 per coord
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

part1 :: [String] -> IO ()
part1 input = do
  putStrLn "Part 1"
  let start = startPosition input 
      states = iterate singleRound start in
    print (take 11 states)

part2 :: [String] -> IO ()
part2 input = do
  putStrLn "Part 2"

main :: IO ()
main = runOnLines part1 part2

