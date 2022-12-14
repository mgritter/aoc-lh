module Main (main) where
{-@ LIQUID "--exact-data-cons" @-}

import LoadLines
import qualified Data.Map as Map
import Data.Maybe
import Data.Either
import Parse (parseLine)
import Data.List.Split

data GridSquare =
  Sand |
  Wall |
  Free

isFree :: GridSquare -> Bool
isFree Free = True
isFree _ = False

{-@ data Coord = Point { yCoord :: Int, xCoord :: Int } @-}
data Coord = Point { yCoord :: Int, xCoord :: Int }
  deriving (Eq,Ord)

type Simulation = Map.Map Coord GridSquare

{-@
data StraightLine =
  HLine { startH::Coord, endH::{c:Coord | yCoord c = yCoord startH } } |
  VLine { startV::Coord, endV::{c:Coord | xCoord c = xCoord startV } }
@-}
data StraightLine =
  HLine { startH::Coord, endH::Coord  } |
  VLine { startV::Coord, endV::Coord  }

{-@ measure isVerticalLine@-}
-- {-@ inline isVerticalLine @-}
isVerticalLine :: StraightLine -> Bool
isVerticalLine (VLine _ _) = True
isVerticalLine _ = False

{-@ measure isHorizontalLine @-}
-- {-@ inline isHorizontalLine @-}
isHorizontalLine :: StraightLine -> Bool
isHorizontalLine (HLine _ _) = True
isHorizontalLine _ = False

intRange :: Int -> Int -> Int -> [Int]
intRange s e step = enumFromThenTo s (s + step) e
{-@ assume intRange :: start:Int -> end:Int -> {step:Int | step /= 0} ->
   {l:[ {x:Int | if step > 0 then (x >= start && x <= end) else (x <= start && x >= end) }]
    | len l = (end - start)/step + 1  } @-}

isStraightLine :: Coord -> Coord -> Maybe StraightLine
isStraightLine s@(Point y1 x1) e@(Point y2 x2) =
  if x1 == x2 then Just $ VLine s e
  else if y1 == y2 then Just $ HLine s e
  else Nothing

-- Horizontal = same Y coordinate, varying X
-- Vertical = same X coordinate, varying Y

{-@ predicate BetweenH S C E = yCoord C = yCoord S &&
  if ( xCoord S <= xCoord E ) then (xCoord C >= xCoord S && xCoord C <= xCoord E)
                              else (xCoord C <= xCoord S && xCoord C >= xCoord E)
@-}
{-@ predicate BetweenV S C E = xCoord C = xCoord S &&
  if ( yCoord S <= yCoord E ) then (yCoord C >= yCoord S && yCoord C <= yCoord E)
                              else (yCoord C <= yCoord S && yCoord C >= yCoord E)
@-}

{-@ test1 :: {c:Coord | BetweenV (Point 0 0) c (Point 10 0)} @-}
test1 :: Coord
test1 = Point 5 0

{-@ test2 :: {c:Coord | BetweenV c c c} @-}
test2 :: Coord
test2 = Point 5 0

{-@ test4 :: {s:StraightLine | isVerticalLine s} @-}
test4 :: StraightLine
test4 = VLine (Point 0 0) (Point 10 0)

-- Fails with measure, not with inline
-- {-@ test3 :: {c:Coord | if (isVerticalLine (VLine (Point 0 0) (Point 10 0))) then (BetweenV c c c) else False} @-}
-- test3 :: Coord
-- test3 = Point 5 0

{-@ direction :: a:Int -> b:Int -> {c:Int | if a <= b then c = 1 else c = -1 } @-}
direction :: Int -> Int -> Int
direction a b = if a <= b then 1 else (-1)

{-@ lineToCoords :: s:StraightLine
  -> [{c:Coord | if (isVerticalLine s) then (BetweenV (startV s) c (endV s))
                                       else (BetweenH (startH s) c (endH s))}]
@-}
lineToCoords :: StraightLine -> [Coord]
lineToCoords (HLine start end) = 
  map (\x -> Point (yCoord start) x) (intRange (xCoord start) (xCoord end) (direction (xCoord start) (xCoord end)))
lineToCoords (VLine start end) =
  map (\y -> Point y (xCoord start)) (intRange (yCoord start) (yCoord end) (direction (yCoord start) (yCoord end)))

paintLines :: [StraightLine] -> Simulation -> Simulation
paintLines sls sim = Map.union (Map.fromList walls) sim where
  walls = map (\c -> (c, Wall)) (sls >>= lineToCoords)

listToStraightLines :: [(Int,Int)] -> [StraightLine]
listToStraightLines [] = []
listToStraightLines ps@(_:_) = sls where
  coords = map (uncurry Point) ps
  pairsOfPoints = zip coords (tail coords)
  sls = mapMaybe (uncurry isStraightLine) pairsOfPoints

maximumY :: Simulation -> Int
maximumY s = yCoord $ fst $ Map.findMax s

showSim :: Int -> Int -> Int -> Int -> Simulation -> String
showSim yMin yMax xMin xMax s =
  unlines (chunksOf (xMax - xMin + 1) chars) where
  squareToChar Sand = 'o'
  squareToChar Free = '.'
  squareToChar Wall = '#'
  chars = [ squareToChar (Map.findWithDefault Free (Point y x) s) |
      y <- [yMin..yMax], x <- [xMin..xMax] ] 

showAuto :: Simulation -> String
showAuto s =
  showSim ((-1) + minimum (map yCoord $ Map.keys s)) (1 + maximumY s)
          ((-1) + minimum (map xCoord $ Map.keys s)) (1 + maximum (map xCoord $ Map.keys s)) s
  

-- Left if fell to infinity
-- Right if stopped
{-@ sandGrainPosition :: infty:Int -> Simulation -> {pos:Coord | yCoord pos <= infty }
   -> Either Coord Coord
    / [ infty - yCoord pos ] @-}
sandGrainPosition :: Int -> Simulation -> Coord -> Either Coord Coord
sandGrainPosition infinity sim p@(Point y x) =
  let down = (Point (y+1) x)
      downSq = Map.findWithDefault Free down sim
      downLeft =(Point (y+1) (x-1))
      downLeftSq = Map.findWithDefault Free downLeft sim
      downRight = (Point (y+1) (x+1))
      downRightSq = Map.findWithDefault Free downRight sim in
    if y >= infinity then Left p
    else if isFree downSq then sandGrainPosition infinity sim down
    else if isFree downLeftSq then sandGrainPosition infinity sim downLeft
    else if isFree downRightSq then sandGrainPosition infinity sim downRight
    else Right p

{-@ inline maxGrains @-}
maxGrains :: Int
maxGrains = 1000000000

{-@ runSimulation :: {infty:Int | infty > 0} -> {ng:Int | ng >= 0} -> Simulation -> (Int,Simulation)
     / [maxGrains - ng] @-}
runSimulation :: Int -> Int -> Simulation -> (Int,Simulation)
runSimulation infinity numGrains sim =
  if numGrains >= maxGrains then (numGrains, sim)
  else case (sandGrainPosition infinity sim (Point 0 500)) of
      Left _ -> (numGrains, sim)
      Right final -> runSimulation infinity (numGrains + 1) (Map.insert final Sand sim)

part1 :: [String] -> IO ()
part1 input = do
  putStrLn "Part 1"
  let parsed = map parseLine input
      errors = (lefts parsed) in
    if length errors > 0 then
      putStrLn $ "Error: " ++ head errors
    else
      let allLines = (rights parsed) >>= listToStraightLines
          sim = paintLines allLines Map.empty
          intoTheVoid = maximumY sim + 1 in
        if intoTheVoid <= 0 then
          putStrLn $ "Negative maximum Y " ++ (show intoTheVoid)
        else do
          putStrLn (showSim 0 9 494 503 sim)
          let (count, final) = runSimulation intoTheVoid 0 sim in do
            putStrLn $ (show count) ++ " grains"
            putStrLn (showSim 0 9 494 503 final)

{-@ runSimulation2 :: {floor:Int | floor > 0} -> {ng:Int | ng >= 0} -> Simulation -> (Int,Simulation)
     / [maxGrains - ng] @-}
runSimulation2 :: Int -> Int -> Simulation -> (Int,Simulation)
runSimulation2 floor numGrains sim =
  if numGrains >= maxGrains then (numGrains, sim)
  else (case (sandGrainPosition floor sim (Point 0 500)) of
      Left final -> check final
      Right final -> check final
       ) where check pos =
                 if pos == (Point 0 500) then
                   (numGrains + 1, sim)
                 else
                   runSimulation2 floor (numGrains + 1) (Map.insert pos Sand sim)

part2 :: [String] -> IO ()
part2 input = do
  putStrLn "Part 2"
  let parsed = map parseLine input
      errors = (lefts parsed) in
    if length errors > 0 then
      putStrLn $ "Error: " ++ head errors
    else
      let allLines = (rights parsed) >>= listToStraightLines
          sim = paintLines allLines Map.empty
          floor = maximumY sim + 1 in
        if floor <= 0 then
          putStrLn $ "Negative maximum Y " ++ (show floor)
        else do
          putStrLn (showAuto sim)
          let (count, final) = runSimulation2 floor 0 sim in do
            putStrLn $ (show count) ++ " grains"
            putStrLn (showAuto final)

main :: IO ()
main = runOnLines part1 part2

