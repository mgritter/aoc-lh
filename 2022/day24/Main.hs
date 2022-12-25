module Main (main) where

import Prelude hiding (abs)
import LoadLines
import Data.Maybe
import qualified Data.Set as Set

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

data Orientation =
  North |   -- towards top of board
  East |    -- towards right, default orientation
  South |
  West
  deriving (Eq)

{-@ offset :: Orientation -> Coord -> Coord @-}
offset :: Orientation -> Coord -> Coord
offset North (Point x y) = Point x (y-1)
offset South (Point x y) = Point x (y+1)
offset East (Point x y) = Point (x+1) y
offset West (Point x y) = Point (x-1) y

{-@
data Blizzard = BZ {
  bPos :: Coord,
  bDir :: Orientation
  }
@-}
data Blizzard = BZ {
  bPos :: Coord,
  bDir :: Orientation
}

parseDirection :: Int-> (Int,Char) -> Maybe Blizzard
parseDirection y (x,'>') = Just (BZ (Point x y) East)
parseDirection y (x,'<') = Just (BZ (Point x y) West)
parseDirection y (x,'^') = Just (BZ (Point x y) North)
parseDirection y (x,'v') = Just (BZ (Point x y) South)
parseDirection _ _ = Nothing

parseBlizzards :: [String] -> [Blizzard]
parseBlizzards rows = scanForBlizzards 0 rows where
  scanForBlizzards _ [] = []
  scanForBlizzards y (row:rest) =
    (mapMaybe (parseDirection y) (zip [0..(length row-1)] row)) ++
    (scanForBlizzards (y+1) rest)

{-@
  data Valley = V {
  xSize :: {n:Int | n >= 3},
  ySize :: {n:Int | n >= 3},
  blizzards :: [BlizzardInRange xSize ySize]
}
@-}
data Valley = V {
  xSize :: Int,
  ySize :: Int,
  blizzards :: [Blizzard]
}
{-@
type BlizzardInRange XMAX YMAX = {b:Blizzard | xCoord (bPos b) >= 1 && xCoord (bPos b) < XMAX - 1 &&
                                               yCoord (bPos b) >= 1 && yCoord (bPos b) < YMAX - 1}
@-}
{-@
type CoordInRange XMAX YMAX = {p:Coord | xCoord p >= 1 && xCoord p < XMAX - 1 &&
                                         yCoord p >= 1 && yCoord p < YMAX - 1}
@-}

{-@ parseValley :: r:[String]  -> Maybe Valley @-}
parseValley :: [String] -> Maybe Valley
parseValley rows =
  if length rows < 3 then
    Nothing
  else if length (head rows) < 3 then
    Nothing
  else let xs = length (head rows)
           ys = length rows in
    Just $ V {
    xSize = xs,
    ySize = ys,
    blizzards = filterBlizzards xs ys $ parseBlizzards rows
    }

{-@ filterBlizzards :: x:Int -> y:Int -> [Blizzard] -> [BlizzardInRange x y] @-}
filterBlizzards :: Int -> Int -> [Blizzard] -> [Blizzard]
filterBlizzards _ _ [] = []
filterBlizzards x y (b:bs) = if xCoord (bPos b) >= 1 && xCoord (bPos b) < x - 1 && yCoord (bPos b) >= 1 && yCoord (bPos b) < y - 1 then
                               (b:filterBlizzards x y bs)
                             else (filterBlizzards x y bs)


{-@ nextBlizzard :: v:Valley -> Blizzard -> BlizzardInRange (xSize v) (ySize v) @-}
nextBlizzard :: Valley -> Blizzard -> Blizzard
nextBlizzard v (BZ p d) =
  let (Point nx ny) = offset d p
      nx' = if nx < 1 then xSize v - 2 else if nx >= xSize v - 1 then 1 else nx
      ny' = if ny < 1 then ySize v - 2 else if ny >= ySize v - 1 then 1 else ny
  in
    BZ (Point nx' ny') d
{-
  Expressed all the cases so that LH would tell us which ones were bad!

nextBlizzard v (BZ p d) =
  let (Point nx ny) = offset d p in
    if nx < 1 then
      if ny < 1 then
        BZ (Point (xSize v - 2) (ySize v - 2) ) d
      else if ny >= ySize v - 1 then
        BZ (Point (xSize v - 2) 1) d
      else
        BZ (Point (xSize v - 2) ny) d
    else if nx >= xSize v - 1 then
      if ny < 1 then
        BZ (Point 1 (ySize v - 2) ) d
      else if ny >= ySize v - 1 then
        BZ (Point 1 1) d
      else
        BZ (Point 1 ny) d
    else
      if ny < 1 then
        BZ (Point nx (ySize v - 2) ) d
      else if ny >= ySize v - 1 then
        BZ (Point nx 1) d
      else
        BZ (Point nx ny) d
-}

{-@ nextValley :: v:Valley -> {v2:Valley | xSize v2 = xSize v && ySize v2 = ySize v } @-}
nextValley :: Valley -> Valley
nextValley v = V {
  xSize = xSize v,
  ySize = ySize v,
  blizzards = map (nextBlizzard v) (blizzards v)
  }


intRange :: Int -> Int -> Int -> [Int]
intRange s e step = enumFromThenTo s (s + step) e
{-@ assume intRange :: start:Int -> end:Int -> {step:Int | step /= 0} ->
   {l:[ {x:Int | if step > 0 then (x >= start && x <= end) else (x <= start && x >= end) }]
    | len l = (end - start)/step + 1  } @-}

{-@ allSpaces :: v:Valley -> Set.Set (CoordInRange (xSize v) (ySize v))  @-}
allSpaces :: Valley -> Set.Set Coord
allSpaces v = Set.fromList allCoords where
  allCoords = (intRange 1 (ySize v - 2) 1) >>= row
  {-@ row :: {y:Int | y >= 1 && y < ySize v - 1} -> [CoordInRange (xSize v) (ySize v)] @-}
  row y = map (\x -> Point x y) (intRange 1 (xSize v - 2) 1)

{-@ openSpaces :: v:Valley -> Set.Set (CoordInRange (xSize v) (ySize v))  @-}
openSpaces :: Valley -> Set.Set Coord
openSpaces v = (allSpaces v) `Set.difference` blizzardPos where
  blizzardPos = Set.fromList (map bPos (blizzards v))

{-@ assume iterate :: (a -> a) -> a -> {l:[a] | len l >= 1000001 } @-}

{-@ type IListCoords XMAX YMAX = l:{[Set.Set (CoordInRange XMAX YMAX)] | len l >= 1000001} @-}

{-@ openSpacesT :: v:Valley -> IListCoords (xSize v) (ySize v) @-}
openSpacesT :: Valley -> [Set.Set Coord]
openSpacesT v = map openSpaces (iterate nextValley v)

{-@ 
data Elves = E {
  ePos :: Coord,
  eTime :: {n:Nat | n <= 1000000}
}
@-}
data Elves = E {
  ePos :: Coord,
  eTime :: Int
}
  deriving (Eq)

compareElves :: Elves -> Elves -> Ordering
compareElves (E c1 t1) (E c2 t2) = compare (c1,t1) (c2,t2)

showElves :: Elves -> String
showElves (E (Point x y) t) = "(" ++ (show x) ++ "," ++ (show y) ++ ")@" ++ (show t)

instance Show Elves where show = showElves
instance Ord Elves where compare = compareElves

{-@
type ElvesInRange XMAX YMAX = {b:Elves | xCoord (ePos b) >= 1 && xCoord (ePos b) < XMAX - 1 &&
                                         yCoord (ePos b) >= 0 && yCoord (ePos b) < YMAX}
@-}

{-@ nextMoves :: v:Valley -> IListCoords (xSize v) (ySize v) -> ElvesInRange (xSize v) (ySize v) -> [ElvesInRange (xSize v) (ySize v)]
@-}
nextMoves :: Valley -> [Set.Set Coord] -> Elves -> [Elves]
nextMoves v openSpaces (E (Point x y) time) =
  if time >= 1000000 then
    []
  else 
    (validAndEmpty (x+1) y) ++
    (validAndEmpty x (y+1)) ++
    (validAndEmpty (x-1) y) ++
    (validAndEmpty x (y-1)) ++
    (validAndEmpty x y)
    where
    validAndEmpty nx ny =
      -- These are the start and end positions
      if nx == 1 && ny == 0 then
        [E (Point nx ny) (time + 1)]
      else if nx == (xSize v) - 2 && ny == (ySize v) - 1 then
        [E (Point nx ny) (time + 1)]
      -- otherwise bounded by the walls
      else if nx >= 1 && nx < (xSize v) - 1 &&
         ny >= 1 && ny < (ySize v) - 1 &&
         Set.member (Point nx ny) (openSpaces !! (time + 1)) then
        [E (Point nx ny) (time + 1)]
      else
        []

{-@ abs :: x:Int -> {y:Int | y >= 0 && ( y = 0 - x || y = x ) } @-}
{-@ inline abs @-}
abs :: Int -> Int
abs x = if x < 0 then -x else x

{-@ inline manhattan @-}
manhattan :: Coord -> Coord -> Int
manhattan p1 p2 =
  abs (xCoord p1 - xCoord p2) + abs (yCoord p1 - yCoord p2) 

heuristic :: Valley -> Elves -> Int
heuristic v e =
  manhattan (ePos e) (Point (xSize v - 2) (ySize v - 1))

type PriorityQueue = Set.Set (Int,Elves)

-- minView :: Set a -> Maybe (a, Set a)

{-@ lazy aStarSearch @-}
{-@ aStarSearch :: v:Valley
  -> ((ElvesInRange (xSize v) (ySize v))->[ElvesInRange (xSize v) (ySize v)])
  -> ((ElvesInRange (xSize v) (ySize v))->Bool)
  -> (Elves->Int)
  -> Set.Set (Int,ElvesInRange (xSize v) (ySize v))
  -> Maybe (ElvesInRange (xSize v) (ySize v)) @-}
aStarSearch :: Valley -> (Elves->[Elves]) -> (Elves->Bool) -> (Elves->Int) -> PriorityQueue -> Maybe Elves
aStarSearch v neighbors goal h priorityQueue =
  case Set.minView priorityQueue of
    Nothing -> Nothing
    Just ((_,e),newQ) ->
      if goal e then
        Just e
      else let nn = neighbors e
               nnWithH = Set.fromList $ map (\n -> (h n + (eTime n), n)) nn in
             aStarSearch v neighbors goal h (newQ `Set.union` nnWithH)

goalAtEnd :: Valley -> Elves -> Bool
goalAtEnd v (E (Point x y) _) = x == (xSize v) - 2 && y == (ySize v) - 1
  
goalAtStart :: Valley -> Elves -> Bool
goalAtStart v (E (Point x y) _) = x == 1 && y == 0

heuristicAtStart :: Valley -> Elves -> Int
heuristicAtStart v e =
  manhattan (ePos e) (Point 1 0)

dumpCoords :: [Set.Set Coord] -> IO ()
dumpCoords ts = do
  let byTime = zip [0..800] ts
      out = unlines (byTime >>= coords3)
      coords3 (t,cs) = map (\c -> show t ++ "," ++
                            show (xCoord c) ++ "," ++
                            show (yCoord c)) (Set.toList cs) in
    writeFile "2022/day24/coords.txt" out

part1 :: [String] -> IO ()
part1 input = do
  putStrLn "Part 1"
  case parseValley input of
    Nothing -> putStrLn "Too small!"
    Just v ->
      if (xSize v) < 3 || (ySize v) < 3 then
        error "Too small!"
      else let s = openSpacesT v
               {-@ start :: ElvesInRange (xSize v) (ySize v) @-}
               start = E (Point 1 0) 0
               neighborF = nextMoves v s
               goalF = goalAtEnd v
               hF = heuristic v
               {-@ startQ :: Set.Set (Int,ElvesInRange (xSize v) (ySize v)) @-}
               startQ = Set.singleton (0,start) in do
             dumpCoords s
             case aStarSearch v neighborF goalF hF startQ of
               Nothing -> putStrLn "Not found"
               Just goal -> do
                 print goal
                 part2 v s goal
                 
{-@ part2 :: v:Valley -> IListCoords (xSize v) (ySize v) -> ElvesInRange (xSize v) (ySize v) -> IO () @-}
part2 :: Valley -> [Set.Set Coord] -> Elves -> IO ()
part2 v s start = do
  putStrLn "Part 2"
  let neighborF = nextMoves v s
      goalF = goalAtStart v
      hF = heuristicAtStart v
      {-@ startQ :: Set.Set (Int,ElvesInRange (xSize v) (ySize v)) @-}
      startQ = Set.singleton (0,start) in
    case aStarSearch v neighborF goalF hF startQ of
      Nothing -> putStrLn "Not found"
      Just goal -> do
        print goal
        part3 v s goal

{-@ part3 :: v:Valley -> IListCoords (xSize v) (ySize v) -> ElvesInRange (xSize v) (ySize v) -> IO () @-}
part3 :: Valley -> [Set.Set Coord] -> Elves -> IO ()
part3 v s start =
  let neighborF = nextMoves v s
      goalF = goalAtEnd v
      hF = heuristic v
      {-@ startQ :: Set.Set (Int,ElvesInRange (xSize v) (ySize v)) @-}
      startQ = Set.singleton (0,start) in
    case aStarSearch v neighborF goalF hF startQ of
      Nothing -> putStrLn "Not found"
      Just goal -> do
        print goal

empty :: [String] -> IO ()
empty input = return ()

main :: IO ()
main = runOnLines part1 empty

