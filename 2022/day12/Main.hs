module Main (main) where
{-@ LIQUID "--no-termination" @-}

import LoadLines
import qualified Data.Vector as Vec
import Data.Vector ((!))
import Data.Maybe
import Data.Char
import Data.List
import qualified Data.Set as Set
import Control.Monad

type Coord = (Int,Int)

yCoord :: Coord -> Int
yCoord (y,x) = y

xCoord :: Coord -> Int
xCoord (y,x) = x
{-@ measure yCoord @-}
{-@ measure xCoord @-}

{-@ type Pos = {n:Int | n > 0} @-}

type Vector = Vec.Vector

{-@ data HeightMap = Mountain {
  ySize :: Pos,
  xSize :: Pos,
  heights :: {v:(Vector {xs:(Vector Int) | vlen xs = xSize}) | vlen v = ySize}
} @-}
data HeightMap = Mountain {
  ySize :: Int,
  xSize :: Int,
  heights :: Vector (Vector Int)
}

{-@ predicate Btwn V Lo Hi = (Lo <= V && V < Hi) @-}
{-@ type ValidCoord H = {c:Coord | Btwn (yCoord c) 0 (ySize H) && Btwn (xCoord c) 0 (xSize H) } @-}

{-@ isValid :: h:HeightMap -> c:Coord -> Maybe ({v:ValidCoord h | xCoord v = xCoord c && yCoord v = yCoord c}) @-}
isValid :: HeightMap -> Coord -> Maybe Coord
isValid h (y,x) =
  if 0 <= y && y < ySize h && 0 <= x && x < xSize h then Just (y,x) else Nothing

{-@ height :: h:HeightMap -> ValidCoord h -> Int @-}
height :: HeightMap -> Coord -> Int
height h (y,x) = ((heights h) ! y) ! x

charToHeight :: Char -> Int
charToHeight 'S' = 1
charToHeight 'E' = 26
charToHeight c = ord c - ord 'a' + 1

readFirstRow :: String -> Vector Int
readFirstRow s = Vec.fromList (Prelude.map charToHeight s)

{-@ readRow :: xSize:Pos -> String -> Maybe {v:(Vector Int)| vlen v = xSize} @-}
readRow :: Int -> String -> Maybe (Vector Int)
readRow xSize s = if Prelude.length s /= xSize then Nothing
  else Just $ Vec.fromList (Prelude.map charToHeight s)

readHeightMap :: [String] -> Maybe HeightMap
readHeightMap ss =
  if Prelude.length ss == 0 then Nothing
  else let firstRow = readFirstRow (Prelude.head ss) in
         if Vec.length firstRow == 0 then Nothing
         else let remainingRows = mapMaybe (readRow (Vec.length firstRow)) (tail ss) in
           Just $ Mountain { ySize = length remainingRows + 1,
                             xSize = (Vec.length firstRow),
                             heights = Vec.fromList (firstRow:remainingRows) }

fseLoop :: [String] -> [ (Int, [(Int, Char)] ) ]
fseLoop ss = zip [0..] (map (zip [0..]) ss)

fseFlatten :: [ (Int, [(Int, Char)] ) ] -> [ (Coord, Char) ]
fseFlatten ys = [ ((y,x),c) | (y,xs) <- ys, (x,c) <- xs ]

{-@ liftIsValid :: h:HeightMap -> c:Maybe Coord -> Maybe (ValidCoord h) @-}
liftIsValid :: HeightMap -> Maybe Coord -> Maybe Coord
liftIsValid h Nothing = Nothing
liftIsValid h (Just c) = isValid h c

{-@ findStartAndEnd :: h:HeightMap -> [String] -> (Maybe (ValidCoord h), Maybe (ValidCoord h)) @-}
findStartAndEnd :: HeightMap -> [String] -> (Maybe Coord, Maybe Coord)
findStartAndEnd h ss = let input = fseFlatten $ fseLoop ss in
  ( liftIsValid h $ (liftM fst) $ find (\(_,c) -> c == 'S') input,
    liftIsValid h $ (liftM fst) $ find (\(_,c) -> c == 'E') input )

withinOne :: Int -> Bool
withinOne 1 = True
withinOne 0 = True
withinOne (-1) = True
withinOne _ = False
{-@ inline withinOne @-}

{-@ type NeighborCoord H C = {d:Coord | (xCoord C = xCoord d && withinOne (yCoord C - yCoord d)) ||
                                        (yCoord C = yCoord d && withinOne (xCoord C - xCoord d)) } @-}

{-@ part1Adj :: h:HeightMap
   -> v1:ValidCoord h -> ValidCoord h -> Bool @-}
part1Adj :: HeightMap -> Coord -> Coord -> Bool
part1Adj h p n = (height h p >= height h n) || (1 + height h p == height h n)

{-@ part2Adj :: h:HeightMap
   -> v2:ValidCoord h -> ValidCoord h -> Bool @-}
part2Adj :: HeightMap -> Coord -> Coord -> Bool
part2Adj h p n = part1Adj h n p

-- the "ok a b" function says it's OK to transition from a to b
{-@ adjacent :: h:HeightMap
   -> (ValidCoord h -> ValidCoord h -> Bool)
   -> v2:ValidCoord h -> n:NeighborCoord h v2
   -> Maybe (ValidCoord h) @-}
adjacent :: HeightMap -> (Coord->Coord->Bool) -> Coord -> Coord -> Maybe Coord
adjacent h ok (y,x) n = case isValid h n of
   Nothing -> Nothing
   Just vn -> if ok (y,x) vn then Just vn
     else Nothing

{-@ allAdjacent :: h:HeightMap
  -> (ValidCoord h -> ValidCoord h -> Bool)
  -> v:ValidCoord h -> [ValidCoord h] @-}
allAdjacent :: HeightMap -> (Coord->Coord->Bool) -> Coord -> [Coord]
allAdjacent h ok (y,x) = mapMaybe (adjacent h ok (y,x)) [(y+1,x),(y-1,x),(y,x+1),(y,x-1)] 

{-@ data QueueEntry c = QE { pos :: c, path :: [c] } @-}
data QueueEntry c = QE { pos :: c, path :: [c] }
  deriving (Show)

-- TODO: it would be awfully nice to have the list guarantee that its items were all adjacent to
-- each other, but we can't inline adjacent due to its use of ! via height.  Can we hide its
-- definition somehow?
--
-- Alternative idea: create a type only returned by adjacent, like this:
{-@ data AdjacentCoord = AC { pathLoc:: Coord, prevInPath :: Coord } @-}
data AdjacentCoord = AC { pathLoc:: Coord, prevInPath :: Coord }
-- Then specify a refinement list type which links the elements together
{-@ data AdjacentCoordList =
    StartState { startCoord :: Coord } |
    NextState { headCoord :: AdjacentCoord, tailCoords :: ListStartingWith (prevInPath headCoord)  }
@-}
{-@ measure headAC :: AdjacentCoordList -> Coord
headAC (StartState c) = c
headAC (NextState ac _) = pathLoc ac
@-}
{-@ type ListStartingWith C = {acl:AdjacentCoordList | headAC acl = C} @-}
data AdjacentCoordList =
    StartState Coord |
    NextState AdjacentCoord AdjacentCoordList

-- But here's the real implementation:
{-@ bfs :: h:HeightMap -> start:ValidCoord h
   -> ok:(ValidCoord h->ValidCoord h->Bool)
   -> goal:(ValidCoord h -> Bool) -> Maybe [ValidCoord h] @-}
bfs :: HeightMap -> Coord -> (Coord->Coord->Bool) -> (Coord->Bool) -> Maybe [Coord]
bfs h start ok goal =
  let x = bfsLoop h ok goal (Set.singleton start) [QE start []] in
    case x of
     Nothing -> Nothing
     Just qe -> Just $ path qe

{-@ bfsLoop :: h:HeightMap -> ok:(ValidCoord h -> ValidCoord h -> Bool) -> goal:(ValidCoord h->Bool) -> visited:Set.Set Coord-> q:[QueueEntry (ValidCoord h)]
 -> Maybe (QueueEntry (ValidCoord h)) @-}
bfsLoop :: HeightMap -> (Coord->Coord->Bool) -> (Coord->Bool) -> Set.Set Coord -> [QueueEntry Coord] -> Maybe (QueueEntry Coord)
bfsLoop _ _ _ _ [] = Nothing
bfsLoop h ok goal visited (q:qs) = if goal (pos q) then Just q
  else bfsLoop h ok goal newVisited (qs ++ newEntries) where
    adj = allAdjacent h ok (pos q)
    unvisited = filter (\c -> not (Set.member c visited)) adj
    newVisited = visited `Set.union` (Set.fromList unvisited)
    newEntries = map (\c -> QE c ((path q) ++ [c])) unvisited

part1 :: [String] -> IO ()
part1 input = do
  putStrLn "Part 1"
  case readHeightMap input of
    Nothing -> putStrLn "Invalid input"
    Just h ->
      case findStartAndEnd h input of
        (Nothing, _) -> putStrLn "No start"
        (_,Nothing) -> putStrLn "No end"
        (Just start, Just goal ) -> do
          print start
          print goal
          let result = bfs h start (part1Adj h) (\c -> goal == c) in
            case result of
              Nothing -> putStrLn "Couldn't find path"
              Just p -> do
                print p
                print (length p)

part2 :: [String] -> IO ()
part2 input = do
  putStrLn "Part 2"
  case readHeightMap input of
    Nothing -> putStrLn "Invalid input"
    Just h ->
      case findStartAndEnd h input of
        (_,Nothing) -> putStrLn "No end"
        (_,Just endPos) -> do
          print endPos
          let result = bfs h endPos (part2Adj h) (\c -> height h c == 1) in
            case result of
              Nothing -> putStrLn "Couldn't find path"
              Just p -> do
                print p
                print (length p)


main :: IO ()
main = runOnLines part1 part2

