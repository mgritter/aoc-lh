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
  ( liftIsValid h $ (liftM fst) $ find (\(p,c) -> c == 'S') input,
    liftIsValid h $ (liftM fst) $ find (\(p,c) -> c == 'E') input )

withinOne :: Int -> Bool
withinOne 1 = True
withinOne 0 = True
withinOne (-1) = True
withinOne _ = False
{-@ inline withinOne @-}

{-@ type NeighborCoord H C = {d:Coord | (xCoord C = xCoord d && withinOne (yCoord C - yCoord d)) ||
                                        (yCoord C = yCoord d && withinOne (xCoord C - xCoord d)) } @-}

{-@ adjacent :: h:HeightMap -> v:ValidCoord h -> n:NeighborCoord h v -> Maybe (ValidCoord h) @-}
adjacent :: HeightMap -> Coord -> Coord -> Maybe Coord
adjacent h (y,x) n = case isValid h n of
   Nothing -> Nothing
   Just vn -> if (height h (y,x) >= height h vn) || (1 + height h (y,x) == height h vn) then Just vn
     else Nothing

{-@ allAdjacent :: h:HeightMap -> v:ValidCoord h -> [ValidCoord h] @-}
allAdjacent :: HeightMap -> Coord -> [Coord]
allAdjacent h (y,x) = mapMaybe (adjacent h (y,x)) [(y+1,x),(y-1,x),(y,x+1),(y,x-1)] 

{-@ data QueueEntry c = QE { pos :: c, path :: [c] } @-}
data QueueEntry c = QE { pos :: c, path :: [c] }
  deriving (Show)

-- TODO: it would be awfully nice to have the list guarantee that its items were all adjacent to
-- each other, but we can't inline adjacent due to its use of ! via height.  Can we hide its
-- definition somehow?
{-@ ignore bfs @-}
{-@ bfs :: h:HeightMap -> start:ValidCoord h -> goal:ValidCoord h -> IO (Maybe [ValidCoord h]) @-}
bfs :: HeightMap -> Coord -> Coord -> IO (Maybe [Coord])
bfs h start goal = do
  x <- bfsLoop h goal (Set.singleton start) [QE start []] 
  case x of
    Nothing -> return $ Nothing
    Just qe -> return $ Just $  path qe

{-@ ignore bfsLoop @-}
{-@ bfsLoop :: h:HeightMap -> goal:ValidCoord h -> visited:Set.Set Coord-> q:[QueueEntry (ValidCoord h)]
 -> IO (Maybe (QueueEntry (ValidCoord h))) @-}
bfsLoop :: HeightMap -> Coord -> Set.Set Coord -> [QueueEntry Coord] -> IO (Maybe (QueueEntry Coord))
bfsLoop _ _ _ [] = do
  putStrLn "Empty queue!"
  return Nothing
bfsLoop h goal visited (q:qs) = if (pos q) == goal then return $ Just q
  else do
     putStrLn $ "Visiting: " ++ (show q) -- ++ " Queue: " ++ (show qs)
     bfsLoop h goal newVisited (qs ++ newEntries) where
       adj = allAdjacent h (pos q)
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
          result <- bfs h start goal
          case result of
            Nothing -> putStrLn "Couldn't find path"
            Just p -> do
              print p
              print (length p)

part2 :: [String] -> IO ()
part2 input = do
  putStrLn "Part 2"

main :: IO ()
main = runOnLines part1 part2

