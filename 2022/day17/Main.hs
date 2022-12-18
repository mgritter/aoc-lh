module Main (main) where

import Prelude hiding (cycle, head, tail)
import LoadLines
import qualified Data.Set as Set
import InfiniteList
import Data.Ord
import qualified Data.Map as Map
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

{-@ add :: c1:Coord -> c2:Coord ->
 { s:Coord | xCoord s = xCoord c1  + xCoord c2 &&
             yCoord s = yCoord c1  + yCoord c2 } @-}
add :: Coord -> Coord -> Coord
add (Point x1 y1) (Point x2 y2) = (Point (x1 + x2) (y1 + y2))

-- Pieces are anchored in their bottom-left corner and rocks are given as offsets
{-@
data Piece = P {
  rocks :: Set.Set Coord
}
@-}
data Piece = P {
  rocks :: Set.Set Coord
}

piece1 :: Piece
piece2 :: Piece
piece3 :: Piece
piece4 :: Piece
piece5 :: Piece
piece1 = P $ Set.fromList [(Point 0 0), (Point 1 0), (Point 2 0), (Point 3 0)]
piece2 = P $ Set.fromList [(Point 1 0), (Point 0 1), (Point 1 1), (Point 2 1), (Point 1 2)]
piece3 = P $ Set.fromList [(Point 0 0), (Point 1 0), (Point 2 0), (Point 2 1), (Point 2 2)]
piece4 = P $ Set.fromList [(Point 0 0), (Point 0 1), (Point 0 2), (Point 0 3)]
piece5 = P $ Set.fromList [(Point 0 0), (Point 1 0), (Point 0 1), (Point 1 1)]

pieceOrder :: [Piece]
pieceOrder = cycle [piece1, piece2, piece3, piece4, piece5]

translate :: Piece -> Coord -> Piece
translate p c = P $ Set.map (add c) (rocks p)
 
{-@
data GameBoard =
  Game { numRocksRemaining :: Nat,
         wind :: {l:[Char] | infiniteList l},
         windIndex :: Nat,
         windLen :: {n:Nat | n > 0 },
         nextPiece :: {l:[Piece] | infiniteList l},
         fallingPiece :: Piece,
         fallingPos :: {c:Coord | yCoord c >= 1 },
         filled :: Set.Set Coord,
         topRock :: Int
       }
@-}
data GameBoard =
  Game { numRocksRemaining :: Int, -- number of rocks still to fall
         wind :: [Char],       -- infinite list
         windIndex :: Int,     -- For part 2 we need this :(
         windLen :: Int, 
         nextPiece :: [Piece], -- infinite list
         fallingPiece :: Piece, 
         fallingPos :: Coord,
         filled :: Set.Set Coord,
         topRock :: Int
       }

showGame :: GameBoard -> String
showGame g =
  "Num rocks remaining: " ++ (show $ numRocksRemaining g) ++
  "\nfallingPos: " ++ (show $ fallingPos g) ++
  "\nfilled: " ++ (show $ Set.toList $ filled g) ++
  "\n"

instance Show GameBoard where show = showGame

{-@ fallingY :: GameBoard -> {y:Int | y >= 1} @-}
fallingY :: GameBoard -> Int
fallingY (Game _ _ _ _ _ _ pos _ _) = yCoord pos
{-@ measure fallingY @-}

-- Given a translated piece, check if it would intersect the floor, the walls, or
-- another rock.
intersects :: GameBoard -> Piece -> Coord -> Bool
intersects board piece pos =
  floor0 || wallLeft || wallRight || existing 
  where translated = translate piece pos
        floor0 = not . null $ Set.filter (\(Point x y) -> y <= 0) (rocks translated)
        wallLeft = not . null $ Set.filter (\(Point x y) -> x <= 0) (rocks translated)
        wallRight = not . null $ Set.filter (\(Point x y) -> x >= 8) (rocks translated)
        existing = not $ Set.disjoint (rocks translated) (filled board)

{-@ dropPiece :: g:GameBoard -> GameBoard / [ fallingY g ]  @-}
dropPiece :: GameBoard -> GameBoard
dropPiece g =
  let (g', done) = fall (pushPiece g) in
    if done then g'
    else dropPiece g'

-- Moves the piece in the wind and advances wind
{-@ pushPiece :: g:GameBoard
  -> { g2:GameBoard | fallingY g2 = fallingY g } @-}
pushPiece :: GameBoard -> GameBoard
pushPiece g =
  (case head (wind g) of
    '>' -> moveX 1 
    '<' -> moveX (-1)
    _ -> g) where
  moveX amount =
    -- had to re-do the math here after switching to fallingY measure
    -- (fallingPos g) `add` (Point amount 0)
    let newPos = (Point (xCoord (fallingPos g) + amount) (fallingY g))
        incrWind = g { wind = tail (wind g),
                       windIndex = (windIndex g + 1) `mod` (windLen g) } in
      if intersects g (fallingPiece g) newPos then
        incrWind
      else
        incrWind { fallingPos = newPos }

-- Moves the piece down and signals if we hit
{-@ fall :: g:GameBoard
  -> { g2:(GameBoard,Bool) |
       not (snd g2) <=>
       fallingY (fst g2) = fallingY g - 1 } @-}
fall :: GameBoard -> (GameBoard, Bool)
fall g = moveY (-1) where
  moveY amount =
    let newPos = (fallingPos g) `add` (Point 0 amount) in
      if yCoord newPos == 0 || intersects g (fallingPiece g) newPos then
        (g, True)
      else
        (g { fallingPos = newPos }, False)

{-@ dropAllPieces :: {g:GameBoard | numRocksRemaining g > 0} -> {l:[GameBoard] | len l > 0}
   / [ numRocksRemaining g]
   @-}
dropAllPieces :: GameBoard -> [GameBoard]
dropAllPieces g =
  let afterDrop = dropPiece g
      newRocks = (filled g) `Set.union` (rocks (translate (fallingPiece afterDrop)
                                               (fallingPos afterDrop)))
      newTopRock = max 0 (yCoord (Set.findMax newRocks))
      -- LH is unhappy when I update numRocksRemaining using g {} instead of Game {}
      nextG = Game {
        numRocksRemaining = numRocksRemaining g - 1,
        wind = wind afterDrop,       -- DON'T change wind
        windIndex = windIndex afterDrop,
        windLen = windLen afterDrop,
        nextPiece = tail (nextPiece g),
        fallingPiece = head (nextPiece g),
        fallingPos = Point 3 (newTopRock + 4),
        filled = newRocks,
        topRock = newTopRock
      } in
    if numRocksRemaining (nextG) == 0 then
      [nextG]
    else
      nextG : (dropAllPieces nextG)
  
part1 :: [String] -> IO ()
part1 input = do
  putStrLn "Part 1"
  if length input < 1 then putStrLn "Empty input" else
    let windInput = (head input) in
      if length windInput < 1 then
         putStrLn "Blank line"
      else let start = Game {
         numRocksRemaining = 2022,
         wind = cycle windInput,
         windIndex = 0,
         windLen = length windInput,
         nextPiece = tail pieceOrder,
         fallingPiece = head pieceOrder,
         fallingPos = Point 3 4,
         filled = Set.empty,
         topRock = 0
       } in
        let states = dropAllPieces start in do
          putStrLn (unlines (map showGame (take 5 states)))
          print (topRock (last states))

printHead :: Int -> GameBoard -> String
printHead numRows g =
  unlines (chunksOf 7 ascii) where
  char c = if Set.member c (filled g) then '#' else '.'
  ascii = [ char (Point x (topRock g - y)) | y <- [0..numRows - 1], x <- [1..7] ]

-- We could do cycle detection on the board, if we could identify a sufficient number of rows.
-- Some solutions looked at the profile of each column as their key.  We'll use 20 rows and
-- assume that is sufficient.

whichPiece :: Piece -> String
whichPiece p =
  if rocks p == rocks piece1 then "p1"
  else if rocks p == rocks piece2 then "p2"
  else if rocks p == rocks piece3 then "p3"
  else if rocks p == rocks piece4 then "p4"
  else "p5"

key :: GameBoard -> String
key g =
  (show (windIndex g)) ++ (whichPiece (fallingPiece g)) ++ (rows 20) where
  char c = if Set.member c (filled g) then '#' else '.'
  rows n = [ char (Point x (topRock g - y)) | y <- [0..n], x <- [1..7] ]

printHeights :: (Int,Int,Int) -> IO ()
printHeights (brY,x,y) = do
  putStrLn $ "at " ++ (show brY) ++ " " ++ (show y) ++ " - " ++ (show x ) ++ " = " ++ (show (y - x))

{-@ ignore findDuplicate @-}
{-@ assume findDuplicate :: xs:[String] -> Maybe ({s:Nat | s < len xs},{l:Nat | l > 0}) @-}
findDuplicate :: [String] -> Maybe (Int,Int)
findDuplicate ss =
  search ss Map.empty 0 where
  search :: [String] -> Map.Map String Int -> Int -> Maybe (Int,Int)
  search [] _ _ = Nothing
  search (x:xs) m i =
    case Map.lookup x m of
      Nothing -> search xs (Map.insert x i m) (i+1)
      Just prev -> Just (prev, i - prev)

{-@ ignore part2 @-}
part2 :: [String] -> IO ()
part2 input = do
  putStrLn "Part 2"
  if length input < 1 then putStrLn "Empty input" else
    let windInput = (head input) in
      if length windInput < 1 then
         putStrLn "Blank line"
      else let cycleLength = length windInput * 5
               goal = 1000000000000
               start = Game {
                 numRocksRemaining = 100000000,
                 wind = cycle windInput,
                 windIndex = 0,
                 windLen = length windInput,
                 nextPiece = tail pieceOrder,
                 fallingPiece = head pieceOrder,
                 fallingPos = Point 3 4,
                 filled = Set.empty,
                 topRock = 0 }
               states = [start] ++ dropAllPieces start
               keys = map key states in
             case findDuplicate keys of
               Nothing -> putStrLn "No cycle"
               Just (cStart, cLen) -> do
                 putStrLn $ "Cycle starting at " ++ (show cStart) ++ " of length " ++ (show cLen)
                 putStrLn $ printHead 10 (states !! cStart)
                 putStrLn ""
                 putStrLn $ printHead 10 (states !! (cStart + cLen))
                 -- states !! 0 = 0 rock dropped
                 -- Want: i == goal mod cLen and i >= cStart
                 let i = cStart + (goal - cStart) `mod` cLen
                     si = states !! i                     
                     repeat = states !! (i + cLen)
                     delta = (topRock repeat) - (topRock si)
                     soln = (topRock si) + delta * ((goal - i) `div` cLen) in do
                   putStrLn $ "Height at " ++ (show i) ++ " rocks is " ++ (show (topRock si))
                   putStrLn $ "Delta in cycle is " ++ (show delta)
                   putStrLn $ "Height at " ++ (show goal) ++ " is " ++ (show soln)
               
main :: IO ()
main = runOnLines part1 part2

