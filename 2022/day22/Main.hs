module Main (main) where

import LoadLines
import Data.Vector ((//),(!))
import qualified Data.Vector as Vec
import Parse
import Prelude hiding (null)
import GHC.List (null)

{-@ type Pos = {n:Int | n > 0} @-}

{-@ assume Vec.generate :: sz:Nat -> ({i:Nat | i < sz} -> a) -> {v:Vector a | vlen v = sz} @-}
{-@ assume Vec.// :: v:Vector a -> [({i:Nat | i < vlen v},a)] -> {v2:Vector a | vlen v2 = vlen v} @-}

type Vector = Vec.Vector

{-@ data Tile =
  Empty |
  Wall |
  Floor
@-}
data Tile =
  Empty |
  Wall |
  Floor
  deriving (Eq)

{-@ data Maze = Tiles {
  ySize :: Pos,
  xSize :: Pos,
  tiles :: {v:(Vector {xs:(Vector Tile) | vlen xs = xSize}) | vlen v = ySize}
} @-}
data Maze = Tiles {
  ySize :: Int,
  xSize :: Int,
  tiles :: Vector (Vector Tile)
}

readTile :: Char -> Tile
readTile '.' = Floor
readTile '#' = Wall
readTile _ = Empty

readFirstRow :: String -> Vector Tile
readFirstRow s = Vec.fromList (map readTile s)

{-@ readRow :: xSize:Pos -> String -> {v:(Vector Tile)| vlen v = xSize} @-}
readRow :: Int -> String -> Vector Tile
readRow xSize s =
  let row = (map readTile s)
      rowLen = length row in
    if rowLen <= xSize then
      Vec.fromList (row ++ (replicate (xSize - rowLen) Empty))
    else
      Vec.fromList (take xSize row)

readMaze :: [String] -> Maybe Maze
readMaze ss =
  if length ss == 0 then Nothing
  else let width = maximum (map length ss) in
    if width == 0 then Nothing
    else let rows = map (readRow width) ss in
      Just $ Tiles { ySize = length rows,
                     xSize = width,
                     tiles = Vec.fromList rows }

data Orientation =
  North |   -- towards top of board
  East |    -- towards right, default orientation
  South |
  West
  deriving (Eq)

{-@ data Position = P { xPos :: Int, yPos :: Int, facing :: Orientation } @-}
data Position = P { xPos :: Int, yPos:: Int, facing:: Orientation }
{-@ type InBounds M = {p:Position | Main.xPos p >= 0 && Main.xPos p < xSize M && Main.yPos p >=0 && Main.yPos p < ySize M} @-}

showPos :: Position -> String
showPos (P x y North) = "(" ++ (show x) ++ "," ++ (show y) ++ ",N)"
showPos (P x y South) = "(" ++ (show x) ++ "," ++ (show y) ++ ",S)"
showPos (P x y East) = "(" ++ (show x) ++ "," ++ (show y) ++ ",E)"
showPos (P x y West) = "(" ++ (show x) ++ "," ++ (show y) ++ ",W)"

instance Show Position where show = showPos

turnLeft :: Orientation -> Orientation
turnLeft North = West
turnLeft West = South
turnLeft South = East
turnLeft East = North
  
turnRight :: Orientation -> Orientation
turnRight North = East
turnRight West = North
turnRight South = West
turnRight East = South

-- Turned out not to need this
{-@ type OneDifference OX OY = (x::Int,{y:Int | if OX = x then OY /= y else OY = y}) @-}
{-@ offset :: Orientation -> ox:Int -> oy:Int -> OneDifference ox oy @-}
offset :: Orientation -> Int -> Int -> (Int, Int)
offset North x y = (x, y-1)
offset South x y = (x, y+1)
offset East x y = (x+1, y)
offset West x y = (x-1, y)

{-@ getTile :: m:Maze -> {x:Nat | x < xSize m} -> {y:Nat | y < ySize m} -> Tile @-}
getTile :: Maze -> Int -> Int -> Tile
getTile m x y = ((tiles m) ! y) ! x

-- findIndex :: (a -> Bool) -> Vector a -> Maybe Int
{-@ assume Vec.findIndex :: (a -> Bool) -> v:Vector a -> Maybe {n:Nat | n < vlen v} @-}
{-@ assume Vec.findIndices :: (a -> Bool) -> v:Vector a -> Vector {n:Nat | n < vlen v} @-}

{-@ getColumn :: m:Maze -> {x:Nat | x < xSize m} -> {v:Vec.Vector Tile | vlen v = ySize m} @-}
getColumn :: Maze -> Int -> Vec.Vector Tile
getColumn m x = Vec.map (\r -> r ! x) (tiles m)

{-@ topmost :: m:Maze -> {x:Nat | x < xSize m} -> {y:Nat | y < ySize m} @-}
topmost :: Maze -> Int -> Int
topmost m x = case Vec.findIndex (\t -> t /= Empty) (getColumn m x) of
  Nothing -> min 0 (ySize m)
  Just y -> y

{-@ bottommost :: m:Maze -> {x:Nat | x < xSize m} -> {y:Nat | y < ySize m} @-}
bottommost :: Maze -> Int -> Int
bottommost m x = let nonEmpty = Vec.findIndices (\t -> t /= Empty) (getColumn m x) in
  if Vec.length nonEmpty == 0 then (ySize m) - 1
  else nonEmpty ! (Vec.length nonEmpty - 1)

-- Why doesn't it believe that 0 is < xSize m?
{-
{-@ leftmost :: m:Maze -> {y:Nat | y < ySize m} -> {x:Nat | x < xSize m} @-}
leftmost :: Maze -> Int -> Int
leftmost m y = case Vec.findIndex (\t -> t /= Empty) ( (tiles m) ! y) of
  Nothing -> 0
  Just x -> x
-}

{-@ getRow :: m:Maze -> {y:Nat | y < ySize m} -> {v:Vec.Vector Tile | vlen v = xSize m} @-}
getRow :: Maze -> Int -> Vec.Vector Tile
getRow m y = (tiles m) ! y

{-@ leftmost :: m:Maze -> {y:Nat | y < ySize m} -> {x:Nat | x < xSize m} @-}
leftmost :: Maze -> Int -> Int
leftmost m y = case Vec.findIndex (\t -> t /= Empty) (getRow m y) of
  Nothing -> min 0 (xSize m) -- but it doesn't like just 0?!?
  Just x -> x

{-@ rightmost :: m:Maze -> {y:Nat | y < ySize m} -> {x:Nat | x < xSize m} @-}
rightmost :: Maze -> Int -> Int
rightmost m y = let nonEmpty = Vec.findIndices (\t -> t /= Empty) (getRow m y) in
  if Vec.length nonEmpty == 0 then (xSize m) - 1
  else nonEmpty ! (Vec.length nonEmpty - 1)

{-@ wrapAround :: m:Maze -> p:InBounds m -> {q:InBounds m | Main.facing q = Main.facing p} @-}
wrapAround :: Maze -> Position -> Position
wrapAround m p = case (facing p) of
  North -> let ny = (yPos p) - 1 in
             if ny < 0 then P (xPos p) (bottommost m (xPos p)) North
             else if getTile m (xPos p) ny == Empty then P (xPos p) (bottommost m (xPos p)) North
             else P (xPos p) ny North
  South -> let ny = (yPos p) + 1 in
             if ny >= ySize m then P (xPos p) (topmost m (xPos p)) South
             else if getTile m (xPos p) ny == Empty then P (xPos p) (topmost m (xPos p)) South
             else P (xPos p) ny South
  West -> let nx = (xPos p) - 1 in
            if nx < 0 then P (rightmost m (yPos p)) (yPos p) West
            else if getTile m nx (yPos p) == Empty then P (rightmost m (yPos p)) (yPos p) West
            else P nx (yPos p) West
  East -> let nx = (xPos p) + 1 in
            if nx >= xSize m then P (leftmost m (yPos p)) (yPos p) East
            else if getTile m nx (yPos p) == Empty then P (leftmost m (yPos p)) (yPos p) East
            else P nx (yPos p) East
            
{-@ moveOneStep :: m:Maze -> x:InBounds m -> {y:InBounds m | Main.facing y = Main.facing x} @-}
moveOneStep :: Maze -> Position -> Position
moveOneStep m oldPos = let newPos = wrapAround m oldPos in
  if getTile m (xPos newPos) (yPos newPos) == Wall then
    oldPos
  else
    newPos
    
{-@ assume iterate :: (a -> a) -> a -> {l:[a] | len l >= 1000000 } @-}
-- TODO: size of list, work with iterate / infinite lists to get it right?
{-@ moveNSteps :: m:Maze -> InBounds m -> n:Pos -> {l:[InBounds m] | len l >= 1} @-}
moveNSteps :: Maze -> Position -> Int -> [Position]
moveNSteps m oldPos numSteps =
  tail $ take (numSteps + 1) (iterate (moveOneStep m) oldPos)

{-@ followDirections :: m:Maze -> InBounds m -> [Direction] -> [InBounds m] @-}
followDirections :: Maze -> Position -> [Direction] -> [Position]
followDirections m start [] = []
followDirections m start (TurnLeft:ds) =
  followDirections m (P (xPos start) (yPos start) (turnLeft (facing start))) ds
followDirections m start (TurnRight:ds) =
  followDirections m (P (xPos start) (yPos start) (turnRight (facing start))) ds
followDirections m start ((Move n):ds) =
  if n > 0 then
    let mvs = moveNSteps m start n in
      mvs ++ (followDirections m (last mvs) ds)
  else
    followDirections m start ds

{-@ startPosition :: {m:Maze | ySize m > 0 } -> InBounds m @-}
startPosition :: Maze -> Position
startPosition m = P (leftmost m 0) 0 East 

password :: Position -> Int
password (P x y North) = (1000 * (y+1)) + (4 * (x+1)) + 3
password (P x y West) = (1000 * (y+1)) + (4 * (x+1)) + 2
password (P x y South) = (1000 * (y+1)) + (4 * (x+1)) + 1
password (P x y East) = (1000 * (y+1)) + (4 * (x+1)) + 0

-- Example directions:
exampleDirs :: String
exampleDirs = "10R5L5R10L4R5L5"
realDirs :: String

part1 :: [String] -> IO ()
part1 input = do
  putStrLn "Part 1"
  case readMaze input of
    Nothing -> putStrLn "parse error"
    Just m ->
      case parseDirections realDirs of
        Left e -> putStrLn $ "direction parse error: " ++ e
        Right dirs ->
          let result = followDirections m (startPosition m) dirs in do
            print $ result
            --if null result then
            if length result == 0 then
              putStrLn "No results"
            else
              print $ (password (last result))

-- transition across an edge (left), or return original coordinates (right)
-- This is indended to be chained with >>=
{-@ transitionEdge :: Orientation -> Int -> x1:Int -> {x2:Int | x2 > x1 }
                   -> Orientation -> Int -> y1:Int -> {y2:Int | y2 - y1 = x2 - x1 || y1 - y2 = x2 - x1}
                   -> Position -> Either Position Position @-}
transitionEdge :: Orientation -> Int -> Int -> Int -> Orientation -> Int -> Int -> Int -> Position -> Either Position Position
transitionEdge North y xStart xEnd newDir y2 xStart2 xEnd2 p | newDir == South || newDir == North =
  if (yPos p == y && xPos p >= xStart && xPos p <= xEnd && facing p == North) then
    Left (P (xStart2 + (xPos p - xStart) * (signum (xEnd2 - xStart2))) y2 newDir)
  else
    Right p
transitionEdge North y xStart xEnd newDir x2 yStart2 yEnd2 p | newDir == West || newDir == East =
  if (yPos p == y && xPos p >= xStart && xPos p <= xEnd && facing p == North) then
    Left (P x2 (yStart2 + (xPos p - xStart) * (signum (yEnd2 - yStart2))) newDir)
  else
    Right p
transitionEdge South y xStart xEnd newDir y2 xStart2 xEnd2 p | newDir == South || newDir == North =
  if (yPos p == y && xPos p >= xStart && xPos p <= xEnd && facing p == South) then
    Left (P (xStart2 + (xPos p - xStart) * (signum (xEnd2 - xStart2))) y2 newDir)
  else
    Right p
transitionEdge South y xStart xEnd newDir x2 yStart2 yEnd2 p | newDir == West || newDir == East =
  if (yPos p == y && xPos p >= xStart && xPos p <= xEnd && facing p == South) then
    Left (P x2 (yStart2 + (xPos p - xStart) * (signum (yEnd2 - yStart2))) newDir)
  else
    Right p
transitionEdge West x yStart yEnd newDir y2 xStart2 xEnd2 p | newDir == South || newDir == North =
  if (xPos p == x && yPos p >= yStart && yPos p <= yEnd && facing p == West) then
    Left (P (xStart2 + (yPos p - yStart) * (signum (xEnd2 - xStart2))) y2 newDir)
  else
    Right p
transitionEdge West x yStart yEnd newDir x2 yStart2 yEnd2 p | newDir == West || newDir == East =
  if (xPos p == x && yPos p >= yStart && yPos p <= yEnd && facing p == West) then
    Left (P x2 (yStart2 + (yPos p - yStart) * (signum (yEnd2 - yStart2))) newDir)
  else
    Right p
transitionEdge East x yStart yEnd newDir y2 xStart2 xEnd2 p | newDir == South || newDir == North =
  if (xPos p == x && yPos p >= yStart && yPos p <= yEnd && facing p == East) then
    Left (P (xStart2 + (yPos p - yStart) * (signum (xEnd2 - xStart2))) y2 newDir)
  else
    Right p
transitionEdge East x yStart yEnd newDir x2 yStart2 yEnd2 p | newDir == West || newDir == East =
  if (xPos p == x && yPos p >= yStart && yPos p <= yEnd && facing p == East) then
    Left (P x2 (yStart2 + (yPos p - yStart) * (signum (yEnd2 - yStart2))) newDir)
  else
    Right p
transitionEdge _ _ _ _ _ _ _ _ p = Right p

-- If out of bounds, bring back into bounds
-- Left is remapped, Right is original
ex1Cube :: Position -> Either Position Position
ex1Cube p =
  -- "A" edge
  transitionEdge North (-1) 8 11 South 4 3 0 p >>=
  transitionEdge North 3 0 3 South 0 11 8 >>=
  -- "B" edge
  transitionEdge East 12 0 3 West 15 11 8 >>=
  transitionEdge East 16 8 11 West 11 3 0 >>=
  -- "C" edge
  transitionEdge West 7 0 3 South 4 4 7 >>=
  transitionEdge North 3 4 7 East 8 0 3 >>=
  -- "D" edge
  transitionEdge East 12 4 7 South 8 15 12 >>=
  transitionEdge North 7 12 15 West 11 7 4 >>=
  -- "E" edge
  transitionEdge West (-1) 4 7 North 11 15 12 >>=
  transitionEdge South 12 12 15 East 0 7 4 >>=
  -- "F" edge
  transitionEdge South 8 0 3 North 11 11 8 >>=
  transitionEdge South 12 8 11 North 7 3 0 >>=
  -- "G" edge
  transitionEdge South 8 4 7 East 8 11 8 >>=
  transitionEdge West 7 8 11 North 8 7 4

realCube :: Position -> Either Position Position
realCube p =
  -- "A" edge
  transitionEdge South 200 0 49 South 0 100 149 p >>=
  transitionEdge North (-1) 100 149 North 199 0 49 >>=
  -- "B" edge
  transitionEdge East 150 0 49 West 99 149 100 >>=
  transitionEdge East 100 100 149 West 149 49 0 >>=
  -- "C" edge
  transitionEdge South 50 100 149 West 99 50 99 >>=
  transitionEdge East 100 50 99 North 49 100 149 >>=
  -- "D" edge
  transitionEdge North (-1) 50 99 East 0 150 199 >>=
  transitionEdge West (-1) 150 199 South 0 50 99 >>=
  -- "E" edge
  transitionEdge West 49 0 49 East 0 149 100 >>=
  transitionEdge West (-1) 100 149 East 50 49 0 >>=
  -- "F" edge
  transitionEdge West 49 50 99 South 100 0 49 >>=
  transitionEdge North 99 0 49 East 50 50 99 >>=
  -- "G" edge
  transitionEdge East 50 150 199 North 149 50 99 >>=
  transitionEdge South 150 50 99 West 49 150 199
  
nextSquare :: Position -> Position
nextSquare (P x y North) = (P x (y-1) North)
nextSquare (P x y South) = (P x (y+1) South)
nextSquare (P x y West) = (P (x-1) y West)
nextSquare (P x y East) = (P (x+1) y East)

{-@ assume ignoredError :: m:Maze -> String -> InBounds m @-}
{-@ ignore ignoredError @-}
ignoredError :: Maze -> String -> Position
ignoredError _ e = error e

{-@ moveOneStep2 :: m:Maze -> x:InBounds m -> InBounds m @-}
moveOneStep2 :: Maze -> Position -> Position
moveOneStep2 m oldPos =
  let walk = nextSquare oldPos
      newPos = (if xPos walk < 0 || yPos walk < 0 || xPos walk >= xSize m || yPos walk >= ySize m then
                 realCube walk
               else if getTile m (xPos walk) (yPos walk) == Empty then
                 realCube walk
               else
                 Left walk) in
    case newPos of
      Right _ -> ignoredError m "Failed to wrap edge"
      Left np ->
        if xPos np < 0 || yPos np < 0 || xPos np >= xSize m || yPos np >= ySize m then
          ignoredError m "Out of bounds"
        else if getTile m (xPos np) (yPos np) == Wall then oldPos
        else np

{-@ moveNSteps2 :: m:Maze -> InBounds m -> n:Pos -> {l:[InBounds m] | len l >= 1} @-}
moveNSteps2 :: Maze -> Position -> Int -> [Position]
moveNSteps2 m oldPos numSteps =
  tail $ take (numSteps + 1) (iterate (moveOneStep2 m) oldPos)

{-@ followDirections2 :: m:Maze -> InBounds m -> [Direction] -> [InBounds m] @-}
followDirections2 :: Maze -> Position -> [Direction] -> [Position]
followDirections2 m start [] = []
followDirections2 m start (TurnLeft:ds) =
  followDirections2 m (P (xPos start) (yPos start) (turnLeft (facing start))) ds
followDirections2 m start (TurnRight:ds) =
  followDirections2 m (P (xPos start) (yPos start) (turnRight (facing start))) ds
followDirections2 m start ((Move n):ds) =
  if n > 0 then
    let mvs = moveNSteps2 m start n in
      mvs ++ (followDirections2 m (last mvs) ds)
  else
    followDirections2 m start ds


part2 :: [String] -> IO ()
part2 input = do
  putStrLn "Part 2"
  case readMaze input of
    Nothing -> putStrLn "parse error"
    Just m ->
      case parseDirections realDirs of
        Left e -> putStrLn $ "direction parse error: " ++ e
        Right dirs ->
          let result = followDirections2 m (startPosition m) dirs in do
            print $ result
            if null result then
              putStrLn "No results"
            else
              print $ (password (last result))

main :: IO ()
main = runOnLines part1 part2

-- Real directions:
realDirs = "22R2L18R32R4L40R7R49L28R47R49L13L38R34R4R5R18L3L3L8L26L14R17L12L7R24R22L15L12L24L18R11R23R36R42L27L33R15L45L34R4R23L43L27R28R47R46R16L32L37L33L34L4L11L14R28L24R25R23R28R26L47L36L27R42R43R3L4R8R16R36R10R1R30L32L39R34R20R47L44R36R38R7L19R15L5R10R41L7L6R44R26L1L14L38L11R37R15L26L3R5L3R42R46R43L18R24L30L1R10L41L48L28R24R9L50R20R15L36R17R11L50R44R50L33R8R24R46L40R35L7L19R25L25L31R5R8L15R37L6L4L47R48L49R10R34L8R22R7R41R37L45L13L48L23L1R47R27R3L37L46R36L16R19L36R5L28R10L40L41R36R18L25L18L48L3R26R37L22R16R4R2R33R11R31R16R13L13L27L22R24L35R50R20R25R16L39R33L26R18L24R30R34L43L39L19R21L32L18L12L47R25L40L38R30L31R3R26R35L40R15L12R22L29L16L41L41R9L36R30R6L17L24L13L6L23L17L15R47R14L37R37L49R5L24L30R7R1R30L45L21L3L12R41R26R42R42R49L50R37L18L16L25R24R30R21L9L24L36L18R21R46R22R38R12R30L40L21L1R4L31L43L42R2R6R20R30R47R44R47R29R39L13L44L17R8L21R41L26L49R11L20L32R9R42R1L12L15R49R11R16R35L13L7L4R42R45L11R24R41L4R16L19R39R43R49R49R10R39R42L11L25L25R46R47L50R44L4L38R47L5L9R41R33R50L20R50R16L38R41R43R34R28L39R7R25L50L5L49L42R26L9L6L38L36L13R17L29R23R2L36L33R32L48L26L31R28L7R37L7L9L14R21L48R16L2L21L10R29R48L37R35L23R42L11R44L41L8L40R21L45R26L10R7R21R11R26R13R46R33R8L47R17L45L12L31L48L2R48R43L28R6R31R8R31L16L25L34R47L23L37L41L38L3L41L50L30R24L8R41L38L26L43L43R41L3L25R32R28R12L44R34R5R4L50L45R39L5L46L13L11L5R40L20L47R26L12L26R49L8L14L32R4R3R10L11R18L16L19R39L44L19L30L48R5L12L42R38L3L16L32R45L43R21R47R3L45R47R2L23R33L43R44R13R49R12L37R26R7L43R8L30L38L13L28R1L41R28R20R38R6L40R26L9R18R25L33L3R13L24L33L18L43L47L48R29R43L36R44R35R7L50L33L35L40R2R31L32R43L50R8L24R8L8R46R11R1R5R28R24R31R42L45R42R44R17L28L11L36R13L33R29L34L4R49R13L13L25L17R24R21R35L5L29L32L19R32R22R36R26R4L39R25R29R15L14R31L28L8L16L40R10L48L27R22L33L11R37L17L39R36R46R34L47R6R31R40R21R11L14R49R45R33L35L39R4L4L41L49L5L15R21L21L20L43L31L28R41L42R48R23R9L9R4L25R37R38R10L39L15L21L19L6R32L41R21L6L23R5L20L42L45R15L36R5R14L10L34R49R40L47L15L50R23R34R6R24R20R11R10R43L9R46L45L45R12R43L46L43R45L15R14L49L7R25R22L47L8L30R40R8R42L46L13L11L5R10L40L2L28R27L19R43L45R23R6L8R14L30R31R50L6L7L33L29L19L25L29L9R41L19R9L45R18L25R8L22L2R22L12L46R15L5L11L46R34R47L15L49L29R18R14R26R9L25R30R34L43R43L44L6L19R7L49R28L12L35L9R23L24L35R49R46R29L13R49L25L4L49L41L41L39L16R5L47R28L34R8R2R47R41R48R10R21L14L28L19L27R22R34R11L9R7R11L40R45L21L1L31R10L35L24R6L1L47R7L4L17R39R44R10R3R24L39L17R9L44R2R6R14L1L28L36R35L7L23L25R18L12L18L14L8L35R4L49R50R45R46L10L37R11R18R45R33R6R19R31R15R42L47L4R31L8L9R10L7R4R9L31L32R1L26R13R39R14R18L16L8R50R16R7L49L25L14R27R29R40L40L1L29L12L11L1L8R4R14R29L3R11L49R5R29L26R28R6L30R49L3R49L10L23R38R2R9R21L21L2L29L8L10R34R3L2L23L38R32L48L11R6R26R44L39R9R40R43R22R19R2R17R11L16L42R28L23R1L39R11R12R1L6R32L24R7L19R41R18R35L37R26L27R16L31R45L21L30L34L39L30L50R43L42R44R2R40L14R11R13L45L14L21R49R25L32R40R50L20R3L24R38R14R2R37L7L1L18L21R2R23L4L36L10R46R11L43R4L1R20L10L16L11R41L43L48R3R15L32R39R48L19L9L26R23R21R9L18R47R23R3L44L36R19R42R16L4L47R44R48L8R41L4L34R2L2L37R18L40R10R46L1L1R12R44R28R30R32L25R17L13L35R30L4L4R3L33R10R24R47L47R14R20L49L25L25L21R22R2R3R8L28R27R34L48L41L26R10R47R17R47L43R44L22R45R21L6R22R6L26L47L32R43L25R18L39R30R36R40R17L9R32L6R25L49L32L12L6L16L14R41R44R15R15R25R20R6R50L24R19R13L33L36L10R11R47R18L25L49L17R40R33L46R2R22R34R13R36L8L17R36R20R47R16R37L7L19L39R44R43R22L41L10R30L22L1R19L1L48L8R39L48L6R5L23R21L12R8L11L33R48R25R31R11L5R49L12R28L27R16R22R47L23L47R28R9L16L25R45L42L32L48L5R27L49R17L1R6L43L23L44L26L9L17R42L10R49R49L48R19L10R40R13R20L10R9L46R31R31L49L3L45L41R9L33L27R25R34L15R6L40L46L7R17R14R22R45L20L17R10L3L12R18L36L43L45L33R46R39R10L19L5R42R8R7R8R28R8L27R41R30R28R9L14R41R45L19R27L46R35L14R23L36R50R37R11R40R23L31L1R26R14L18L8R43L11L44L25L30L43L37R44L41L25R6L27L37L47R20R14L47R5R47R44R17R24L49R16L47L16L16R44L38L26L15L2L43L47R38R37R23L12L38R41R48R8L35R4R9R22R23L47R16L24L19R28R8L13L44R12R4L8L20R32R48R19R13L3R15R7L45R1R27R50R40L45R37R6L46L48R34L14R17L36L24R19L31R23L44R1R12R12L33R31R4L35L7R44L24R13R5R32R4L11R33L15L21R28R31L45R3R25L44L2R22L47L47L10L3R33L37L39L31L24R41L44R29R16R6L24R13R49L43R26L13R6L15L14L25L24L39R45R9R9R37R10R37R42R22L29R6L29R42R37L29L9L37L37L38R35L33L22R9L26R7R33L12R2R50L43L29L40R36L17L50L37R2L20R14L15L27R3R1L41R26R4L49R6R5R36L9R7L8L13L27L9L7R22L38L28R45L41L17L41L40L34L44R23L50R7R31R3R12L47L2R49R11L9R39L14R47L31R6R30L22R18R9R26R22R43L33L29L34L50L19R37R12R10L9R39L14R29L39R7L2R21L37R41L20R4L37L43R34L6R6R12R39R9L14L41R11R36L21L28L37L50L14L36R9L37R40R10R6R33L11R15L5L1L34L35L46R3R39R16R18R40R31L31R14L14L34L43R25R8R43R7L23L41R40L11R12R46R47R14L44L26L13L5L37R10L10R8L23L34R11L48R13R17R45R34R22L48L18L48R44L21R8L41L48R3L26L27R3L16R12L4R32L50R34R45R11L14R33L47L12R41R24R29R32R45L14R22R48R45R3R7R13R46L8L3L46L4L23L33L14L9L1R33R11L31R22L13R33R28R35L2R8R12L2L16L40L48L24R27L38R7L14R35R49L22R36L28R35L31L14R13L32L7L45R1L15R28R46L33R12R35R44R11L48R7L23R1L16L8R20R15R22L22L28R47R12R34R30L36L41R31R19L4R26L19L24L7L48R8R7R11L39L17L30L26L37L8L47L23L35R26R47L47L34L29R41L7L31R50L16L27L21L10L28L24R22L47L29R14L13L22L20L47R17R6R8R17R38R26L41L11L4R49L16L50L11R13L10L44R48R25L29R27L17R50L37R10R7L12R17L35L15L49R5R4R17L31R8L23R20R20L28L27R12L48L19L4R41L50L45L21R24R10L27L6L6R36L49L24R31R2R50R20R18R2L42R34L32R47R6L25L22R35L45R23R1L23R15R44L31L18R25R30L6L31L37L1L19R46R38R19R29R16R23R13R18L44R38R27R6R11R14L27L30R47L10R21R37L8L29L14L36R26L15R37L7L25R50R11L30R4L25R13L9R42L28R16R26R23R4R16R20L29R43R8L12R18L8R37L1L46R9R47L50L44R10R46L48L45L35R42R40L43L17L37R40L25R13R26L19L11L50R45R37R13L15R18R19L21L30R37R42L24L47R48L7L8R25R22L14R17R12L24R42L35L10L28R17R18L9L19L46R10L39L49L19L1L44R12L2R23R41R39L43R21R13L42R3L31R9L33R22R21L42L38R37R26R49L6R28L28L25L9L3L21R2R3L45L36L36L21L32L31R37L41L44L17L5L36L18L23L19L48R1R28R23L6L12L48"
