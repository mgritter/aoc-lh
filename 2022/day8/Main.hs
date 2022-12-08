module Main (main) where
{-@ LIQUID "--no-termination" @-}

import LoadLines
import Data.Vector ((//),(!))
import qualified Data.Vector as Vec
import Data.Char (digitToInt)
import Data.Maybe
import Data.List (foldl')

{-@ type Pos = {n:Int | n > 0} @-}

type Vector = Vec.Vector

{-@ data HeightMap = Trees {
  ySize :: Pos,
  xSize :: Pos,
  heights :: {v:(Vector {xs:(Vector Int) | vlen xs = xSize}) | vlen v = ySize}
} @-}
data HeightMap = Trees {
  ySize :: Int,
  xSize :: Int,
  heights :: Vector (Vector Int)
}

readFirstRow :: String -> Vector Int
readFirstRow s = Vec.fromList (Prelude.map digitToInt s)

{-@ readRow :: xSize:Pos -> String -> Maybe {v:(Vector Int)| vlen v = xSize} @-}
readRow :: Int -> String -> Maybe (Vector Int)
readRow xSize s = if Prelude.length s /= xSize then Nothing
  else Just $ Vec.fromList (Prelude.map digitToInt s)

readHeightMap :: [String] -> Maybe HeightMap
readHeightMap ss =
  if Prelude.length ss == 0 then Nothing
  else let firstRow = readFirstRow (Prelude.head ss) in
         if Vec.length firstRow == 0 then Nothing
         else let remainingRows = mapMaybe (readRow (Vec.length firstRow)) (tail ss) in
           Just $ Trees { ySize = length remainingRows + 1,
                          xSize = (Vec.length firstRow),
                          heights = Vec.fromList (firstRow:remainingRows) }

{-@ assume Vec.generate :: sz:Nat -> ({i:Nat | i < sz} -> a) -> {v:Vector a | vlen v = sz} @-}

{-@ assume Vec.// :: v:Vector a -> [({i:Nat | i < vlen v},a)] -> {v2:Vector a | vlen v2 = vlen v} @-}

{-@ zeros :: ys:Pos -> xs:Pos -> {h:HeightMap | xSize h = xs && ySize h = ys} @-}
zeros :: Int -> Int -> HeightMap
zeros ys xs = Trees { ySize = ys, xSize = xs, heights = Vec.generate ys zeroVec } where
  zeroVec _ = Vec.generate xs zero where
  zero _ = 0

{-@ markTree :: h:HeightMap -> {y:Nat | y < ySize h} -> {x:Nat | x < xSize h} ->
   { h2:HeightMap | ySize h = ySize h2 && xSize h = xSize h2 } @-}
markTree :: HeightMap -> Int -> Int -> HeightMap
markTree h y x = Trees{ ySize = ySize h, xSize = xSize h,
                        heights = (heights h) // [(y, ((heights h) ! y) // [(x,1)] )] }


{-@ type Delta = {d:Int | d = 0 || d = -1 || d = 1} @-}
{-@ type DeltaNZ DY = {d:Int | (d = 0 && DY /= 0) || d = -1 || d = 1} @-}
{-@ type InRangeY T = {d:Nat | d < ySize T}  @-}
{-@ type InRangeX T = {d:Nat | d < xSize T}  @-}

-- Assume that (y0,x0) needs to be marked
-- Look for the next highest tree in direction (dy,dx) until off the grid,
-- mark that tree and recurse
-- Termination checking is awful, disabling
{-@ scanOne :: h:HeightMap -> {m:HeightMap | xSize m = xSize h && ySize m = ySize h}
    -> y:InRangeY h -> x:InRangeX h
    -> dy:Delta -> dx:DeltaNZ dy
    -> {m2:HeightMap | xSize m2 = xSize h && ySize m2 = ySize h }
@-}
-- if dy = +1 then (ySize - y) is decreasing
-- if dy = -1 then y is decreasing
scanOne :: HeightMap -> HeightMap -> Int -> Int -> Int -> Int -> HeightMap
scanOne trees marks y0 x0 dy dx =
    findNextMax trees marks' (y0 + dy) (x0 + dx) where
    findNextMax :: HeightMap -> HeightMap -> Int -> Int -> HeightMap
    maxHeight = treeHeight trees y0 x0
    marks' = (markTree marks y0 x0)     
    treeHeight h y x = ((heights h) ! y) ! x
    -- t' is just trees, passed along so we can get the size right
    {-@ findNextMax :: h:HeightMap ->
                       {m:HeightMap | xSize m = xSize h && ySize m = ySize h} ->
                       {y:Int | y >= -1 && y <= ySize h} ->
                       {x:Int | x >= -1 && x <= xSize h} ->
                       {m3:HeightMap | xSize m3 = xSize h && ySize m3 = ySize h}
                       / [ySize h + (0 - dy) * y, xSize h + (0 - dx) * x] @-}
    findNextMax t' marks' y x = if y < 0 then marks'
      else if y >= ySize t' then marks'
      else if x < 0 then marks'
      else if x >= xSize t' then marks'
      else if treeHeight t' y x > maxHeight then scanOne t' marks' y x dy dx 
      else findNextMax t' marks' (y + dy) (x + dx)      

-- Once we changed from [l,u] -- which was incorrect, to .., then we started
-- having type problems here.  Also dependent 4-tuple wtf?!?
{-@ assume allStarts :: h:HeightMap -> [ (InRangeY h, InRangeX h, Delta, Delta) ] @-}
allStarts :: HeightMap -> [(Int,Int,Int,Int)]
allStarts trees =
    -- Downward from all x values
    [ (0,x,1,0) | x <- [0..xSize trees - 1] ] ++
    -- Rightward from all y values (left edge)
    [ (y,0,0,1) | y <- [0..ySize trees - 1] ] ++
    -- Upwards from bottom edge
    [ (ySize trees - 1,x,-1,0) | x <- [0..xSize trees - 1] ] ++
    -- Leftward from right edge
    [ (y,xSize trees - 1,0,-1) | y <- [0..ySize trees - 1] ]

scanAll :: HeightMap -> HeightMap
scanAll trees = foldl' scanFrom zeroMatrix (allStarts trees) where
  scanFrom marks (y0,x0,dy,dx) =
    if dx == 0 && dy == 0 then marks 
    else scanOne trees marks y0 x0 dy dx
  zeroMatrix = zeros (ySize trees) (xSize trees)

sumAll :: HeightMap -> Int
sumAll trees = Vec.sum (Vec.map Vec.sum (heights trees))

showTrees :: HeightMap -> String 
showTrees trees = unlines (Vec.toList (Vec.map printRow (heights trees))) where
    printRow v = Vec.foldl' addDigit "" v
    addDigit s d = s ++ (show d)

part1 :: [String] -> IO ()
part1 input = do
  putStrLn "Part 1"
  case readHeightMap input of
    Nothing -> putStrLn "Parse error"
    Just trees -> let scanned = scanAll trees in do
      print $ (allStarts trees)
      putStrLn (showTrees scanned)
      print $ sumAll scanned
      
part2 :: [String] -> IO ()
part2 input = do
  putStrLn "Part 2"

main :: IO ()
main = runOnLines part1 part2
