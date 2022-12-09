module Main (main) where

import LoadLines
import Data.Vector ((//),(!))
import qualified Data.Vector as Vec
import Data.Char (digitToInt)
import Data.Maybe
import Data.List (foldl')
import GHC.Enum
import Control.Monad (liftM2)

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

{-@ type InRangeY T = {d:Nat | d < ySize T}  @-}
{-@ type InRangeX T = {d:Nat | d < xSize T}  @-}
{-@ type HeightMapSz H = {h:HeightMap | xSize h = xSize H && ySize h = ySize H} @-}

{-@ markTree :: h:HeightMap -> InRangeY h -> InRangeX h ->
   { h2:HeightMap | ySize h = ySize h2 && xSize h = xSize h2 } @-}
markTree :: HeightMap -> Int -> Int -> HeightMap
markTree h y x = Trees{ ySize = ySize h, xSize = xSize h,
                        heights = (heights h) // [(y, ((heights h) ! y) // [(x,1)] )] }

-- Only orthogonal directions supported
{-@ type Delta = {d:Int | d = 0 || d = -1 || d = 1} @-}
{-@ type DeltaNZ DY = {d:Int | (d = 0 && DY /= 0) || (d = -1 && DY = 0) || (d = 1 && DY = 0)} @-}

{-@ isDeltaPair :: y:Delta -> x:Delta ->
  {b:Bool | b <=> ( ( x = 0 && y /= 0 ) || ( x /= 0 && y = 0 ) )} @-}
isDeltaPair :: Int -> Int -> Bool
isDeltaPair 0 0 = False
isDeltaPair y 0 = True
isDeltaPair 0 x = True
isDeltaPair _ _ = False
{-@ inline isDeltaPair @-}

intRange :: Int -> Int -> Int -> [Int]
intRange s e step = enumFromThenTo s (s + step) e
{-@ assume intRange :: start:Int -> end:Int -> {step:Int | step /= 0} ->
   {l:[ {x:Int | if step > 0 then (x >= start && x <= end) else (x <= start && x >= end) }]
    | len l = (end - start)/step + 1  } @-}

-- Return a list of coordinates starting at the given point and moving in the direction given
{-@ computeRange :: h:HeightMap -> InRangeY h -> InRangeX h -> dy:Delta -> dx:DeltaNZ dy
     -> {l:[(InRangeY h, InRangeX h)] | len l > 0 } @-}
computeRange :: HeightMap -> Int -> Int -> Int -> Int -> [(Int,Int)]
computeRange h y0 x0 (-1) 0 = map (flip (,) x0) (intRange y0 0 (-1))                  
computeRange h y0 x0 1 0 = map (flip (,) x0) (intRange y0 (ySize h - 1) 1)
computeRange h y0 x0 0 (-1) = map ((,) y0) (intRange x0 0 (-1))
computeRange h y0 x0 0 1 = map ((,) y0) (intRange x0 (xSize h - 1) 1)

-- Filter a list of coordinates to increasing maximum height
{-@ findMaxes :: h:HeightMap -> Int -> [(InRangeY h, InRangeX h)] -> [(InRangeY h, InRangeX h)] @-}
findMaxes :: HeightMap -> Int -> [(Int,Int)] -> [(Int,Int)]
findMaxes h bestHeight [] = []
findMaxes h bestHeight ((y,x):rest) =
  let th = ((heights h) ! y) ! x in
    if th > bestHeight then (y,x):(findMaxes h th rest)
    else findMaxes h bestHeight rest

-- Assume that (y0,x0) needs to be marked
-- Look for the next highest tree in direction (dy,dx) until off the grid,
-- mark that tree and recurse
{-@ scanOne :: h:HeightMap -> m:HeightMapSz h
    -> y:InRangeY h -> x:InRangeX h
    -> dy:Delta -> dx:DeltaNZ dy
    -> HeightMapSz h
@-}
scanOne :: HeightMap -> HeightMap -> Int -> Int -> Int -> Int -> HeightMap
scanOne trees marks y0 x0 dy dx =
  foldl' (\h (x,y) -> markTree h x y) marks highestTrees where
  highestTrees = findMaxes trees (-1) scanLine
  scanLine = computeRange trees y0 x0 dy dx

-- Once we changed from [l,u] -- which was incorrect, to .., then we started
-- having type problems here.  Also dependent 4-tuple wtf?!?
{-@ assume allStarts :: h:HeightMap ->
   [((InRangeY h, InRangeX h), p:{(Delta, Delta) | isDeltaPair (fst p) (snd p)})] @-}
allStarts :: HeightMap -> [((Int,Int),(Int,Int))]
allStarts trees =
    -- Downward from all x values
    [ ((0,x),(1,0)) | x <- [0..xSize trees - 1] ] ++
    -- Rightward from all y values (left edge)
    [ ((y,0),(0,1)) | y <- [0..ySize trees - 1] ] ++
    -- Upwards from bottom edge
    [ ((ySize trees - 1,x),(-1,0)) | x <- [0..xSize trees - 1] ] ++
    -- Leftward from right edge
    [ ((y,xSize trees - 1),(0,-1)) | y <- [0..ySize trees - 1] ]

scanAll :: HeightMap -> HeightMap
scanAll trees = foldl' scanFrom zeroMatrix (allStarts trees) where
  scanFrom marks ((y0,x0),(dy,dx)) =
    scanOne trees marks y0 x0 dy dx
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
      -- print $ (allStarts trees)
      putStrLn (showTrees scanned)
      print $ sumAll scanned

-- Compute the number of trees visible along a given range of coordinates. This stops
-- with the first tree of height >= the initial value.
-- It may be zero if we're at the edge, but is one if the neighboring tree is too high.
-- So we can't use takeWhile, unfortunately?
{-@ treesVisible :: h:HeightMap -> Int -> [(InRangeY h, InRangeX h)] -> Int @-}
treesVisible :: HeightMap -> Int -> [(Int,Int)] -> Int
treesVisible h maxHeight [] = 0
treesVisible h maxHeight ((y,x):rest) =
  let th = ((heights h) ! y) ! x in
    1 + if th >= maxHeight then 0 else treesVisible h maxHeight rest

-- Multiple the treesVisible score in each cardinal direction, not counting
-- the tree itself.
{-@ computeScore :: h:HeightMap -> y:InRangeY h -> x:InRangeX h -> Int @-}
computeScore :: HeightMap -> Int -> Int -> Int
computeScore trees y x = foldl1 (*) numTrees where
  myHeight = ((heights trees) ! y ) ! x
  ranges = [ tail $ computeRange trees y x 0 1,
             tail $ computeRange trees y x 0 (-1),
             tail $ computeRange trees y x 1 0,
             tail $ computeRange trees y x (-1) 0 ]
  numTrees = map (treesVisible trees myHeight) ranges

maxScore :: HeightMap -> Int
maxScore trees =
  maximum (map cs (cartProd ys xs)) where
  cs (y,x) = computeScore trees y x  
  xs = intRange 0 (xSize trees - 1) 1
  ys = intRange 0 (ySize trees - 1) 1
  cartProd a b = liftM2 (,) a b 

part2 :: [String] -> IO ()
part2 input = do
  putStrLn "Part 2"
  case readHeightMap input of
    Nothing -> putStrLn "Parse error"
    Just trees -> print $ maxScore trees

main :: IO ()
main = runOnLines part1 part2
