module Main (main) where

import Prelude hiding (abs)
import Data.List
import LoadLines
import Parser
import Data.Either

-- Theory: if (y,x) is closer to a probe than that probe's beacon, then it cannot contain a probe.

{-@ data Coord = Point { xCoord :: Int, yCoord :: Int } @-}
data Coord = Point { xCoord :: Int, yCoord :: Int }
  deriving (Eq,Ord)

showCoord :: Coord -> String
showCoord (Point x y) = "(" ++ (show x) ++ "," ++ (show y) ++ ")"

instance Show Coord where show = showCoord

{-@ data Sensor = S { pos :: Coord, closest :: Coord } @-}
data Sensor = S { pos :: Coord, closest :: Coord }
  deriving (Eq,Ord,Show)

toSensor :: (Int,Int,Int,Int) -> Sensor
toSensor (x1,y1,x2,y2) = S (Point x1 y1) (Point x2 y2)

{-
 -- TODO: what's the problem here, it looks like LH thinks 0 is only an integer?
{-@ abs :: x:a -> {y:a | y >= 0 && ( y = 0 - x || y = x ) } @-}
abs :: Num a => Ord a => a -> a
abs x = if x < 0 then -x else x
-}

{-@ abs :: x:Int -> {y:Int | y >= 0 && ( y = 0 - x || y = x ) } @-}
{-@ inline abs @-}
abs :: Int -> Int
abs x = if x < 0 then -x else x

{-@ manhattan :: Coord -> Coord -> Nat @-}
{-@ inline manhattan @-}
manhattan :: Coord -> Coord -> Int
manhattan p1 p2 = abs ( xCoord p1 - xCoord p2 ) + abs ( yCoord p1 - yCoord p2 )

-- True if coordinate is closer to the sensor than its beacon
{-@ isCloser :: Coord -> Sensor -> Bool @-}
{-@ inline isCloser @-}
isCloser :: Coord -> Sensor -> Bool
isCloser c s = manhattan c (pos s) <= manhattan (pos s) (closest s)

-- True if all sensors are closer to their beacons than to this coordinate.
-- WRONG!  FIXME
couldHaveABeacon :: [Sensor] -> Coord -> Bool
couldHaveABeacon sensors c = and (map (not . (isCloser c)) sensors)

-- A beacon is impossible if this coordinate is closer to a sensor than
-- that sensor's beacon, UNLESS it is the coordinate of the beacon itself.
couldNotHaveABeacon :: [Sensor] -> Coord -> Bool
couldNotHaveABeacon sensors c = or (map impossible sensors) where
  impossible s = (isCloser c s) && not (c == closest s)

--- Crude heuristic:
---   |---------- minimum X sensor ---------------------- maximum X sensor -------|
--- dist to beacon                                                            dist to beacon

-- What is the set of X coordinates at which we might overlap with a sensor's covered range?
{-@ xRange :: [Sensor] -> (Int, Int) @-}
xRange ss = (minimum (map minX ss), maximum (map maxX ss)) where
  minX (S p close) = xCoord p - (manhattan p close)
  maxX (S p close) = xCoord p + (manhattan p close)

-- TODO for proof:
-- rewrite maximum
-- rewrite minimum
-- rewrite map (?)
{- Aspirational proof 
{-@ proofOutline :: ss:[Sensor] -> {s:Sensor | member s ss} -> x:Int -> y:Int -> 
  { x < fst (xRange ss) => not (isCloser (Point x) s) } @-}
-}

countNoBeacon :: [Sensor] -> Int -> [Int]
countNoBeacon ss y = filter noBeaconPossible [fst range..snd range] where
  noBeaconPossible x = couldNotHaveABeacon ss (Point x y)
  range = xRange ss

part1 :: [String] -> IO ()
part1 input = do  
  putStrLn "Part 1"
  let errors = lefts $ map parseLine input
      sensors = map toSensor $ rights $ map parseLine input in
    if length errors > 0 then
      putStrLn (head errors)
    else do
      print $ xRange sensors
      print $ length $ countNoBeacon sensors 2000000

-- If there's only one point, then it has to be just outside the
-- region covered by some sensor (in fact, multiple?)
--     CCC
--     BCCA
--     BC$AA
--     BBAAA

-- Return all coordinates just out of range (distance N+1) of the sensor
--   X     X  
--  X      #X
-- X####S###BX
--  X       X
--   X     X


radius :: Sensor -> Int
radius s = 1 + manhattan (pos s) (closest s)
{-@ inline radius @-}

{-@ oneOrTwoPoints :: s:Sensor -> {y:Int | 0 - radius s <= y && y <= radius s} ->
  [{c:Coord | manhattan c (pos s) == manhattan (pos s) (closest s) + 1}] @-}
oneOrTwoPoints :: Sensor -> Int -> [Coord]
oneOrTwoPoints (S p b) yOffset =
    (if yOffset == -radius || yOffset == radius then [Point (xCoord p) (yCoord p + yOffset)]
    else if yOffset < 0 then
           [Point (xCoord p - (radius + yOffset)) (yCoord p + yOffset),
            Point (xCoord p + (radius + yOffset)) (yCoord p + yOffset)]
    else 
           [Point (xCoord p - (radius - yOffset)) (yCoord p + yOffset),
            Point (xCoord p + (radius - yOffset)) (yCoord p + yOffset)]
    ) where
      radius = 1 + manhattan p b 

{-@ ignore sensorBorder @-}
{-@ sensorBorder :: s:Sensor -> [Coord] @-}
sensorBorder :: Sensor -> [Coord]
sensorBorder (S pos beacon) =
  let radius = 1 + manhattan pos beacon in
    [-radius..radius] >>= (oneOrTwoPoints (S pos beacon))

searchRegion :: [Sensor] -> Int -> [Coord]
searchRegion ss maxVal =
  filter inRange (ss >>= sensorBorder) where
  inRange (Point x y) = 0 <= x && x <= maxVal && 0 <= y && y <= maxVal

searchMax = 4000000
--searchMax = 20

-- Simulatneous solution to:
-- 0 <= pos_x + x <= max
-- -radius <= x <= radius
-- is ecesary but not sufficient
--
-- -pos_x <= x <= max + pos_x
-- -radius <= x <= radius
-- max (-pos_x, -radius) <= min( max+ pos_x, radius)
--
borderInSearchRegion :: Int -> Sensor -> Bool
borderInSearchRegion maxVal s@(S pos beacon) =
  (max (0 - xCoord pos) (0 - r)) <= (min (maxVal + xCoord pos) r) &&
  (max (0 - yCoord pos) (0 - r)) <= (min (maxVal + yCoord pos) r)
  where r = radius s

part2 :: [String] -> IO ()
part2 input = do
  putStrLn "Part 2"
  let errors = lefts $ map parseLine input
      sensors = map toSensor $ rights $ map parseLine input in
    if length errors > 0 then
      putStrLn (head errors)
    -- Note: using (take 1) seconds works too!  And much faster!  But why?
    -- the first sensor should be the first border, and so lazily we should
    -- find it first too!
    else let search = searchRegion sensors searchMax
             points = filter (couldHaveABeacon sensors) search in do
    -- else let points = filter (couldHaveABeacon sensors) [Point x y | x <- [0..4000000], y <- [0..4000000] ] in do
      if length points > 0 then
        print $ (xCoord (head points) * 4000000) + (yCoord (head points))
      else 
        putStrLn ("no point found")

main :: IO ()
main = runOnLines part1 part2

