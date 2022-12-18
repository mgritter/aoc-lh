module Main (main) where

import Prelude hiding (abs)
import LoadLines
import Data.List.Split
import qualified Data.Set as Set
import Data.Maybe

{-@
data Voxel = Point {
  xCoord :: Int,
  yCoord :: Int,
  zCoord :: Int
}
@-}
data Voxel = Point {
  xCoord :: Int,
  yCoord :: Int,
  zCoord :: Int
} deriving (Eq, Ord)

showVoxel :: Voxel -> String
showVoxel (Point x y z) = "(" ++ (show x) ++ "," ++ (show y) ++ "," ++ (show z) ++ ")"

instance Show Voxel where show = showVoxel

parseVoxel :: String -> Maybe Voxel
parseVoxel s = 
  let tokens = splitOn "," s in
    if length tokens /= 3 then Nothing
    else Just $ Point (read (tokens !! 0)) (read (tokens !! 1)) (read (tokens !! 2)) 

{-@ abs :: x:Int -> {y:Int | y >= 0 && ( y = 0 - x || y = x ) } @-}
{-@ inline abs @-}
abs :: Int -> Int
abs x = if x < 0 then -x else x


-- using (Point x1 y1 z1) (Point x2 y2 z2) resulted in an invalid specification
{-@ inline manhattan @-}
manhattan :: Voxel -> Voxel -> Int
manhattan p1 p2 =
  abs (xCoord p1 - xCoord p2) + abs (yCoord p1 - yCoord p2) + abs (zCoord p1 - zCoord p2)
  
{-@ neighbors :: v:Voxel -> {vs:[{n:Voxel | manhattan v n = 1}] | len vs = 6} @-}
neighbors :: Voxel -> [Voxel]
neighbors (Point x y z) =
  [ Point (x+1) y z,
    Point (x-1) y z,
    Point x (y+1) z,
    Point x (y-1) z,
    Point x y (z+1),
    Point x y (z-1) ]
    
countExposedIn :: Set.Set Voxel -> Voxel -> Int
countExposedIn s v = length $ filter (\v -> not (Set.member v s)) (neighbors v)

countExposed :: [Voxel] -> Int
countExposed vs = sum (map (countExposedIn (Set.fromList vs)) vs)

part1 :: [String] -> IO ()
part1 input = do
  putStrLn "Part 1"
  let voxels = mapMaybe parseVoxel input in
    print $ countExposed voxels

{-@ data Bounds = B { minX :: Int, maxX :: Int, minY :: Int, maxY :: Int, minZ :: Int, maxZ :: Int } @-}
data Bounds = B { minX :: Int, maxX :: Int, minY :: Int, maxY :: Int, minZ :: Int, maxZ :: Int }
  deriving (Show)

bounds :: [Voxel] -> Bounds
bounds vs =
  B (minimum (map xCoord vs)) (maximum (map xCoord vs)) (minimum (map yCoord vs)) (maximum (map yCoord vs)) (minimum (map zCoord vs)) (maximum (map zCoord vs))

inBounds :: Bounds -> Voxel -> Bool
inBounds b v = minX b <= xCoord v && xCoord v <= maxX b &&
               minY b <= yCoord v && yCoord v <= maxY b &&
               minZ b <= zCoord v && zCoord v <= maxZ b
{-@ inline inBounds @-}

relax :: Bounds -> Bounds
relax b = B (minX b - 1) (maxX b + 1) (minY b - 1) (maxY b + 1) (minZ b - 1) (maxZ b + 1) 

allPoints :: Bounds -> [Voxel]
allPoints b = [ Point x y z | x <- [minX b .. maxX b],
                y <- [minY b .. maxY b],
                z <- [minZ b .. maxZ b] ]

{-@ checkBounds :: b:Bounds -> v:Voxel -> {t:Bool | t = inBounds b v} @-}
checkBounds :: Bounds -> Voxel -> Bool
checkBounds = inBounds

-- findConnectedComponent
--      generator connected neighborhood
--      starting point
--      returns the connected component
findConnectedComponent :: (Voxel->[Voxel]) -> Voxel -> Set.Set Voxel
findConnectedComponent neighbors start =
  dfs neighbors Set.empty [start]

{-@ lazy dfs @-}
dfs :: (Voxel->[Voxel]) -> Set.Set Voxel -> [Voxel] -> Set.Set Voxel
dfs _ visited [] = visited
dfs neighbors visited (curr:rest) =
  let newVisited = visited `Set.union` (Set.singleton curr)
      nn = neighbors curr
      nn2 = filter (\n -> not (Set.member n newVisited)) nn in
    dfs neighbors newVisited (nn2 ++ rest)

-- FIXME: how can we check inBounds b v2???
-- Answer: filter isn't smart enough to limit the type of its output type
-- to those which pass the predicate.
{-@ neighborsOf :: r:Set.Set Voxel -> b:Bounds -> s:Voxel -> v:Voxel
  -> [{v2:Voxel | manhattan v2 v = 1}]
@-}
neighborsOf :: Set.Set Voxel -> Bounds -> Voxel -> Voxel -> [Voxel]
neighborsOf rocks boundary start v =
  filter ok (neighbors v) where
    ok x = inBounds boundary x && sameMaterial x
    sameMaterial y = Set.member y rocks == Set.member start rocks    

interiorVoxels :: Set.Set Voxel -> Bounds -> Set.Set Voxel
interiorVoxels rocks bounds =
  -- Divide searchSpace up into rocks and non-rocks
  explore searchSpace Set.empty where
     looserBounds = relax bounds
     outsideV = Point (minX looserBounds) (minY looserBounds) (minZ looserBounds)
     outside = findConnectedComponent (neighborsOf rocks looserBounds outsideV) outsideV
     searchSpace = (Set.fromList (allPoints bounds)) `Set.difference` outside 
     explore :: Set.Set Voxel -> Set.Set Voxel -> Set.Set Voxel
     {-@ lazy explore @-}
     explore toSearch nonRocks =
       if null toSearch then nonRocks
       else let startV = Set.findMin toSearch
                cc = findConnectedComponent (neighborsOf rocks bounds startV) startV in
              explore
                 (toSearch `Set.difference` cc)
                 (if Set.member startV rocks then nonRocks else nonRocks `Set.union` cc)

-- Given the list, the rocks and the non-rocks, count exposed faces not in either set
countExposed2 :: [Voxel] -> Set.Set Voxel -> Set.Set Voxel -> Int
countExposed2 vs rocks interior =      
  sum (map (countExposedIn (rocks `Set.union` interior)) vs)

part2 :: [String] -> IO ()
part2 input = do
  putStrLn "Part 2"
  let rocks = mapMaybe parseVoxel input
      region = bounds rocks
      rocksSet = Set.fromList rocks
      interior = interiorVoxels rocksSet region
      soln = countExposed2 rocks rocksSet interior in do
    putStrLn $ "bounds: " ++ (show region)
    putStrLn $ "size: " ++ (show $ (maxX region - minX region) * (maxY region - minY region) * (maxZ region - minZ region))
    putStrLn $ "interior: " ++ (show interior)
    putStrLn $ "exposed faces: " ++ (show soln)
      
main :: IO ()
main = runOnLines part1 part2

