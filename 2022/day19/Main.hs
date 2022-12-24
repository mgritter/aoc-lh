module Main (main) where

import LoadLines
import Data.List.Split
import Data.List
import Data.Maybe
import qualified Data.Set as Set
import Cplex

{-@ 
data Resources =
  RS { ore :: Nat,
       clay :: Nat,
       obsidian :: Nat,
       geode :: Nat }
@-}
data Resources =
  RS { ore :: Int,
       clay :: Int,
       obsidian :: Int,
       geode :: Int }
  deriving (Show,Eq,Ord)

{-@
data Recipe =
  RC { recipeId :: Nat,
       oreCost :: Resources,
       clayCost :: Resources,
       obsidianCost :: Resources,
       geodeCost :: Resources }
@-}
data Recipe =
  RC { recipeId :: Int,
       oreCost :: Resources,
       clayCost :: Resources,
       obsidianCost :: Resources,
       geodeCost :: Resources
     }

--    0      1   2   3    4     5    6  7   8     9   10     11  12 13    14    15      16   17   18  
-- Blueprint 1: Each ore robot costs 4 ore. Each clay robot costs 4 ore. Each obsidian robot costs 3
--  19  20 21  22    23   24    25    26  27  28 29  30   31
-- ore and 19 clay. Each geode robot costs 4 ore and 15 obsidian.
-- Blueprint 2: Each ore robot costs 4 ore. Each clay robot costs 3 ore. Each obsidian robot costs 2 ore and 20 clay. Each geode robot costs 2 ore and 9 obsidian.
-- Blueprint 3: Each ore robot costs 4 ore. Each clay robot costs 3 ore. Each obsidian robot costs 4 ore and 19 clay. Each geode robot costs 4 ore and 12 obsidian.

parseRecipe :: String -> Maybe Recipe
parseRecipe s = let tok = splitOneOf " " s in
  if length tok /= 32 then Nothing 
  else let id = read (delete ':' (tok !! 1))
           c1 = (read (tok !! 6))
           c2 = (read (tok !! 12))
           c3 = (read (tok !! 18))
           c4 = (read (tok !! 21))
           c5 = (read (tok !! 27))
           c6 = (read (tok !! 30)) in
    if id > 0 && c1 > 0 && c2 > 0 && c3 > 0 && c4 > 0 && c3 + c4 > 0 && c5 >0 && c6 > 0 && c5 + c6 > 0 then    
      Just $ RC {
      recipeId = id,
      oreCost = RS c1 0 0 0,
      clayCost = RS c2 0 0 0,
      obsidianCost = RS c3 c4 0 0,
      geodeCost = RS c5 0 c6 0
      }
    else
      Nothing

-- (robots_it, resources_it, purchases_it)
--   s.t resources_it >= cost (purchases_it)
--       robots_i(t+1) = robots_i(t) + purchases_i(t)
--       resources_i(t+1) = resources_it - cost(purchases_it) + robots_it
-- Yes, an ILP :(

equality :: [(Int,String)] -> String -> Constraint
equality clauses var =
  SuchThat (((-1),var):clauses) Equal 0

equalInt :: String -> Int -> Constraint
equalInt var n =
  SuchThat [(1,var)] Equal n

-- ax1 + bx2 <= x3 iff
-- ax1 + bx2 - x3 <= 0
lte :: [(Int,String)] -> String -> Constraint
lte clauses var =
  SuchThat (((-1),var):clauses) Lte 0

chooseOne :: [String] -> Constraint
chooseOne vars =
  SuchThat (map (\v -> (1,v)) vars) Lte 1

-- gr_i = geode robots on start of minute i
-- br_i = obsidian robots on start of minute i
-- cl_i = clay robots on start of minute i
-- or_i = ore robots on start of minute i
-- b_i, c_i, o_i = obsidian, clay, ore inventory on start of minute i
-- build_g_i, build_b_i, build_c_i, build_o_i = decision to build in minute i, must sum to 0 or 1

mipProblem :: Recipe -> Int -> MipProblem
mipProblem r maxTime =
  MIP { objective = geodeSum,
        constraints = initState ++ buildAtMostOne ++ haveEnoughResources ++ nextMinute,
        boolVariables = buildVars } where
  buildVar m i = "build_" ++ m ++ "_" ++ (show i)
  robotVar m i = m ++ "r_" ++ (show i)
  invVar m i = m ++ "_" ++ (show i)
  buildVars = [ buildVar m i | m <- ["g", "b", "c", "o"], i <- [1..maxTime] ]
  -- maximize geodes built, one per robot that exists at the start of each minute
  geodeSum = [(1,robotVar "g" i) | i <- [1..maxTime]]
  -- start with one ore robot and nothing else
  initState = [equalInt (robotVar "o" 1) 1,
               equalInt (robotVar "c" 1) 0,
               equalInt (robotVar "b" 1) 0,
               equalInt (robotVar "g" 1) 0,
               equalInt (invVar "o" 1) 0,
               equalInt (invVar "c" 1) 0,
               equalInt (invVar "b" 1) 0]
  -- Choose at most one robot to build
  buildAtMostOne = [chooseOne [(buildVar "o" i), (buildVar "c" i),
                               (buildVar "b" i), (buildVar "g" i)]
                   | i <- [1..maxTime] ]
  -- Build choice must have enough resources
  resourceBound accessor var = [ lte [(accessor (oreCost r),buildVar "o" i),
                                      (accessor (clayCost r),buildVar "c" i),
                                      (accessor (obsidianCost r),buildVar "b" i),
                                      (accessor (geodeCost r),buildVar "g" i)]
                                 (var i) | i <- [1 .. maxTime] ]
  haveEnoughResources = (resourceBound ore (invVar "o")) ++
                        (resourceBound clay (invVar "c")) ++
                        (resourceBound obsidian (invVar "b"))
  -- resources = old - build costs + production
  nextResources m accessor = [ equality [(1,invVar m i),
                                         ((-1) * (accessor (oreCost r)),buildVar "o" i),
                                         ((-1) * (accessor (clayCost r)),buildVar "c" i),
                                         ((-1) * (accessor (obsidianCost r)),buildVar "b" i),
                                         ((-1) * (accessor (geodeCost r)),buildVar "g" i),
                                         (1,robotVar m i)]
                               (invVar m (i+1)) | i <- [1 .. maxTime - 1] ]
  -- robots = old + production
  nextRobots = [ equality [(1,robotVar m i),
                           (1,buildVar m i)]
                 (robotVar m (i+1)) | i <- [1 .. maxTime-1], m <- ["o", "c", "b", "g" ] ]
  nextMinute = nextRobots ++
               nextResources "o" ore ++
               nextResources "c" clay ++
               nextResources "b" obsidian 
                  
part1 :: [String] -> IO ()
part1 input = do
  putStrLn "Part 1"
  let recipes = mapMaybe parseRecipe input
      probs = map (\r -> mipProblem r 24) recipes
      rp = zip recipes probs
      run1 (r,p) = do
        out <- runCplex p ("part1-" ++ (show (recipeId r)))
        case out of
          Left e -> do
            putStrLn $ (show (recipeId r)) ++ " error: " ++  e
            return 0
          Right v -> do
            putStrLn $ (show (recipeId r)) ++ " geodes: " ++ (show v)
            return $ (recipeId r) * v            
    in do
    vals <- mapM run1 rp
    print (sum vals)

part2 :: [String] -> IO ()
part2 input = do
  putStrLn "Part 2"
  let recipes = take 3 $ mapMaybe parseRecipe input
      probs = map (\r -> mipProblem r 32) recipes
      rp = zip recipes probs
      run1 (r,p) = do
        out <- runCplex p ("part2-" ++ (show (recipeId r)))
        case out of
          Left e -> do
            putStrLn $ (show (recipeId r)) ++ " error: " ++  e
            return 0
          Right v -> do
            putStrLn $ (show (recipeId r)) ++ " geodes: " ++ (show v)
            return $ v            
    in do
    vals <- mapM run1 rp
    print (foldl1 (*) vals)

main :: IO ()
main = runOnLines part1 part2

