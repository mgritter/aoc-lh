module Main (main) where

import LoadLines
import Data.List.Split
import Data.List
import Data.Maybe

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
  deriving (Show)

{-@ totalResources :: Resources -> Nat @-}
totalResources :: Resources -> Int
totalResources r = ore r + clay r + obsidian r + geode r
{-@ inline totalResources @-}

{-@ add :: r1:Resources -> r2:Resources -> {s:Resources |
  ore s = ore r1 + ore r2 &&
  clay s = clay r1 + clay r2 &&
  obsidian s = obsidian r1 + obsidian r2 &&
  geode s = geode r1 + geode r2
} @-}
add :: Resources -> Resources -> Resources
add r1 r2 = RS {
  ore = ore r1 + ore r2,
  clay = clay r1 + clay r2,
  obsidian = obsidian r1 + obsidian r2,
  geode = geode r1 + geode r2
  }

mult :: Int -> Resources -> Resources
mult s r1 = RS {
  ore = s * ore r1,
  clay = s * clay r1,
  obsidian = s * obsidian r1,
  geode = s * geode r2
  }

-- True if r1 >= r2 pointwise
resourceGte :: Resources -> Resources -> Bool
resourceGte r1 r2 =
  ore r1 >= ore r2 &&
  clay r1 >= clay r2 &&
  obsidian r1 >= obsidian r2 &&
  geode r1 >= geode r2
{-@ inline resourceGte @-}

{-@ sub :: a:Resources -> {b:Resources | resourceGte a b && totalResources b > 0}
 -> {c:Resources | totalResources c = totalResources a - totalResources b} @-}
sub :: Resources -> Resources -> Resources
sub r1 r2 = RS {
  ore = ore r1 - ore r2,
  clay = clay r1 - clay r2,
  obsidian = obsidian r1 - obsidian r2,
  geode = geode r1 - geode r2
  }
  
{-@ 
data SearchState =
  SS { timeRemaining :: Nat,
       resources :: Resources,
       robots :: Resources,
       report :: String }
@-}
data SearchState =
  SS { timeRemaining :: Int,
       resources :: Resources,
       robots :: Resources,
       report :: String }

{-@
data Recipe =
  RC { recipeId :: Nat,
       costs :: [({robot:Resources | ore robot + clay robot + obsidian robot + geode robot = 1},
                  {costs:Resources | totalResources costs > 0})]
     }
@-}
data Recipe =
  RC { recipeId :: Int,
       costs :: [(Resources,Resources)] -- List of (robot, cost) pairs
     }

-- Return all possibilities for what we can build with the existing resources
-- List is (new robots, remaining resources)
{-@ canBuild :: recipe:Recipe -> avail:Resources -> {options:[(Resources,Resources)] | len options > 0}
   / [ len (costs recipe), totalResources avail ]
@-}
canBuild :: Recipe -> Resources -> [(Resources,Resources)]
canBuild (RC _ []) available = [(RS 0 0 0 0, available)]
canBuild orig@(RC i ((newRobots, costs):rest)) available =
          if available `resourceGte` costs then
            (canBuild (RC i rest) available) ++
            (map
              (\(r,c) -> (add newRobots r, c))
              (canBuild orig (sub available costs)))
          else
            canBuild (RC i rest) available
    

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
      costs = [
          (RS 1 0 0 0, RS c1 0 0 0),
          (RS 0 1 0 0, RS c2 0 0 0),
          (RS 0 0 1 0, RS c3 c4 0 0),
          (RS 0 0 0 1, RS c5 0 c6 0)
          ] }
    else
      Nothing

-- Plan: DFS (really?)
-- Later: come up with bound and do branch-and-bound?

-- Initial plan: search time by time
{-@ successors :: Recipe -> {s:SearchState | timeRemaining s > 0}
  -> [{succ:SearchState | timeRemaining succ = timeRemaining s - 1}] @-}
successors :: Recipe -> SearchState -> [SearchState]
successors r s =
  map nextTimePeriod (canBuild r (resources s)) where
    nextTimePeriod (newRobots, remaining) =
      let resourcesAtEnd = add (robots s) remaining in
        SS { timeRemaining = timeRemaining s - 1,
             resources = resourcesAtEnd,
             robots = add (robots s) newRobots,
             report = (report s) ++ "Time " ++ (show (timeRemaining s)) ++ " built " ++ (show newRobots) ++ " have " ++ (show resourcesAtEnd) ++ "\n" }

-- The current search tree looks like:
--             N
--        ore / \ do nothing
--              N+1
--             /  \ do nothing
--           ore  N+2
--                / \ do nothing
--
-- Should we prune 'ore' from our choices after passing on it?  Or pick our next "purchase" and
-- wait until that is feasible?

-- Is it a LP?
--
-- (robots_it, resources_it, purchases_it)
--   s.t resources_it >= cost (purchases_it)
--       robots_i(t+1) = robots_i(t) + purchases_i(t)
--       resources_i(t+1) = resources_it - cost(purchases_it) + robots_it
-- Yes, an ILP :(

-- Return the next time when the given amount of resources are available, or Nothing if never
{-@ timeAvailable :: SearchState -> r:Resources -> Maybe {s2:SearchState | resourceGte (resources s2) r} @-}
timeAvailable :: SearchState -> Resources -> Maybe SearchState
timeAvailable ss needed =
  let timeNeeded target production =
        if production == 0 then
          if req > 0 then Nothing else Some $ 0
        else Some $ (target + production - 1) `div` production
      timeNeeded2 have need production =
        if have < need then timeNeeded (need - have) production else Some $ 0
      timeVector = [timeNeeded2 (ore (resources ss)) (ore needed) (ore (robots ss)),
                    timeNeeded2 (clay (resources ss)) (clay needed) (clay (robots ss)),
                    timeNeeded2 (obsidian (resources ss)) (obsidian needed) (obsidian (robots ss)),
                    timeNeeded2 (quartz (resources ss)) (quartz needed) (quartz (robots ss))]
      t = maximum $ map (fromMaybe 1000) timeVector in
    if t == 1000 then None
    else advanceTime t ss

advanceTime :: SearchState -> Int -> Maybe SearchState
advanceTime ss t =
  if (timeRemaining ss) > t then Nothing
  else SS {
    timeRemaining = timeRemaining - t,
    resources = add (resources ss) (mult t (robots ss)),
    robots = robots ss,
    report = report ss ++ "Wait " ++ (show t ) ++ " minutes\n"
    }

{-@ successors2 :: Recipe -> {s:SearchState | timeRemaining s > 0}
  -> [{succ:SearchState | timeRemaining succ < timeRemaining s ||
                          resourceGte (resources s) (resources succ) }] @-}
successors2 :: Recipe -> SearchState -> [SearchState]
successors2 r s =
  ifEmptyThenAdvanceTime (mapMaybe buildNext (costs r)) where
  buildNext (robot,cost) =
    case timeAvailable s cost of
      Nothing -> Nothing
      Just future -> 
        SS { timeRemaining = timeRemaining s - 1,
             resources = resourcesAtEnd,
             robots = add (robots s) newRobots,
             report = (report s) ++ "Time " ++ (show (timeRemaining s)) ++ " built " ++ (show newRobots) ++ " have " ++ (show resourcesAtEnd) ++ "\n" }
      
  
  map nextTimePeriod (canBuild r (resources s)) where
    nextTimePeriod (newRobots, remaining) =
      let resourcesAtEnd = add (robots s) remaining in
        SS { timeRemaining = timeRemaining s - 1,
             resources = resourcesAtEnd,
             robots = add (robots s) newRobots,
             report = (report s) ++ "Time " ++ (show (timeRemaining s)) ++ " built " ++ (show newRobots) ++ " have " ++ (show resourcesAtEnd) ++ "\n" }


orderByGeodes :: SearchState -> SearchState -> Ordering
orderByGeodes a b = compare (geode (resources a)) (geode (resources b))

{-@ dfsMostGeodes :: Recipe -> s:SearchState -> SearchState
  / [timeRemaining s] @-}
dfsMostGeodes :: Recipe -> SearchState -> SearchState
dfsMostGeodes recipe start =
  if timeRemaining start == 0 then start else
    let ss = successors recipe start in
      maximumBy orderByGeodes (map (dfsMostGeodes recipe) ss)

initState :: SearchState
initState = SS { timeRemaining = 24,
                 resources = RS 0 0 0 0,
                 robots = RS 1 0 0 0,
                 report = "" }
  
qualityLevel :: Recipe -> Int
qualityLevel r =
  let maxG = dfsMostGeodes r initState in
    (geode (resources maxG)) * (recipeId r)

part1 :: [String] -> IO ()
part1 input = do
  putStrLn "Part 1"
  let recipes = mapMaybe parseRecipe input
      qls = map (\r -> (r, qualityLevel r)) recipes in do
    if length recipes >= 2 then do
      putStrLn (report $ dfsMostGeodes (recipes !! 0) initState)
      putStrLn (report $ dfsMostGeodes (recipes !! 1) initState)
    else
      putStrLn "Too few recipes!"
    _ <- mapM (\(r,q) -> 
                  putStrLn $ "Recipe " ++ (show (recipeId r)) ++ " quality " ++ (show q)) qls
    print (sum $ map snd qls)

part2 :: [String] -> IO ()
part2 input = do
  putStrLn "Part 2"

main :: IO ()
main = runOnLines part1 part2

