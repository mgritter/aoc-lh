module Main (main) where
{-@ LIQUID "--no-termination" @-}

import LoadLines
import Valve
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Sort
import Data.Either
import Data.Maybe
import Control.Exception

type Cavern = Map.Map String Valve

makeCavern :: [Valve] -> Cavern
makeCavern vs = Map.fromList (map (\v -> (name v, v)) vs)

defaultValve :: Valve
defaultValve = V "bad" 0 []

{-@
data SearchState =
  SS { timeRemaining :: Nat,
       pressureRelieved :: Nat,
       location :: String,
       opened :: Set.Set String,
       unopened :: [Nat],
       visited :: Set.Set String,
       record :: String
     }
@-}
data SearchState =
  SS { timeRemaining :: Int,
       pressureRelieved :: Int, -- projected value based on valves already opened
       location :: String,
       opened :: Set.Set String,
       unopened :: [Int],  -- track how many valves we could yet open, maximum first
       visited :: Set.Set String,  -- valves visited since last open
       record :: String
     }

-- Best-first search?  Maybe???
-- No, that's bogus.
--
-- DP on size [2^14, 50, 7300] == about 6 billion entries, too big
--
-- Branch and bound?

-- Upper bound says: what if we could get to the highest-valued remaining valves
-- in one move each?
{-@ upperBound :: ss:SearchState -> {n:Int | n >= pressureRelieved ss} / [timeRemaining ss] @-}
upperBound :: SearchState -> Int
upperBound ss =
  if timeRemaining ss == 0 then
    pressureRelieved ss
  else if length (unopened ss) == 0 then
    pressureRelieved ss
  else
    upperBound $ SS { timeRemaining = timeRemaining ss - 1,
                       pressureRelieved = (pressureRelieved ss) + (timeRemaining ss - 1) * (head $ unopened ss),
                       location = "",
                       opened = Set.empty,
                       unopened = tail (unopened ss),
                       visited = Set.empty,
                       record = "" }

-- Remove the first occurence of x from the list
removeFirst :: [Int] -> Int -> [Int]
removeFirst [] _ = []
removeFirst (y:ys) x = if x == y then ys else y:(removeFirst ys x)
  
{-@ moveState :: {ss:SearchState | timeRemaining ss > 0} -> Valve ->
  Maybe {ss2:SearchState | timeRemaining ss2 < timeRemaining ss} @-}
moveState :: SearchState -> Valve -> Maybe SearchState
moveState (SS time pressure loc open unopen visit r) valve =
  if not (Set.member (name valve) visit) then
    Just $ SS { timeRemaining = (time - 1),
                pressureRelieved = pressure,
                location = (name valve),
                opened = open,
                unopened = unopen,
                visited = visit `Set.union` (Set.singleton (name valve)),
                record = r ++ "Move to valve " ++ (name valve) ++ "\n"
              }
  else
    Nothing

{-@ closeState :: {ss:SearchState | timeRemaining ss > 0} ->
  {v:Valve | name v = location ss} ->
  [{ss2:SearchState | timeRemaining ss2 < timeRemaining ss}] @-}
closeState :: SearchState -> Valve -> [SearchState]
closeState (SS time pressure loc open unopen vist r) valve =
  if Set.member (name valve) open || flow_rate valve == 0 then
    []
  else
    [SS { timeRemaining = (time - 1),
          pressureRelieved = pressure + (time - 1) * (flow_rate valve),
          location = loc,
          opened = (Set.singleton (name valve)) `Set.union` open,
          unopened = removeFirst unopen (flow_rate valve),
          visited = Set.empty,
          record = r ++ "Open valve " ++ loc ++ " at time " ++ (show time) ++ "\n"
        }]

{-@ assume findByName :: Cavern -> l:String -> {v:Valve | name v = l } @-}
findByName :: Cavern -> String -> Valve
findByName cavern loc = Map.findWithDefault defaultValve loc cavern

-- Search for a solution better than "bestSoFar" from the given state
{-@ branchAndBound :: Cavern -> SearchState -> ss:SearchState -> Maybe SearchState / [ timeRemaining ss, 1000 ] @-}
branchAndBound :: Cavern -> SearchState -> SearchState -> Maybe SearchState
branchAndBound cavern bestSoFar ss@(SS time pressure loc open unopen visit r) =
  if time <= 0 then
    if pressure > pressureRelieved bestSoFar then Just $ ss else Nothing
  else if length unopen == 0 then
    if pressure > pressureRelieved bestSoFar then Just $ ss else Nothing
  else if upperBound ss < pressureRelieved bestSoFar then
    Nothing
  else if length nextStates >= 1000 then
    Nothing
  else
    recurseEach cavern ss bestSoFar False nextStates where
    here = findByName cavern loc
    nextValves = map (\l -> Map.findWithDefault defaultValve l cavern) (neighbors here)
    nextStates = if time <= 0 then [] else
                   closeState ss here ++
                   (mapMaybe (moveState ss) nextValves)

{-@ recurseEach :: Cavern -> prev:SearchState -> SearchState -> Bool
  -> x:[{s:SearchState | timeRemaining s < timeRemaining prev}]
  -> Maybe SearchState / [ timeRemaining prev, len x ] @-}
recurseEach :: Cavern -> SearchState -> SearchState -> Bool -> [SearchState] -> Maybe SearchState
recurseEach _ _ ub True [] = Just ub
recurseEach _ _ ub False [] = Nothing    
recurseEach cavern prev ub improved (x:xs) =
  case (branchAndBound cavern ub x) of
    Nothing -> recurseEach cavern prev ub improved xs
    Just betterResult -> recurseEach cavern prev betterResult True xs

part1 :: [String] -> IO ()
part1 input = do
  putStrLn "Part 1"
  let errors = lefts $ map parseV input
      valves = rights $ map parseV input in
    if length errors > 0 then
      putStrLn (head errors)
    else
      let startState = SS {
            timeRemaining = 30,
            pressureRelieved = 0,
            location = "AA",
            opened = Set.empty,
            unopened = sortBy (\a b -> compare b a) (filter (\x -> x > 0) (map flow_rate valves)),
            record = "",
            visited = Set.empty
            } in do
        putStrLn $ "Unopened = " ++ (show $ unopened startState )
        putStrLn $ "Initial bound = " ++ (show $ upperBound startState) 
        case branchAndBound (makeCavern valves) startState startState of
          Just v -> do
            print $ (pressureRelieved v)
            putStrLn (record v)
          Nothing -> putStrLn "Oops, no solution?!?"

part2 :: [String] -> IO ()
part2 input = do
  putStrLn "Part 2"

main :: IO ()
main = runOnLines part1 part2

