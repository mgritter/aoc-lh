module Main (main) where
-- {-@ LIQUID "--no-termination" @-}

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
       locationElephant :: String,
       opened :: Set.Set String,
       unopened :: [Nat],
       visited :: Set.Set String,
       visitedElephant :: Set.Set String,
       record :: String
     }
@-}
data SearchState =
  SS { timeRemaining :: Int,
       pressureRelieved :: Int, -- projected value based on valves already opened
       location :: String,
       locationElephant :: String,
       opened :: Set.Set String,
       unopened :: [Int],  -- track how many valves we could yet open, maximum first
       visited :: Set.Set String,  -- valves visited since last open
       visitedElephant :: Set.Set String,
       record :: String
     }

-- Using timeRemaining for termination checking was giving bad results.
-- Using this metric is better, I think because it has codomain Nat
-- (at least, I guess that is the part that the termination checker could not prove.)
{-@ tr :: SearchState -> Nat @-}
tr :: SearchState -> Int
tr (SS time _ _ _ _ _ _ _ _ ) = time
{-@ measure tr @-}

-- Best-first search?  Maybe???
-- No, that's bogus.
--
-- DP on size [2^14, 50, 7300] == about 6 billion entries, too big
--
-- Branch and bound?

{-@ sumNats :: [Nat] -> Nat @-}
sumNats :: [Int] -> Int
sumNats [] = 0
sumNats (x:xs) = x + sumNats xs

-- Upper bound says: what if we could get to the highest-valued remaining valves
-- in two moves each (or one for the first one?)
{-@ upperBound :: {step:Nat | step > 0} -> ss:SearchState -> {n:Int | n >= pressureRelieved ss} / [tr ss] @-}
upperBound :: Int -> SearchState -> Int
upperBound step ss =
  if tr ss < step then
    pressureRelieved ss
  else if length (unopened ss) == 0 then
    pressureRelieved ss
  else if locationElephant ss == "none" then
    -- Every two steps we move to a new valve and open it
    upperBound 2 $ SS { timeRemaining = tr ss - step,
                        pressureRelieved = (pressureRelieved ss) + (tr ss - step) * (head $ unopened ss),
                        location = "",
                        locationElephant = "none",
                        opened = Set.empty,
                        unopened = tail (unopened ss),
                        visited = Set.empty,
                        visitedElephant = Set.empty,
                        record = "" }
  else
    -- Every two steps both we and the elephant move to a new valve and open it.
    upperBound 2  $ SS { timeRemaining = tr ss - step,
                         pressureRelieved = (pressureRelieved ss) + (tr ss - step) * (sumNats (take 2 $ unopened ss)),
                         location = "",
                         locationElephant = "",
                         opened = Set.empty,
                         unopened = (drop 2 (unopened ss)),
                         visited = Set.empty,
                         visitedElephant = Set.empty,
                         record = "" }
    
-- Remove the first occurence of x from the list
removeFirst :: [Int] -> Int -> [Int]
removeFirst [] _ = []
removeFirst (y:ys) x = if x == y then ys else y:(removeFirst ys x)
  
{-@ moveState :: {ss:SearchState | tr ss > 0} -> Valve ->
  Maybe {ss2:SearchState | tr ss2 < tr ss} @-}
moveState :: SearchState -> Valve -> Maybe SearchState
moveState (SS time pressure loc locE open unopen visit visitE r) valve =
  if not (Set.member (name valve) visit) then
    Just $ SS { timeRemaining = (time - 1),
                pressureRelieved = pressure,
                location = (name valve),
                locationElephant = locE,
                opened = open,
                unopened = unopen,
                visited = visit `Set.union` (Set.singleton (name valve)),
                visitedElephant = visitE,
                record = r ++ "Move to valve " ++ (name valve) ++ "\n"
              }
  else
    Nothing

{-@ closeState :: {ss:SearchState | tr ss > 0} ->
  {v:Valve | name v = location ss} ->
  [{ss2:SearchState | tr ss2 < tr ss}] @-}
closeState :: SearchState -> Valve -> [SearchState]
closeState (SS time pressure loc locE open unopen visit visitE r) valve =
  if Set.member (name valve) open || flow_rate valve == 0 then
    []
  else
    [SS { timeRemaining = (time - 1),
          pressureRelieved = pressure + (time - 1) * (flow_rate valve),
          location = loc,
          locationElephant = locE,
          opened = (Set.singleton (name valve)) `Set.union` open,
          unopened = removeFirst unopen (flow_rate valve),
          visited = Set.empty,
          visitedElephant = visitE,          
          record = r ++ "Open valve " ++ loc ++ " at time " ++ (show time) ++ "\n"
        }]

{-@ assume findByName :: Cavern -> l:String -> {v:Valve | name v = l } @-}
findByName :: Cavern -> String -> Valve
findByName cavern loc = Map.findWithDefault defaultValve loc cavern

{-@ assume Data.Maybe.mapMaybe :: (a -> Maybe b) -> l1:[a] -> {l2:[b] | len l2 <= len l1} @-}

{-@ nextStatesPart1 :: Cavern -> curr:SearchState -> [{s:SearchState | tr s < tr curr}] @-}
nextStatesPart1 :: Cavern -> SearchState -> [SearchState]
nextStatesPart1 cavern ss =
  if tr ss <= 0 then []
  else closeState ss here ++
       (mapMaybe (moveState ss) nextValves)
  where
    here = findByName cavern (location ss)
    nextValves = map (\l -> Map.findWithDefault defaultValve l cavern) (neighbors here)

{-@ type MoveGen = (Cavern -> s1:SearchState ->  [{s2:SearchState | tr s2 < tr s1}]) @-}
type MoveGen = Cavern-> SearchState ->  [SearchState]

-- Search for a solution better than "bestSoFar" from the given state
{-@ branchAndBound :: MoveGen ->
  Cavern -> SearchState -> ss:SearchState -> Maybe SearchState / [ tr ss, 1000 ] @-}
branchAndBound :: MoveGen -> Cavern ->
  SearchState -> SearchState -> Maybe SearchState
branchAndBound nextStatesGen cavern bestSoFar ss =
  if timeRemaining ss <= 0 then
    if pressureRelieved ss > pressureRelieved bestSoFar then Just $ ss else Nothing
  else if length (unopened ss) == 0 then
    if pressureRelieved ss > pressureRelieved bestSoFar then Just $ ss else Nothing
  else if upperBound 1 ss < pressureRelieved bestSoFar then
    Nothing
  else
    -- Completely artificial limit because 1000 = "infinity" here for termination checking.
    let nextStates = (take 900 (nextStatesGen cavern ss)) in
      recurseEach bestSoFar False nextStates
    where
      {-@ recurseEach :: lb:SearchState -> Bool
           -> x:[{s:SearchState | tr s < tr ss}]
           -> Maybe SearchState / [ tr ss, len x ] @-}
      recurseEach :: SearchState -> Bool -> [SearchState] -> Maybe SearchState
      recurseEach lb True [] = Just lb
      recurseEach _ False [] = Nothing    
      recurseEach lb improved (x:xs) =
        case (branchAndBound nextStatesGen cavern lb x) of
          Nothing -> recurseEach lb improved xs
          Just betterResult -> recurseEach betterResult True xs
      
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
            locationElephant = "none",
            opened = Set.empty,
            unopened = sortBy (\a b -> compare b a) (filter (\x -> x > 0) (map flow_rate valves)),
            record = "",
            visited = Set.empty,
            visitedElephant = Set.empty
            } in do
        putStrLn $ "Unopened = " ++ (show $ unopened startState )
        putStrLn $ "Initial bound = " ++ (show $ upperBound 1 startState) 
        case branchAndBound nextStatesPart1 (makeCavern valves) startState startState of
          Just v -> do
            print $ (pressureRelieved v)
            putStrLn (record v)
          Nothing -> putStrLn "Oops, no solution?!?"

-- TODO: what if the human can move but the elephant can't or vice versa?
-- seems unlikely
{-@ elephantMoves :: Cavern -> human:SearchState -> [{s:SearchState | tr s = tr human}] @-}
elephantMoves :: Cavern -> SearchState -> [SearchState]
elephantMoves cavern hs = mapMaybe moveTo (neighbors here)
  where
    here = findByName cavern (locationElephant hs)
    moveTo valveName
      = if Set.member valveName (visitedElephant hs) then
          Nothing
        else
          Just $ hs { locationElephant = valveName,
                      visitedElephant = (visitedElephant hs) `Set.union` (Set.singleton valveName),
                      record = (record hs) ++ "Elphant move to valve " ++ valveName ++ "\n" }

{-@ elephantClose :: Cavern -> human:SearchState -> [{s:SearchState | tr s = tr human}] @-}
elephantClose :: Cavern -> SearchState -> [SearchState]
elephantClose cavern hs =
  (if Set.member (name here) (opened hs) || flow_rate here == 0 then
     []
   else
     [ hs { pressureRelieved = (pressureRelieved hs) + (timeRemaining hs) * (flow_rate here),
            opened = (Set.singleton (name here)) `Set.union` (opened hs),
            unopened = removeFirst (unopened hs) (flow_rate here),
            visitedElephant = Set.empty,
            record = (record hs) ++ "Open valve " ++ (name here) ++ " at time " ++ (show (1 + timeRemaining hs)) ++ "\n"
          }
     ]
  ) where here = findByName cavern (locationElephant hs)

{-@ nextStatesPart2 :: Cavern -> curr:SearchState -> [{s:SearchState | tr s < tr curr}] @-}
nextStatesPart2 :: Cavern -> SearchState -> [SearchState]
nextStatesPart2 cavern ss =
  if tr ss <= 0 then []
  else (humanMoves >>= (elephantClose cavern)) ++ (humanMoves >>= (elephantMoves cavern))
  where humanMoves = nextStatesPart1 cavern ss


part2 :: [String] -> IO ()
part2 input = do
  putStrLn "Part 2"
  let errors = lefts $ map parseV input
      valves = rights $ map parseV input in
    if length errors > 0 then
      putStrLn (head errors)
    else
      let startState = SS {
            timeRemaining = 26,
            pressureRelieved = 0,
            location = "AA",
            locationElephant = "AA",
            opened = Set.empty,
            unopened = sortBy (\a b -> compare b a) (filter (\x -> x > 0) (map flow_rate valves)),
            record = "",
            visited = Set.empty,
            visitedElephant = Set.empty
            } in do
        putStrLn $ "Unopened = " ++ (show $ unopened startState )
        putStrLn $ "Initial bound = " ++ (show $ upperBound 1 startState) 
        case branchAndBound nextStatesPart2 (makeCavern valves) startState startState of
          Just v -> do
            print $ (pressureRelieved v)
            putStrLn (record v)
          Nothing -> putStrLn "Oops, no solution?!?"


main :: IO ()
main = runOnLines part1 part2

