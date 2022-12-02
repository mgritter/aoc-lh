{-@ LIQUID "--max-case-expand=4" @-}
module Main (main) where

import System.Environment
import Data.Maybe (mapMaybe)

data RPS =
  Rock |
  Paper |
  Scissors

data Strategy =
  Lose |
  Draw |
  Win
  
data Game =
  FirstWin |
  SecondWin |
  Tie

-- beatsM X = Y means "X beats Y"
{-@ measure beatsM @-}
{-@ beatsM :: RPS -> RPS @-}
beatsM :: RPS -> RPS
beatsM Paper = Rock
beatsM Rock = Scissors
beatsM Scissors = Paper

{-@ beats :: x:RPS -> y:RPS -> {g:Game |
  (beatsM x = y => g = FirstWin) &&
  (beatsM y = x => g = SecondWin) &&
  (x = y  => g = Tie)} @-}
beats :: RPS -> RPS -> Game
beats Rock Paper = SecondWin
beats Paper Rock = FirstWin
beats Paper Scissors = SecondWin
beats Scissors Paper = FirstWin
beats Scissors Rock = SecondWin
beats Rock Scissors = FirstWin
beats _ _  = Tie

{-@ scoreForGame :: g:Game -> {s:Int | (g = FirstWin && s = 0) ||
  (g == SecondWin && s == 6) ||
  (g == Tie && s == 3) } @-}
scoreForGame :: Game -> Int
scoreForGame FirstWin = 0
scoreForGame Tie = 3
scoreForGame SecondWin = 6
{-@ measure scoreForGame @-}

-- is the score for the shape you selected (1 for Rock, 2 for Paper, and 3 for Scissors)
{-@ scoreForMove :: m:RPS -> {s:Int | (m = Rock && s = 1) ||
  (m = Paper && s = 2) ||
  (m = Scissors && s = 3) } @-}
scoreForMove :: RPS -> Int
scoreForMove Rock = 1
scoreForMove Paper = 2
scoreForMove Scissors = 3
{-@ measure scoreForMove @-}

-- {-@ testScore :: {x:Int | x = 9} @-}
-- testScore = scoreForGame SecondWin  + scoreForMove Scissors

-- The first column is what your opponent is going to play: A for Rock, B for Paper, and C for Scissors. The second column--" Suddenly, the Elf is called away to help with someone's tent.
-- The second column, you reason, must be what you should play in response: X for Rock, Y for Paper, and Z for Scissors. Winning every time would be suspicious, so the responses must have been carefully chosen.

{-@ die :: {v:_ | false} -> a @-}
die msg = error msg

{-@ parseMove :: s:String -> Maybe RPS @-}
parseMove :: String -> Maybe RPS
parseMove "A" = Just Rock
parseMove "B" = Just Paper
parseMove "C" = Just Scissors
parseMove "X" = Just Rock
parseMove "Y" = Just Paper
parseMove "Z" = Just Scissors
parseMove _ = Nothing

-- Why doesn't the specification help?
-- I think it was because --max-case-expand was not set yet
-- parseMove _ = die "Unexpected input"

--"Anyway, the second column says how the round needs to end: X means you need to lose, Y means you need to end the round in a draw, and Z means you need to win. Good luck!"
parseStrategy :: String -> Maybe Strategy
parseStrategy "X" = Just Lose
parseStrategy "Y" = Just Draw
parseStrategy "Z" = Just Win
parseStrategy _ = Nothing

parseMoves :: String -> Maybe (RPS, RPS)
parseMoves s = let tokens = words s in
  if length tokens /= 2 then
    Nothing
  else case (parseMove $ tokens !! 0, parseMove $ tokens !! 1) of
    (Just x, Just y) -> Just (x,y)
    _ -> Nothing

parseMoves2 :: String -> Maybe (RPS, Strategy)
parseMoves2 s = let tokens = words s in
  if length tokens /= 2 then
    Nothing
  else case (parseMove $ tokens !! 0, parseStrategy $ tokens !! 1) of
    (Just x, Just y) -> Just (x,y)
    _ -> Nothing

{-@ moveToScore :: g:(RPS,RPS) -> {s:Int |
  (beatsM (fst g) = (snd g) => s = scoreForGame FirstWin + scoreForMove (snd g)) &&
  (beatsM (snd g) = (fst g) => s = scoreForGame SecondWin + scoreForMove (snd g)) &&
  ((fst g) = (snd g) => s = scoreForGame Tie + scoreForMove (snd g))
  }
@-}
moveToScore :: (RPS,RPS) -> Int
moveToScore (x, y) = (scoreForGame (beats x y)) + (scoreForMove y)

-- In the first round, your opponent will choose Rock (A), and you should choose Paper (Y). This ends in a win for you with a score of 8 (2 because you chose Paper + 6 because you won).
{-@ test1 :: {s:Int | s = 8} @-}
test1 = moveToScore (Rock,Paper)

-- In the second round, your opponent will choose Paper (B), and you should choose Rock (X). This ends in a loss for you with a score of 1 (1 + 0).
{-@ test2 :: {s:Int | s = 1} @-}
test2 = moveToScore (Paper,Rock)

-- The third round is a draw with both players choosing Scissors, giving you a score of 3 + 3 = 6.
{-@ test3 :: {s:Int | s = 6} @-}
test3 = moveToScore (Scissors,Scissors)

part1 :: [String] -> IO ()
part1 input = do
  putStrLn "Part 1"
  print $ sum $ map moveToScore (mapMaybe parseMoves input)

{-@ ourMove :: x:RPS -> s:Strategy -> {y:RPS |
  (s = Draw => y = x) &&
  (s = Win => beatsM y = x) &&
  (s = Lose => beatsM x = y) } @-}
ourMove :: RPS -> Strategy -> RPS
ourMove x Draw = x
ourMove Paper Win = Scissors
ourMove Scissors Win = Rock
ourMove Rock Win = Paper
ourMove x Lose = beatsM x

computeMove (x,s) = (x,ourMove x s)

part2 :: [String] -> IO ()
part2 input = do
  putStrLn "Part 2"
  print $ sum $ map (moveToScore . computeMove) (mapMaybe parseMoves2 input)
  
main :: IO ()
main = do
  args <- getArgs
  if length args == 1 then do
    contents <- readFile (args !! 0)    
    let input = lines contents in
      part1 input >> part2 input
  else
    putStrLn "Must specify exactly one input file."

