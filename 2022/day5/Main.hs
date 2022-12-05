module Main (main) where

import LoadLines
import Data.Maybe
import Data.List (foldl')
import Data.List.Split

data Stack =
  Empty |
  Box String Stack

{-@ measure empty @-}
empty :: Stack -> Bool
empty Empty = True
empty _ = False

{-@ top :: {s:Stack | not empty s} -> String @-}
top :: Stack -> String
top (Box x _) = x

{-@ pop :: {s:Stack | not empty s} -> Stack @-}
pop :: Stack -> Stack
pop (Box _ y) = y

{-@ push :: String -> Stack -> Stack @-}
push :: String -> Stack -> Stack
push item stack = Box item stack

{-@ data Cargo = Stacks { numStacks :: Nat,
                          stacks :: {s:[Stack] | len s = numStacks} }         
  @-}
data Cargo =
  Stacks  { numStacks :: Int
          , stacks :: [Stack]  }

{-@ type InRange c = {i:Int | 1 <= i && i <= numStacks c} @-}

-- FIXME: how can we prove that stacks !! i is the only thing that changed
-- in c2 compared with c?
{-@ replaceStack :: c:Cargo -> pos:InRange c
  -> s:Stack -> {c2:Cargo | numStacks c2 = numStacks c} @-}
replaceStack :: Cargo -> Int -> Stack -> Cargo
replaceStack c position newstack =
  let oldstacks = stacks c in
  Stacks { numStacks = numStacks c,
           stacks = (take (position - 1) oldstacks) ++ [newstack] ++ (drop position  oldstacks ) }

{-@ pickUp :: c:Cargo -> pos:Int -> Maybe (String, Cargo) @-}
pickUp :: Cargo -> Int -> Maybe (String, Cargo)
pickUp c position | position > numStacks c = Nothing
pickUp c position | position <= 0 = Nothing
pickUp c position = let s = (stacks c) !! (position - 1) in
  if empty s then Nothing
  else Just (top s, replaceStack c position (pop s))

{-@ place :: c:Cargo -> pos:Int -> String -> Maybe Cargo @-}
place :: Cargo -> Int -> String -> Maybe Cargo
place c position label | position > numStacks c = Nothing
place c position label | position <= 0 = Nothing
place c position label = let s = (stacks c) !! (position - 1) in
  Just $ replaceStack c position (push label s)

{-@ topBoxes :: Cargo -> String @-}
topBoxes :: Cargo -> String
topBoxes c = concat $ map topOrNull (stacks c)
  where topOrNull s = if empty s then "" else top s

{-@ data Operation = Move { numBoxes :: {n:Int | n >= 1},
                            fromStack :: {n:Int | n >= 1},
                            toStack :: {n:Int | n >= 1} } @-}
data Operation =
  Move  { numBoxes :: Int
        , fromStack :: Int
        , toStack :: Int }

parseOperation :: String -> Maybe Operation
parseOperation s = let tokens = splitOneOf " " s in
  if length tokens /= 6 then Nothing else
    let nb = (read (tokens !! 1))
        fs = (read (tokens !! 3))
        ts = (read (tokens !! 5)) in
      if nb >= 1 && fs >= 1 && ts >= 1 then
        Just $ Move nb fs ts
      else
        Nothing

applySingle :: Maybe Cargo -> Maybe Operation -> Maybe Cargo
applySingle Nothing _ = Nothing
applySingle _ Nothing = Nothing
applySingle (Just c) (Just op) = case (pickUp c (fromStack op)) of
  Nothing -> Nothing
  Just (item, c') -> (place c' (toStack op) item)

applyOperation :: Maybe Cargo -> Maybe Operation -> Maybe Cargo
applyOperation Nothing _ = Nothing
applyOperation _ Nothing = Nothing
applyOperation (Just c) (Just op) = foldl' applySingle (Just c) (replicate (numBoxes op) (Just op))

-- Boxes are returned top-first: [A,B,C]
{-@ pickUpN :: c:Cargo -> pos:Int -> {num:Int | num >= 0} ->
  Maybe ({boxes:[String] | len boxes = num}, Cargo) / [num]  @-}
pickUpN :: Cargo -> Int -> Int -> Maybe ([String], Cargo)
pickUpN c position _ | position > numStacks c = Nothing
pickUpN c position _ | position <= 0 = Nothing
pickUpN c position 0 = Just ([], c)
pickUpN c position num = 
  let s = (stacks c) !! (position - 1) in
  if empty s then Nothing
  else let remainder = pickUpN (replaceStack c position (pop s)) position (num-1) in
    case remainder of
      Nothing -> Nothing
      Just (boxes,finalc) -> Just ((top s):boxes, finalc)

-- Boxes are given top-first: [A,B,C]
{-@ placeN :: c:Cargo -> pos:Int -> [String] ->
    Maybe {c2:Cargo | numStacks c2 = numStacks c} @-}
placeN :: Cargo -> Int -> [String] -> Maybe Cargo
placeN c position labels | position > numStacks c = Nothing
placeN c position labels | position <= 0 = Nothing
placeN c position [] = Just c
placeN c position (top:rest) = let result = placeN c position rest in
  case result of
    Nothing -> Nothing
    Just c' -> let s = (stacks c') !! (position - 1) in  
      Just $ replaceStack c' position (push top s)

                             
applyOperation2 :: Maybe Cargo -> Maybe Operation -> Maybe Cargo
applyOperation2 Nothing _ = Nothing
applyOperation2 _ Nothing = Nothing
applyOperation2 (Just c) (Just op) =
  case pickUpN c (fromStack op) (numBoxes op) of
    Nothing -> Nothing
    Just (boxes,c') ->
      placeN c' (toStack op) boxes

{-
    [D]    
[N] [C]    
[Z] [M] [P]
 1   2   3
  -}
part1Example = Stacks 3 [
  Box "N" (Box "Z" Empty),
  Box "D" (Box "C" (Box "M" Empty)),
  Box "P" Empty ]

{-
                [V]     [C]     [M]
[V]     [J]     [N]     [H]     [V]
[R] [F] [N]     [W]     [Z]     [N]
[H] [R] [D]     [Q] [M] [L]     [B]
[B] [C] [H] [V] [R] [C] [G]     [R]
[G] [G] [F] [S] [D] [H] [B] [R] [S]
[D] [N] [S] [D] [H] [G] [J] [J] [G]
[W] [J] [L] [J] [S] [P] [F] [S] [L]
 1   2   3   4   5   6   7   8   9 
-}

stringToStack :: String -> Stack
stringToStack [] = Empty
stringToStack (b:rest) = Box [b] (stringToStack rest)

realInput = Stacks 9 [
  stringToStack "VRHBGDW",
  stringToStack "FRCGNJ",
  stringToStack "JNDHFSL",
  stringToStack "VSDJ",
  stringToStack "VNWQRDHS",
  stringToStack "MCHGP",
  stringToStack "CHZLGBJF",
  stringToStack "RJS",
  stringToStack "MVNBRSGL" ]

startStack = realInput

part1 :: [String] -> IO ()
part1 input = do
  putStrLn "Part 1"
  let operations = map parseOperation input in
    case foldl' applyOperation (Just startStack) operations of
      Nothing -> putStrLn "Error!"
      Just c -> print $ topBoxes c

part2 :: [String] -> IO ()
part2 input = do
  putStrLn "Part 2"
  let operations = map parseOperation input in
    case foldl' applyOperation2 (Just startStack) operations of
      Nothing -> putStrLn "Error!"
      Just c -> print $ topBoxes c
      
main :: IO ()
main = runOnLines part1 part2
