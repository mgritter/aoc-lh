module Main (main) where
{-@ LIQUID "--no-termination" @-}

import LoadLines
import Data.List.Split
import Data.Maybe

data Instruction =
  Noop |
  Addx Int
  deriving (Show)

parseInstr :: String -> Maybe Instruction
parseInstr s = case (splitOneOf " " s) of
  (noop:[]) -> Just $ Noop
  ("addx":n:[]) -> Just $ Addx (read n)
  _ -> Nothing

-- This is state DURING the cycle "cycle", the instruction in progress
-- takes effect at the END of the cycle.
{-@
data CpuState =
  CPU { xReg :: Int,
        currCycle :: {n:Nat | n >= 1},
        inProgress :: Maybe Instruction,
        remainingCycles :: n:Nat }
@-}
data CpuState =
  CPU { xReg :: Int,
        currCycle :: Int,
        inProgress :: Maybe Instruction,
        remainingCycles :: Int }
  deriving (Show)

-- Emulate the start of a cycle (do all the end-of-cycle operations)
-- Return true if the instruction was consumed.
-- TODO: is there a better way we could have designed this to avoid the need to return whether
-- an instruction was consumed?
{-@ emulateCycle :: c:CpuState  ->
   Maybe Instruction ->
   {d:(CpuState,Bool) | currCycle (fst d) = currCycle c + 1 } @-}
emulateCycle :: CpuState -> Maybe Instruction -> ( CpuState, Bool )
emulateCycle cpu@(CPU x c ip remaining) instr = if remaining == 1 then
    (loadInstruction (finishInstruction cpu) instr, True)
  else if remaining == 0 then
    (CPU{ xReg = x, currCycle = c + 1, inProgress = ip, remainingCycles = 0 }, False)
  else
    (CPU{ xReg = x, currCycle = c + 1, inProgress = ip, remainingCycles = remaining - 1 }, False)

{-@ loadInstruction :: {c:CpuState | remainingCycles c = 0 && not isJust (inProgress c) } ->
   Maybe Instruction ->
   {d:CpuState | currCycle d = currCycle c && xReg c = xReg d } @-}
loadInstruction :: CpuState -> Maybe Instruction -> CpuState
loadInstruction cpu@(CPU x c Nothing 0) Nothing = cpu
loadInstruction cpu@(CPU x c Nothing 0) (Just Noop) =
  CPU x c (Just Noop) 1
loadInstruction cpu@(CPU x c Nothing 0) (Just (Addx n)) =
  CPU x c (Just (Addx n)) 2

-- comparison using = Nothing doesn't work, oops!
{-@ finishInstruction :: {c:CpuState | remainingCycles c = 1 } ->
    {d:CpuState | remainingCycles d = 0 &&
     currCycle d = currCycle c + 1 &&
     not isJust (inProgress d) &&
     ((isJust (inProgress d) && fromJust (inProgress d) = Noop ) => xReg c = xReg d ) }
@-}
finishInstruction :: CpuState -> CpuState
finishInstruction (CPU x c (Just Noop) 1) = CPU x (c+1) Nothing 0
finishInstruction (CPU x c (Just (Addx n)) 1) = CPU (x+n) (c+1) Nothing 0
finishInstruction (CPU x c Nothing 1) = CPU x (c+1) Nothing 0

-- Return a CpuState for every cycle
-- This return an infinite list so termination checking is disabled.
emulate :: CpuState -> [Instruction] -> [CpuState]
emulate cpu [] =
  let (endOfCycle, _) = emulateCycle cpu Nothing in
    cpu:(emulate endOfCycle [])
emulate cpu (next:instrs) =
  let (endOfCycle, consumed) = emulateCycle cpu (Just next) in
    if consumed then
      cpu:(emulate endOfCycle instrs)
    else
      cpu:(emulate endOfCycle (next:instrs))

-- TODO: why doesn't this fail due to the !! on a list of unknown length?
-- Does LH know that the list is unbounded?
-- {-@ fail signalStrength @-}
signalStrength :: [CpuState] -> Int
signalStrength states =
  20 * xReg (states !! 19) +
  60 * xReg (states !! 59) +
  100 * xReg (states !! 99) +
  140 * xReg (states !! 139) +
  180 * xReg (states !! 179) +
  220 * xReg (states !! 219)

showStates :: [CpuState] -> String
showStates ss = unlines $ map show ss

part1 :: [String] -> IO ()
part1 input = do
  putStrLn "Part 1"
  let instrs = mapMaybe parseInstr input in
    if length instrs == 0 then
      putStrLn "No instructions!"
    else
      let firstState =loadInstruction (CPU { xReg = 1, currCycle = 1, inProgress = Nothing, remainingCycles = 0 } ) (Just (head instrs)) in
        let states = (emulate firstState (tail instrs)) in do
          putStrLn (showStates (take 20 states))
          print $ signalStrength states

pixels :: [CpuState] -> String
pixels [] = "\n"
pixels (c:rest) =
  let spriteMiddle = xReg c
      pixelPos = (currCycle c - 1) `mod` 40
      newline = if pixelPos == 39 then "\n" else ""
  in
    if abs ( spriteMiddle - pixelPos ) <= 1 then
      "X" ++ newline ++ (pixels rest)
    else
      "." ++ newline ++ (pixels rest)
  
part2 :: [String] -> IO ()
part2 input = do
  putStrLn "Part 2"
  let instrs = mapMaybe parseInstr input in
    if length instrs == 0 then
      putStrLn "No instructions!"
    else
      let firstState =loadInstruction (CPU { xReg = 1, currCycle = 1, inProgress = Nothing, remainingCycles = 0 } ) (Just (head instrs)) in
        let states = (emulate firstState (tail instrs)) in do
          putStrLn $ (pixels (take 240 states))

main :: IO ()
main = runOnLines part1 part2

