module LoadLines(runOnLines) where

import System.Environment

-- Main function that reads all the lines in a file and sends them
-- to the part1 and part2 functions
runOnLines :: ([String]->IO()) -> ([String]->IO()) -> IO ()
runOnLines part1 part2 = do
  args <- getArgs
  if length args == 1 then do
    contents <- readFile (args !! 0)    
    let input = lines contents in
      part1 input >> part2 input
  else
    putStrLn "Must specify exactly one input file."
