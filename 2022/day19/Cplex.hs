module Cplex(
  Bound(Equal,Gte,Lte),
  Constraint(SuchThat),
  MipProblem(MIP,objective, constraints, boolVariables),
  cplexFormat,
  runCplex
    ) where

import Data.List
import System.Process
import System.Exit

data Bound =
  Equal |
  Gte |
  Lte
  deriving (Show)

data Constraint =
  SuchThat [(Int,String)] Bound Int
  deriving (Show)

data MipProblem =
  MIP {
     objective :: [(Int,String)],
     constraints :: [Constraint],
     boolVariables :: [String]
  }
  deriving (Show)

showLinear :: [(Int,String)] -> String
showLinear ts = intercalate " " (map showTerm ts) where
  showTerm (coeff,var) = if coeff < 0 then
    (show coeff) ++ " " ++ var
  else
    "+" ++ (show coeff) ++ " " ++ var

showBound :: Bound -> String
showBound Equal = " = "
showBound Gte = " >= "
showBound Lte = " <= "

showConstraint :: Constraint -> String
showConstraint (SuchThat lt bound val) =
  (showLinear lt) ++ (showBound bound) ++ (show val)
              
cplexFormat :: MipProblem -> String
cplexFormat p =
  "Maximize\n" ++
  showLinear (objective p) ++
  "\nSubject To\n" ++
  (unlines $ map showConstraint (constraints p)) ++
  "\nBinary\n" ++
  (unlines (boolVariables p))
  ++ "\nEnd\n"

writeCplexFile :: MipProblem -> String -> IO ()
writeCplexFile p fn =
  writeFile fn (cplexFormat p)

objPrefix = "c Objective:  obj = "

parseSolutionFile :: String -> IO (Either String Int)
parseSolutionFile fn = do
  contents <- readFile fn
  -- Looks like:
  -- c Objective:  obj = 9 (MAXimum)
  let objOut = filter (isPrefixOf objPrefix) (lines contents) in
    if length objOut == 0 then return $ Left "Objective not found"
    else let w = words (head objOut) in
      if length w < 5 then
        return $ Left "Objective missing"
      else
        return $ Right (read (w !! 4))
        
runCplex :: MipProblem -> String -> IO (Either String Int)
runCplex p fn =
  let lpFile = "2022/day19/" ++ fn ++ ".cplex"
      solFile = "2022/day19/" ++ fn ++ ".sol"  in do
    _ <- writeCplexFile p lpFile
    (rc, out, error) <- readProcessWithExitCode "/usr/bin/glpsol" [ "--lp", lpFile, "-w", solFile ] ""
    if rc /= ExitSuccess then
      return $ Left error
    else
      parseSolutionFile solFile
    
