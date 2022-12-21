module Main (main) where

import LoadLines
import qualified Data.Map as Map
import Data.List.Split
import Data.Either
import Data.Maybe
import Control.Monad.ST
import Control.Monad
import Data.STRef
import Data.Ratio

{-@
data Expr =
  Constant Int |
  Add { arg1::String, arg2 :: String} |
  Mul { arg1::String, arg2 :: String} |
  Div { arg1::String, arg2 :: String} |
  Sub { arg1::String, arg2 :: String}
@-}
data Expr =
  Constant Int |
  Add String String |
  Mul String String |
  Div String String |
  Sub String String
  deriving (Show)

{-@ data Monkey = M { name :: String, expr :: Expr } @-}
data Monkey = M { name :: String, expr :: Expr }
  deriving (Show)

--  0  1 2
-- sllz: 4
--  0   1 2   3  4
-- pppw: cczh / lfqf
parseMonkey :: String -> Maybe Monkey
parseMonkey s = let tok = splitOneOf " :" s in
  if length tok == 3 then
    Just $ M { name = (tok !! 0), expr = Constant (read (tok !! 2)) }
  else if length tok == 5 then case (tok !! 3) of
    "+" -> Just $ M { name = (tok !! 0), expr = Add (tok !! 2) (tok !! 4) }
    "-" -> Just $ M { name = (tok !! 0), expr = Sub (tok !! 2) (tok !! 4) }
    "/" -> Just $ M { name = (tok !! 0), expr = Div (tok !! 2) (tok !! 4) }
    "*" -> Just $ M { name = (tok !! 0), expr = Mul (tok !! 2) (tok !! 4) }
    _ -> Nothing
  else Nothing

type MExpr = Map.Map String Expr
type MVal = Map.Map String Int

evalMonkey :: MExpr -> String -> Either String Int
evalMonkey exprs val = runST (evalMonkeyST exprs val)

binOp :: (Int->Int->Int) -> (Either String Int) -> (Either String Int) -> (Either String Int)
binOp f a1 a2 =
  case (a1,a2) of
    (Left e, _) -> Left e
    (_, Left e) -> Left e
    (Right v1, Right v2) -> Right (f v1 v2)

divOp :: (Either String Int) -> (Either String Int) -> (Either String Int)
divOp a1 a2 =
  case (a1,a2) of
    (Left e, _) -> Left e
    (_, Left e) -> Left e
    (Right _, Right 0) -> Left "division by zero"
    (Right v1, Right v2) -> Right (div v1 v2)

-- Takes 6+ minutes to compile if not ignored!
{-@ ignore evalMonkeyST @-}
{-@ lazy evalMonkeyST @-}
evalMonkeyST :: MExpr -> String -> ST s (Either String Int)
evalMonkeyST exprs var = do
    vals <- newSTRef ( Map.empty :: MVal ) 
    helper var vals where
      helper :: String -> (STRef s MVal) -> ST s (Either String Int)
      helper monkeyName vals = do
        cache <- readSTRef vals
        case Map.lookup monkeyName cache of
          Just val -> return $ Right val
          Nothing -> do
            x <- case Map.lookup monkeyName exprs of
              Nothing -> return $ Left $ "Unknown variable " ++ monkeyName
              Just (Constant v) -> return $ Right v
              Just (Add m1 m2) -> do
                v1 <- helper m1 vals
                v2 <- helper m2 vals
                return $ binOp (+) v1 v2
              Just (Mul m1 m2) -> do
                v1 <- helper m1 vals
                v2 <- helper m2 vals
                return $ binOp (*) v1 v2
              Just (Div m1 m2) -> do
                v1 <- helper m1 vals
                v2 <- helper m2 vals
                return $ divOp v1 v2
              Just (Sub m1 m2) -> do
                v1 <- helper m1 vals
                v2 <- helper m2 vals
                return $ binOp (-) v1 v2
            _ <- case x of
              Left _ -> return $ ()
              Right intVal -> modifySTRef vals (Map.insert monkeyName intVal)
            return x
            

part1 :: [String] -> IO ()
part1 input = do
  putStrLn "Part 1"
  let monkeys = mapMaybe parseMonkey input
      monkeyMap = Map.fromList (map (\m -> (name m, expr m)) monkeys) in do
    -- print $ monkeys
    -- print $ monkeyMap
    case evalMonkey monkeyMap "root" of
      Left err -> putStrLn $ "Error: " ++ err
      Right val -> print $ val

{-@ data ExprTree =
  Equality { left::ExprTree, right:: ExprTree } |
  ConstantE (Ratio Int) |
  AddE {left :: ExprTree, right :: ExprTree} |
  MulE {left :: ExprTree, right :: ExprTree} |
  DivE {left :: ExprTree, right :: ExprTree} |
  SubE {left :: ExprTree, right :: ExprTree} |
  Human {scale :: (Ratio Int), constantTerm :: (Ratio Int) }
@-}
data ExprTree =
  Equality ExprTree ExprTree |
  ConstantE (Ratio Int) |
  AddE ExprTree ExprTree |
  MulE ExprTree ExprTree |
  DivE ExprTree ExprTree |
  SubE ExprTree ExprTree |
  Human (Ratio Int) (Ratio Int)
  deriving (Show)

{-@ lazy monkeyToTree @-}
monkeyToTree :: MExpr -> String -> Maybe ExprTree
monkeyToTree expr "humn" = Just $ Human (1 % 1) (0 % 1)
monkeyToTree expr "root" =
  case Map.lookup "root" expr of
    Nothing -> Nothing
    Just (Add m1 m2) -> (liftM2 Equality) (monkeyToTree expr m1) (monkeyToTree expr m2)
    _ -> Nothing
monkeyToTree expr m =
  case Map.lookup m expr of
    Nothing -> Nothing
    Just (Add m1 m2) -> (liftM2 AddE) (monkeyToTree expr m1) (monkeyToTree expr m2)
    Just (Sub m1 m2) -> (liftM2 SubE) (monkeyToTree expr m1) (monkeyToTree expr m2)
    Just (Mul m1 m2) -> (liftM2 MulE) (monkeyToTree expr m1) (monkeyToTree expr m2)
    Just (Div m1 m2) -> (liftM2 DivE) (monkeyToTree expr m1) (monkeyToTree expr m2)
    Just (Constant v) -> Just $ ConstantE (v % 1)

-- Simplify to 
-- constant = human * x / z  + y
--
-- simplify x = either Human or Equality or Constant
{-@ ignore simplify @-}
simplify :: ExprTree -> ExprTree
simplify (Human a b) = Human a b
simplify (ConstantE v) = ConstantE v
simplify (Equality a b) = Equality (simplify a) (simplify b)
simplify (AddE a b) =
  case (simplify a, simplify b) of
    (ConstantE va, ConstantE vb) -> ConstantE (va + vb)
    (ConstantE va, Human a b) -> Human a (va + b)
    (Human a b, ConstantE vb) -> Human a (vb + b)    
simplify (SubE a b) =
  case (simplify a, simplify b) of
    (ConstantE va, ConstantE vb) -> ConstantE (va - vb)
    (ConstantE va, Human a b) -> Human (-a) (va - b)
    (Human a b, ConstantE vb) -> Human a (b - vb)    
simplify (MulE a b) =
  case (simplify a, simplify b) of
    (ConstantE va, ConstantE vb) -> ConstantE (va * vb)
    (ConstantE va, Human a b) -> Human (va * a) (va * b)
    (Human a b, ConstantE vb) -> Human (a * vb) (b * vb)    
simplify (DivE a b) =
  case (simplify a, simplify b) of
    (ConstantE va, ConstantE vb) -> ConstantE (va / vb)
    (Human a b, ConstantE vb) -> Human (a / vb) (b / vb)    

-- human * n / d + c = x
-- human * n / d = x - c
-- human = ( x - c ) * d / n
{-@ ignore solve @-}
solve :: ExprTree -> Ratio Int
solve (Equality (Human a b) (ConstantE x)) = (x - b) / a
solve (Equality x (Human a b)) = solve (Equality (Human a b) x)
solve _ = 0

part2 :: [String] -> IO ()
part2 input = do
  putStrLn "Part 2"
  let monkeys = mapMaybe parseMonkey input
      monkeyMap = Map.fromList (map (\m -> (name m, expr m)) monkeys) in
    case monkeyToTree monkeyMap "root" of
      Nothing -> putStrLn "Tree construction error"
      Just exprTree ->
        let simpleTree = simplify exprTree in do
          print $ simpleTree
          print $ solve simpleTree

main :: IO ()
main = runOnLines part1 part2

