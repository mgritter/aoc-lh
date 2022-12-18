module Maximum (maximum, member, maximumIsGte) where

import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (maximum)

{-@ LIQUID "--reflection" @-}

{-@ maximum :: {xs:[a] | len xs > 0 } -> a @-}
maximum :: Ord a => [a] -> a
maximum (x:[]) = x
maximum (x:xs) = let m = maximum xs in
  if x > m then x else m

-- How do we prove that the return value is >= than anything
-- in the list?  We don't have a "forall".  We could return
-- some other data type that encoded the guarantee, maybe, but
-- it seems best to write a proof.

{-@ member :: a -> [a] -> Bool @-}
member :: Eq a => a -> [a] -> Bool
member _ [] = False
member x (y:ys) = if x == y then True else member x ys

{-@ reflect member @-}
{-@ reflect maximum @-}

{-@ maximumIsGte :: {xs:[a] | len xs > 0} -> x:a ->
  { member x xs => maximum xs >= x } @-}
maximumIsGte :: Ord a => [a] -> a -> Proof
maximumIsGte (x:[]) y =
  if y == x then
    member y (x:[])
    === maximum (x:[]) >= y *** QED
  else
    member y (x:[])
    === member y [] *** QED
maximumIsGte (x:xs) y =
  if y == x then
    maximum (x:xs)
    =>= y *** QED
  else if member y xs then   
    -- have: member y xs => maximum xs >= y
    --  therefore           maximum xs >= y
    -- need: maximum (x:xs) >= y
    maximum (x:xs)
    =>= maximum xs ? maximumIsGte xs y
    =>= y *** QED
  else
    member y (x:xs)
    === member y xs *** QED
