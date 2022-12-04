module Example where

-- Failing version: {-@ type ValidRange = (x:Int,{y:Int | x <= y }) @-}
{-@ type ValidRange = (x::Int,{y:Int | x <= y }) @-}
type Range = (Int,Int)

{-@ buildRange :: Int -> Int -> Maybe ValidRange @-}
buildRange :: Int -> Int -> Maybe Range
buildRange a b | a <= b = Just (a,b)
               | otherwise = Nothing
               
