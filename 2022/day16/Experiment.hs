module Experiment where

{-@ double :: x:a -> {ys:[{y:a | y = x}] | len ys = 2} @-}
double :: a -> [a]
double x = [ x, x ]

{-@ fail doubleEach @-}
{-@ doubleEach :: xs:[Int] -> {ys:[Int] | len ys = 2 * len xs} @-}
doubleEach :: [Int] -> [Int]
doubleEach xs = xs >>= double

{-@ doubleEach2 :: [{x:Int | x= 2}] -> [{y:Int | y = 2}] @-}
doubleEach2 :: [Int] -> [Int]
doubleEach2 xs = xs >>= double


