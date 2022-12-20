module Experiment where

{-@ needsPositive :: {x:Int| x >= 0} -> String  @-}
needsPositive :: Int -> String
needsPositive 0 = ""
needsPositive x = 'a':(needsPositive (x - 1))

{-@ sus :: Int -> {y:Int | y > 0} -> String @-}
sus x y = needsPositive (x `mod` y)
