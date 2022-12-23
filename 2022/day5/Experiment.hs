module Experiment where

type Stack = [Int]

{-@ data VecOfStacks = VecS { numStacks :: Nat,
                              stacks :: {s:[Stack] | len s = numStacks} }         
  @-}
data VecOfStacks =
  VecS { numStacks :: Int,
         stacks :: [Stack] }

{-@ ith :: xs:[a] -> {i:Int | 0 <= i && i < len xs} -> a @-}
ith :: [a] -> Int -> a
ith (x:xs) i = if i == 0 then x else ith xs (i-1)
  
{-@ getStack :: v:VecOfStacks -> {i:Int | 0 <= i && i < numStacks v} -> Stack @-}
getStack :: VecOfStacks -> Int -> Stack
-- getStack (VecS _ s) i = s !! i
getStack (VecS _ s) i = ith s i

-- unbound GHC.Types::i

-- unbound GHC.Types::i
{-@ reflect ith @-}

-- needs ith
{-@ reflect getStack @-}

empty :: Stack -> Bool
empty [] = True
empty (_:_) = False
{-@ measure empty @-}

{-@ predicate NonEmptyAt V I = not empty (getStack V I) @-}

{-@ checkNonempty :: v:VecOfStacks -> {i:Int | 0 <= i && i < numStacks v} -> {b:Bool | b <=> NonEmptyAt v i } @-}
checkNonempty v i = length (getStack v i) > 0

{-@ pop :: {s:Stack | not empty s} -> Stack @-}
pop :: Stack -> Stack
pop (_:xs) = xs

{-@ top :: {s:Stack | not empty s} -> Int @-}
top :: Stack -> Int
top (x:_) = x

{-@ popStack :: v:VecOfStacks -> {i : Int | NonEmptyAt v i } -> (Stack,Int) @-}
popStack :: VecOfStacks -> Int -> (Stack,Int)
popStack v i = (pop (getStack v i), top (getStack v i)) where
