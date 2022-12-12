module LengthLemmas where
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--ple" @-}

import Prelude hiding (length, filter, not)
import Language.Haskell.Liquid.ProofCombinators

{-@ filter :: (a->Bool) -> [a] -> [a] @-}
{-@ reflect filter @-}
filter :: (a -> Bool) -> [a] -> [a]
filter _ [] = []
filter p (x:xs) = if p x then x:(filter p xs) else (filter p xs)

length :: [a] -> Int
length [] = 0
length (x:xs) = 1 + length xs
{-@ reflect length @-}

{-@ myNot :: Bool -> Bool @-}
{-@ reflect myNot @-}
myNot :: Bool -> Bool
myNot True = False
myNot False = True

{-@ reflect comp @-}
comp :: (b->c) -> (a->b) -> a -> c
comp f g x = f (g x) 

{-@ lemmaCompNot :: p:(a->Bool) -> {l:[a] | len l > 0 && not (p (head l)) } ->
    { (( comp myNot p ) (head l)) = True} @-}
lemmaCompNot :: (a->Bool) -> [a] -> Proof
lemmaCompNot p (x:xs) = 
  ( comp myNot p ) x
  === myNot (p x)
  *** QED

{-@ lemmaCompNot2 :: p:(a->Bool) -> {l:[a] | len l > 0 && not (p (head l)) } ->
    { (( myNot . p ) (head l)) = True} @-}
lemmaCompNot2 :: (a->Bool) -> [a] -> Proof
lemmaCompNot2 p (x:xs) = 
  ( myNot . p ) x
  === myNot (p x)
  *** QED

{-
{-@ lemmaCompNot3 :: p:(a->Bool) -> {x:a | p x = False} ->
    { (myNot . p ) x = True } @-}
--    ((myNot . p ) x) = True }              doesn't work
--    { q:Proof | ((myNot . p ) x) = True }  doesn't work either
lemmaCompNot3 :: (a->Bool) -> a -> Proof
lemmaCompNot3 p x = 
  ( myNot . p ) x
  === myNot (p x)
  *** QED
-}

{-
cons :: a -> [a] -> [a]
cons x xs = x : xs
{-@ reflect cons @-}

{-@ lemmaFilterNot :: p:(a->Bool) -> {l:[a] | len l > 0 && not (p (head l)) } ->
  { filter (comp myNot p) l = cons (head l) (filter (comp myNot p) (tail l)) } @-}
lemmaFilterNot :: (a->Bool) -> [a] -> Proof
lemmaFilterNot p (x:xs) =
  filter (comp myNot p) (x:xs) ? lemmaCompNot p (x:xs)
  === x:(filter (comp myNot p) xs)
  *** QED
-}

-- Here's what I originally wanted:
-- {-@ lemmaFilterLength :: p:(a->Bool) -> l:[a] ->
--   { length (filter p l) + length (filter (not . p) l) = length l } @-}
{-@ lemmaFilterLength :: p:(a->Bool) -> l:[a] ->
  { length (filter p l) + length (filter (comp myNot p) l) = length l } @-}
lemmaFilterLength :: (a->Bool) -> [a] -> Proof
lemmaFilterLength p [] = length [] === 0 === length (filter p []) === length (filter (comp myNot p) []) *** QED
lemmaFilterLength p (x:xs) =
      (if p x then
          length (filter p (x:xs))
          === length (x:(filter p xs))
        else
          length (filter (comp myNot p) (x:xs)) ? lemmaCompNot p (x:xs)
          === length (x:(filter (comp myNot p) xs))
      ) ?
      lemmaFilterLength p xs
      *** QED

{-@ lemmaFilterLength2 :: p:(a->Bool) -> l:[a] ->
  { length (filter p l) + length (filter (myNot . p) l) = length l } @-}
lemmaFilterLength2 :: (a->Bool) -> [a] -> Proof
lemmaFilterLength2 p [] = length [] === 0 === length (filter p []) === length (filter (myNot . p) []) *** QED
lemmaFilterLength2 p (x:xs) =
      (if p x then
          length (filter p (x:xs))
          === length (x:(filter p xs))
        else
          length (filter (myNot . p) (x:xs)) ? lemmaCompNot2 p (x:xs)
          === length (x:(filter (myNot . p) xs))
      ) ?
      lemmaFilterLength2 p xs
      *** QED

