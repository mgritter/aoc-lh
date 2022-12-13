module LengthLemmas (filter, length, notP, lemmaFilterLength) where
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

import Prelude hiding (length, filter)
import Language.Haskell.Liquid.ProofCombinators

{-@ reflect filter @-}
filter :: (a -> Bool) -> [a] -> [a]
filter _ [] = []
filter p (x:xs) = if p x then x:(filter p xs) else (filter p xs)

{-@ reflect length @-}
length :: [a] -> Int
length [] = 0
length (_:xs) = 1 + length xs

{-@ notP :: (a->Bool) -> a -> Bool @-}
{-@ reflect notP @-}
notP :: (a->Bool) -> a -> Bool
notP p x = if p x then False else True

{-@
lemmaFilterLength
  :: p:(a->Bool)
  -> l:[a] ->
  { length (filter p l) + length (filter (notP p) l) = length l }
@-}
lemmaFilterLength :: (a->Bool) -> [a] -> Proof
lemmaFilterLength _ [] = ()
lemmaFilterLength p (x:xs) =
    if p x then
      lemmaFilterLength p xs
    else
      lemmaFilterLength p xs
