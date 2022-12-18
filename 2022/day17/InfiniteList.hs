module InfiniteList(cycle, head, tail) where

import Prelude hiding (cycle, head, tail)
import qualified Data.List

{-@ measure infiniteList :: [a] -> Bool @-}

-- If we don't have the spec for cycle then it fails because len xs is not greater than 0.
-- With both specs we get a warning.
-- {-@ cycle :: {x:[a] | len x > 0} -> [a] @-}
{-@ ignore cycle @-}
{-@ assume cycle :: {x:[a] | len x > 0} -> {y:[a] | infiniteList y } @-}
cycle :: [a] -> [a]
cycle xs = Data.List.cycle xs

{-@ ignore head @-}
{-@ head :: {xs:[a] | len xs > 0 || infiniteList xs} -> a @-}
head :: [a] -> a
head xs = Data.List.head xs

{-@ ignore tail @-}
{-@ tail :: {xs:[a] | len xs > 0 || infiniteList xs} ->
   {ys:[a] | if (infiniteList xs) then (infiniteList ys)else len ys = len xs - 1 } @-}
tail :: [a] -> [a]
tail xs = Data.List.tail xs
