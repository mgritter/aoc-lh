module ExperimentRational where

import Data.Ratio

-- See https://github.com/ucsd-progsys/liquidhaskell/issues/1336
{-@ embed Ratio * as int @-}
safeDivision :: Ratio Int -> Ratio Int -> Either String (Ratio Int)
safeDivision a b = if b == 0 then Left "division by zero" else Right (a/b)

