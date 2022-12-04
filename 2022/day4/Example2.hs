module Example2 where

type Range = (Int,Int)

-- Fails if {-@ inline contains @-}
contains :: Range -> Range -> Bool
contains (a,b) (c,d) = a <= c && b <= d

