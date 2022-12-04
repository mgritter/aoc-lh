module Example3 where

type Range = (Int,Int)

{-@ measure start @-}
start :: Range -> Int
start (a,b) = a

{-@ measure end @-}
end :: Range -> Int
end (a,b) = b

{-@ using (Range) as  {r:Range | start r <= end r} @-}

-- seemed to work earlier, now fails
-- {-@ intsToRanges :: Int -> Int -> Int -> Int -> Maybe (Range,Range) @-}
-- intsToRanges :: Int -> Int -> Int -> Int -> Maybe (Range,Range)
-- intsToRanges a b c d = if a <= b && c <= d then Just ((a,b),(c,d)) else Nothing

-- fails
-- {-@ list4ToRanges :: {r:[Int] | len r = 4 } -> Maybe (Range,Range) @-}
-- list4ToRanges :: [Int]-> Maybe (Range,Range)
-- list4ToRanges (a:b:c:d:[]) = if a <= b && c <= d then Just ((a,b),(c,d)) else Nothing
