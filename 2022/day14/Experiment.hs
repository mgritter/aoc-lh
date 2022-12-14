module Experiment where
{-@ LIQUID "--exact-data-cons" @-}

{-@ data Coord = Point { yCoord :: Int, xCoord :: Int } @-}
data Coord = Point { yCoord :: Int, xCoord :: Int }
  deriving (Eq,Ord)

{-@
data StraightLine =
  HLine { startH::Coord, endH::{c:Coord | yCoord c = yCoord startH } } |
  VLine { startV::Coord, endV::{c:Coord | xCoord c = xCoord startV } }
@-}
data StraightLine =
  HLine { startH::Coord, endH::Coord  } |
  VLine { startV::Coord, endV::Coord  }

-- BAD: {-@ measure isVerticalLine :: StraightLine -> Bool @-}
-- GOOD: {-@ measure isVerticalLine @-}
-- ALSO FINE:
{-@ inline isVerticalLine @-}
isVerticalLine :: StraightLine -> Bool
isVerticalLine (VLine _ _) = True
isVerticalLine _ = False

{-@ test4 :: {s:StraightLine | isVerticalLine s} @-}
test4 :: StraightLine
test4 = VLine (Point 0 0) (Point 10 0)

