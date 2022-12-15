module Packet(
  Packet(Number, PList),
  listToPList,
  packetHeight
  ) where
 
import Data.List

{-@ 
data Packet =
  Number { number::Int } |
  PList { height :: {n:Nat | n > 0}, subPackets :: [ShorterThan height] }
@-}
data Packet =
  Number { number :: Int } |
  PList { height :: Int, subPackets:: [Packet] }

{-@ type ShorterThan H = {p:Packet | Packet.packetHeight p < H } @-}

{-@ measure isList @-}
isList :: Packet -> Bool
isList (Number _) = False
isList (PList _ _) = True

{-@ measure packetHeight @-}
-- Without this line, the termination check fails.
-- With this line we need to specify Packet.packetHeight in the ShorterThan deifnition!
{-@ packetHeight :: Packet -> Nat @-}
packetHeight :: Packet -> Int
packetHeight (Number _) = 0
packetHeight (PList h _) = h

{-@ listToPList :: [Packet] -> {p:Packet | isList p} @-}
listToPList :: [Packet] -> Packet
listToPList [] = PList 1 []
listToPList (p:ps) =
  let rest = listToPList ps
      php = 1 + packetHeight p in
    if php > height rest then
      PList php (p:(subPackets rest))
    else
      PList (height rest) (p:(subPackets rest))
  
{-
Desired form of the above:
listToPList :: [Packet] -> Packet
listToPList ps = let m = maximum (map packetHeight ps) in
  PList (m+1) ps
-}

{-@ showPacket :: p:Packet -> String / [packetHeight p] @-}
showPacket :: Packet -> String
showPacket (Number x) = show x
showPacket (PList _ []) = "[]"
showPacket (PList _ xs) = "[" ++ (foldl1 (++) (intersperse "," (map showPacket xs))) ++ "]"

instance Show Packet where show = showPacket

