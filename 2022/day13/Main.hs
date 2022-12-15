module Main (main) where
{-@ LIQUID "--max-case-expand=10" @-}

import LoadLines
import Parse
import Packet
import Data.Either
import Data.Ord
import Data.Sort
import Data.List

{-@
data PacketPair =
  PP { index :: Int, first :: Packet, second :: Packet }
@-}
data PacketPair =
  PP { index :: Int, first :: Packet, second :: Packet }

{-@ takeWhileNonempty  :: xs:[String] -> ys:[{s:String | len s > 0}] @-}
takeWhileNonempty :: [String] -> [String]
takeWhileNonempty [] = []
takeWhileNonempty (x:xs) = if length x > 0 then x:(takeWhileNonempty xs) else []

-- Partition the intial list into sublists that were separated by an empty string
{-@ splitByEmpty :: xs:[String] -> [[{s:String | len s > 0}]] @-}
splitByEmpty :: [String] -> [[String]]
splitByEmpty [] = []
splitByEmpty xs =
  let first = takeWhileNonempty xs
      rest = (drop (length first + 1) xs) in
    first : (splitByEmpty rest)

parseOnePair :: Int -> [String] -> Either String PacketPair
parseOnePair i (x:y:[]) =
  case (parse parsePacket "first" x, parse parsePacket "second" y) of
    (Right xl, Right yl) -> Right $ PP i xl yl
    _ -> Left "packets did not parse"
parseOnePair _ _ = Left "Didn't find a pair"

parsePairs :: [String] -> Either String [PacketPair]
parsePairs ls = if length errors > 0 then Left (head errors)
  else Right goodVals where
  textPairs = splitByEmpty ls
  results = map (uncurry parseOnePair) (zip [1..] textPairs)
  errors = lefts results
  goodVals = rights results

--  Number 0
--
--  PList 1 []
--  PList 1 [x]
--  Plist 1 [x,y]

--  PList 2

{-@ measure safeListLength :: Packet -> Nat 
safeListLength (Number _) = 1
safeListLength (PList _ xs) = len xs
@-}

{-@ measure bareNats :: Packet -> Nat 
bareNats (Number _) = 1
bareNats (PList _ xs) = 0
@-}

{-@ max :: Nat -> Nat -> Nat @-}
max :: Int -> Int -> Int
max a b = if a > b then a else b
{-@ inline max @-}

-- Are the left and right packets in correct order?
{-@ correctOrder :: a:Packet -> b:Packet -> Ordering /
   [ max (packetHeight a) (packetHeight b), max (bareNats a) (bareNats b), max (safeListLength a) (safeListLength b) ]  @-}
correctOrder :: Packet -> Packet -> Ordering
correctOrder (Number x) (Number y) = compare x y
correctOrder (Number x) b@(PList _ y) = correctOrder (PList 1 [(Number x)]) b
correctOrder a@(PList _ x) (Number y) = correctOrder a (PList 1 [(Number y)])
correctOrder (PList _ []) (PList _ []) = EQ
correctOrder (PList _ (_:_)) (PList _ []) = GT 
correctOrder (PList _ []) (PList _ (_:_)) = LT
correctOrder (PList xh (x:xs)) (PList yh (y:ys)) =
  case correctOrder x y of
    EQ -> correctOrder (PList xh xs) (PList yh ys)
    GT -> GT
    LT -> LT

hasCorrectOrder :: PacketPair -> Bool
hasCorrectOrder pp = correctOrder (first pp) (second pp) == LT

part1 :: [String] -> IO ()
part1 input = do
  putStrLn "Part 1"
  case parsePairs input of
    Left error -> putStrLn $ "Error: " ++ error
    Right pps ->
      let valid = filter hasCorrectOrder pps in do
        print $ (map index valid)
        print $ sum (map index valid)
        
-- [[2]]
marker2 = PList 2 [PList 1 [Number 2]]
-- [[6]]
marker6 = PList 2 [PList 1 [Number 6]]

parseList :: [String] -> [Packet]
parseList ls = rights (map (parse parsePacket "input") ls)

isMarker :: Packet -> Bool
isMarker (PList 2 [(PList 1 [Number 2])]) = True
isMarker (PList 2 [(PList 1 [Number 6])]) = True
isMarker _ = False

part2 :: [String] -> IO ()
part2 input = do
  putStrLn "Part 2"
  let allPackets = parseList input
      augmented = allPackets ++ [marker2, marker6]
      sorted = sortBy correctOrder augmented
      indexes = findIndices isMarker sorted in do
    putStrLn $ (unlines (map show sorted))
    print $ indexes
    if length indexes == 2 then
      print $ ((indexes !! 0) + 1) * ((indexes !! 1) + 1)
    else
      putStrLn "oops"
        
main :: IO ()
main = runOnLines part1 part2

