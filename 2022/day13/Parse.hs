module Parse (parsePacket,
              Packet(Number, PList),
              parse) where
{-@ LIQUID "--no-termination" @-}

import Text.ParserCombinators.Parsec
import Control.Monad
import Data.List

{-@ 
data Packet =
  Number { number::Int } |
  PList { subPackets :: [Packet] }
@-}
data Packet =
  Number Int |
  PList [Packet]

{-
measure packetHeight :: Packet -> Int
packetHeight (Number _) = 0
packetHeight (PList 
-}

showPacket :: Packet -> String
showPacket (Number x) = show x
showPacket (PList []) = "[]"
showPacket (PList xs) = "[" ++ (foldl1 (++) (intersperse "," (map showPacket xs))) ++ "]"

instance Show Packet where show = showPacket

parsePacket :: Parser Packet
parsePacket = parseNumber <|> parseList

parseNumber :: Parser Packet
parseNumber = (liftM (Number . read) $ many1 digit)

parseList :: Parser Packet
parseList = do
  _ <- char '['
  x <- sepBy parsePacket (char ',')
  _ <- char ']'
  return $ PList x

