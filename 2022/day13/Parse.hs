module Parse (parsePacket,
              Packet(Number, PList),
              parse) where
{-@ LIQUID "--no-termination" @-}

import Text.ParserCombinators.Parsec
import Control.Monad
import Packet

parsePacket :: Parser Packet
parsePacket = parseNumber <|> parseList

parseNumber :: Parser Packet
parseNumber = (liftM (Number . read) $ many1 digit)

parseList :: Parser Packet
parseList = do
  _ <- char '['
  x <- sepBy parsePacket (char ',')
  _ <- char ']'
  return $ listToPList x

