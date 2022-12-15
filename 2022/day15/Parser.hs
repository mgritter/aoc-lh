module Parser (parseLine) where

import Text.ParserCombinators.Parsec
import Control.Monad

parseUnsignedNumber :: Parser Int
parseUnsignedNumber = (liftM read) $ many1 digit

parseNumber :: Parser Int
parseNumber =
  (char '-' >> (liftM ((-) 0) parseUnsignedNumber))
  <|>
  parseUnsignedNumber
  
parseSensor :: Parser (Int,Int,Int,Int)
parseSensor = do
  _ <- string "Sensor at x="
  x1 <- parseNumber
  _ <- string ", y="
  y1 <- parseNumber
  _ <- string ": closest beacon is at x="
  x2 <- parseNumber
  _ <- string ", y="
  y2 <- parseNumber
  return (x1,y1,x2,y2)
  
parseLine :: String -> Either String (Int,Int,Int,Int)
parseLine s = case (parse parseSensor "line" s) of
  Right x -> Right x
  Left err -> Left $ "Couldn't parse line: " ++ (show err)
