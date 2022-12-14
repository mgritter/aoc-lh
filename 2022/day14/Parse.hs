module Parse (parseLine) where

import Text.ParserCombinators.Parsec
import Control.Monad

parseNumber :: Parser Int
parseNumber = (liftM read) $ many1 digit

parseCoord :: Parser (Int,Int)
parseCoord = do
  x <- parseNumber
  _ <- char ','
  y <- parseNumber
  return $ (y,x)
  
parseList :: Parser [(Int,Int)]
parseList = sepBy parseCoord (string " -> ")

parseLine :: String -> Either String [(Int,Int)] 
parseLine s = case (parse parseList "line" s) of
  Right x -> Right x
  _ -> Left "Couldn't parse line"
  
