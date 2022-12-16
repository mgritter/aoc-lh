module Parse (parseLine,
             ) where

import Text.ParserCombinators.Parsec
import Control.Monad

parseUnsignedNumber :: Parser Int
parseUnsignedNumber = (liftM read) $ many1 digit

parseValve :: Parser String
parseValve = do
  x <- upper
  y <- upper
  return $ [x,y]

parseListOfValves :: Parser [String]
parseListOfValves = sepBy parseValve (string ", ")

parseValveDesc :: Parser (String, Int, [String])
parseValveDesc = do
  _ <- string "Valve "
  n <- parseValve
  _ <- string " has flow rate="
  flow <- parseUnsignedNumber
  _ <- char ';'
  _ <- string " tunnel"
  _ <- optional (char 's')
  _ <- string " lead"
  _ <- optional (char 's')
  _ <- string " to valve"
  _ <- optional (char 's')
  _ <- string " "
  nn <- parseListOfValves
  return $ (n,flow,nn)

parseLine :: String -> Either String (String, Int, [String])
parseLine s = case (parse parseValveDesc "line" s) of
  Right t -> Right t
  Left err -> Left $ "Couldn't parse line: " ++ (show err)
  
