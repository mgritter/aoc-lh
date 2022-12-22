module Parse (Direction(TurnLeft,TurnRight,Move), parseDirections) where

import Text.ParserCombinators.Parsec
import Control.Monad

data Direction =
  TurnLeft |
  TurnRight |
  Move Int
  
parseUnsignedNumber :: Parser Direction
parseUnsignedNumber = liftM (Move . read) $ many1 digit

parseLeft :: Parser Direction
parseLeft = char 'L' >> return TurnLeft

parseRight :: Parser Direction
parseRight = char 'R' >> return TurnRight

parseDir :: Parser Direction
parseDir = parseLeft <|> parseRight <|> parseUnsignedNumber

parseDirs :: Parser [Direction]
parseDirs = many1 parseDir

parseDirections :: String -> Either String [Direction]
parseDirections s = case (parse parseDirs "directions" s) of
  Right t -> Right t
  Left err -> Left $ "Couldn't parse line: " ++ (show err)

