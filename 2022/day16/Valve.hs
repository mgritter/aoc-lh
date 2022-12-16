module Valve (
  Valve(name,flow_rate,neighbors,V),
  parseV
  ) where

import Parse

{-@
data Valve =
  V { name :: String, flow_rate :: Nat, neighbors :: [String] }
@-}
data Valve =
  V { name :: String, flow_rate :: Int, neighbors :: [String] }

parseV :: String -> Either String Valve
parseV s = case (parseLine s) of
  Right (n,flow,nn) -> if flow >= 0 then
                         Right $ V n flow nn
                       else
                         Left "Negative flow"
  Left err -> Left err
