module Main (main) where
{-@ LIQUID "--max-case-expand=6" @-}
{-@ LIQUID "--no-termination" @-}

import LoadLines
import Data.List.Split
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set

data Shell =
  Cd String |
  Ls |
  FileSize Int String |
  Subdir String

parseShell :: String -> Maybe Shell
parseShell line = case (splitOneOf " " line) of
  ("$":"cd":x:[]) -> Just $ Cd x
  ("$":"ls":[]) -> Just $ Ls
  ("dir":x:[]) -> Just $ Subdir x
  (sz:file:[]) -> Just $ FileSize (read sz) file
  _ -> Nothing

{-@ data FsObj =
    File { fileName :: String, size :: Int } |
    Directory { dirName :: String, contents :: Map.Map String FsObj } @-}    
data FsObj =
  File { fileName :: String, size :: Int } |
  Directory { dirName :: String, contents :: Map.Map String FsObj }

type DirPath = [String]

{-@ measure isDirectory @-}
isDirectory :: FsObj -> Bool
isDirectory (Directory _ _) = True
isDirectory _ = False

{-@ type Dir = {d:FsObj | isDirectory d} @-}

{-@ insertFile :: f:Dir -> {p:DirPath | len p >= 1} -> FsObj -> {f2:FsObj | isDirectory f2 && dirName f2 = dirName f } @-}
insertFile :: FsObj -> DirPath -> FsObj -> FsObj
insertFile (Directory name contents) (p:[]) obj =
  (Directory name (Map.insert p obj contents))
insertFile (Directory name contents) (p:ps) obj =
  let subdir = Map.lookup p contents
  in case subdir of
    Just (Directory n' c') ->
       (Directory name
         (Map.insert p (insertFile (Directory n' c') ps obj) contents))
    Just (File _ _) ->
       (Directory name
         (Map.insert p (insertFile (Directory p Map.empty) ps obj) contents))
    Nothing ->
       (Directory name
         (Map.insert p (insertFile (Directory p Map.empty) ps obj) contents))


{-@ data ShellState = State { cwd :: [String], root :: Dir } @-}
data ShellState = State { cwd :: [String], root :: FsObj }

dirUp :: [String] -> [String]
dirUp path = (take (length path - 1) path)
                  
{-@ parseLine :: ShellState -> Shell -> ShellState @-}
parseLine :: ShellState -> Shell -> ShellState
parseLine (State cwd root) (Cd "/") = State [] root 
parseLine (State cwd root) (Cd "..") = State (dirUp cwd) root
parseLine (State cwd root) (Cd name) = State (cwd ++ [name]) root
parseLine (State cwd root) Ls = State cwd root
parseLine (State cwd root) (FileSize sz name) =
  State cwd (insertFile root (cwd ++ [name]) (File name sz))
parseLine (State cwd root) (Subdir name) =
  State cwd (insertFile root (cwd ++ [name]) (Directory name Map.empty))

{-@ indent :: Nat -> String @-}
indent :: Int -> String
indent n = replicate n ' '

{-@ showDir :: Nat -> f:FsObj -> String @-}
showDir :: Int -> FsObj -> String
showDir ind (File n sz) = (indent ind) ++ n ++ " " ++ (show sz)
showDir ind (Directory n contents) = (indent ind) ++ n ++ "\n" ++
                                     (unlines (map (showDir (ind + 2))
                                                   (Map.elems contents)))

-- computeSizes returns the size of the files underneath the directory, and a list of subdirectory
-- sizes (including ourself!)
computeSizes :: FsObj -> (Int, [Int])
computeSizes (File _ sz) = (sz, [])
computeSizes (Directory _ contents) =
  let subdirs = (map computeSizes (Map.elems contents)) in
    let total = (sum (map fst subdirs))
        in (total, (concat (map snd subdirs)) ++ [total])

part1 :: [String] -> IO ()
part1 input = do
  putStrLn "Part 1"
  let cmds = mapMaybe parseShell input in
    let final = foldl parseLine (State [] (Directory "/" Map.empty)) cmds in
      let (_, dirSizes) = computeSizes (root final) in
        let total = sum (filter (\s -> s <= 100000) dirSizes) in
          print total
{-
      putStr $ showDir 0 (root final)
-}

diskSize = 70000000
needed = 30000000
{-@ inline diskSize @-}
{-@ inline needed @-}

{-@ type QualifiedSize Used = {s:Int | diskSize - Used + s >= needed } @-}

{-@ filterQualified :: used:Int -> sizes:[Int] ->
  [{q:QualifiedSize used | Set_mem q (listElts sizes)}] @-}
filterQualified :: Int -> [Int] -> [Int]
filterQualified used [] = []
filterQualified used (s:ss) =
  if diskSize - used + s >= needed then s:(filterQualified used ss)
  else (filterQualified used ss)

{-@ minQualified :: used:Int
  -> original:[Int]
  -> {qs:[{q:QualifiedSize used | Set_mem q (listElts original)}] | len qs > 0}
  -> {s:(QualifiedSize used) | Set_mem s (listElts original) } @-}
minQualified :: Int -> [Int] -> [Int] -> Int
minQualified _ _ (s:[]) = s
minQualified used orig (s:ss) = let m = minQualified used orig ss in
                          if m < s then m else s                          

{-@ dirToDelete :: used:Int -> dirSizes:[Int] ->
   Maybe {s:(QualifiedSize used) | Set_mem s (listElts dirSizes) } @-} 
dirToDelete :: Int -> [Int] -> Maybe Int
{-
-- Original version, type-checks fine
dirToDelete used [] = Nothing
dirToDelete used (x:xs) =
  if diskSize - used + x >= needed then
    let minInRest = dirToDelete used xs
    in case minInRest of
      Nothing -> Just x
      Just y -> if y < x then Just y else Just x
  else
    dirToDelete used xs
-}

-- Only type-checks after rewriting *two* standard functions
-- Can we somehow tell LH that (listElts qualified) is a subset of (listElts used) in
-- a more natural way?
dirToDelete used xs =
  let qualified = filterQualified used xs in
    if length qualified == 0 then Nothing else
      let foo = minQualified used xs qualified
          in Just foo

part2 :: [String] -> IO ()
part2 input = do
  putStrLn "Part 2"
  let cmds = mapMaybe parseShell input in
    let final = foldl parseLine (State [] (Directory "/" Map.empty)) cmds in
      let (tot, dirSizes) = computeSizes (root final) in
        case dirToDelete tot dirSizes of
          Nothing -> putStrLn "No directory large enough!"
          Just x -> print x
          
main :: IO ()
main = runOnLines part1 part2
