module LHMap (
  -- Associative lists --
  AList,
    emptyA,
    sizeA,
    insertA,
    lookupA,
    keyPresent,
    removeKey,    
    toAList,

  -- Map functions, with properties defined in terms of toAList --
    Map,
    LHMap.null,
    empty,
    insert,
    singleton,
    LHMap.lookup,
    delete,
    size
  ) where
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"            @-}

import qualified Data.Map as DMap
import Language.Haskell.Liquid.ProofCombinators
import Control.Exception (assert)

type Map k v = DMap.Map k v

-- To represent the semantics of a map, we'll define an associative list, then
-- provide a measure that converts a Map to an associative list, and define
-- the semantics of Map operations in AList operations.

{-@ data AList k v = AEmpty |
                     ACons { akey :: k, avalue:: v, arest :: DoesNotInclude k v akey } @-}
{-@ type DoesNotInclude k v H = AList {v:k | v /= H} v @-}
data AList k v =
  AEmpty |
  ACons k v (AList k v)

{-@ emptyA :: AList k v -> Bool @-}
{-@ measure emptyA @-}
emptyA :: AList k v -> Bool
emptyA AEmpty = True
emptyA _ = False

{-@ sizeA :: AList k v -> {s:Int | s >= 0} @-}
{-@ measure sizeA @-}
sizeA :: AList k v -> Int
sizeA AEmpty = 0
sizeA (ACons _ _ rest) = 1 + sizeA rest

-- Check that the key is present.
{-@ keyPresent :: k -> AList k v -> Bool @-}
{-@ reflect keyPresent @-}
keyPresent :: Eq k => k -> AList k v -> Bool
keyPresent _ AEmpty  = False
keyPresent k1 (ACons k2 _ rest) | k1 == k2 = True
                                | otherwise = keyPresent k1 rest

-- Return the list with the type proving that the key is absent.
{-@ removeKey :: key:k -> AList k v -> DoesNotInclude k v key @-}
{-@ reflect removeKey @-}
removeKey :: Eq k => k -> AList k v -> AList k v
removeKey _ AEmpty  = AEmpty
removeKey k1 (ACons k2 v2 rest) | k1 == k2 = rest
                                | otherwise = ACons k2 v2 (removeKey k1 rest)

-- THEOREM: If we ACons key x onto a list, then keyPresent key is true
-- Unnecessary, insertA can be defined without it.
keyPresentLemma :: k -> v -> AList k v -> Bool
{-@ keyPresentLemma :: key:k -> val:v -> l:AList k v -> { keyPresent key (ACons key val l) } @-}
keyPresentLemma _ _ _  = True

{-@ reflect mention @-}
mention :: a -> b -> b
mention _ x = x

-- Add a key/value pair to the assocative list
{-@ insertA :: key:k -> val:v -> AList k v -> {a:AList k v | keyPresent key a} @-}
{-@ reflect insertA @-}
insertA :: Eq k => k -> v -> AList k v -> AList k v
insertA key val aList =
  let x = ACons key val (removeKey key aList) in
    -- Mentioning keyPresent unrolls it once, which is all we need to prove the correct type.
    mention (keyPresent key x) x

{-@ test1 :: {a:AList Int String | keyPresent 1 a} @-}
test1 :: AList Int String
test1 = insertA 1 "one" AEmpty

{-@ lookupA :: key:k -> l:AList k v -> {m:Maybe v | isJust m <=> keyPresent key l} @-}
{-@ reflect lookupA @-}
lookupA :: Eq k => k -> AList k v -> Maybe v
lookupA _ AEmpty = Nothing
lookupA key (ACons k2 val rest) = if key == k2 then Just val else lookupA key rest

-- Size is constant or decreases by one under removeKey
{-@ removeSizeLemma :: pre:AList k v -> key:k ->
 { sizeA (removeKey key pre) == sizeA pre ||
   sizeA (removeKey key pre) == sizeA pre - 1 } @-}
removeSizeLemma :: Eq k => AList k v -> k -> Proof
removeSizeLemma AEmpty key = removeKey key AEmpty === AEmpty *** QED
removeSizeLemma (ACons key _ rest) k2 =
  if key == k2 then ()
  else removeSizeLemma rest k2

-- Is size nondecreasing under insertion?
{-@ sizeNondecreasingLemma :: pre:AList k v -> key:k -> val:v ->
 { sizeA (insertA key val pre) == sizeA pre ||
   sizeA (insertA key val pre) == 1 + sizeA pre } @-}
sizeNondecreasingLemma :: Eq k => AList k v -> k -> v -> Proof
sizeNondecreasingLemma l key _ = removeSizeLemma l key

--------------------------------------------------
-- Map function specifications in terms of AList
--------------------------------------------------

-- TODO: these assumptions use equality, when if we actually implements toAList
-- the property would be weaker: equivalence up to order.  It might be that this
-- permits us to reason that two lists are equal when they are not.

-- UNIMPLEMENTED measure to convert from a map to an AList.  We don't want to
-- actually do this, we just want to define properties "as if" we had done it.
-- See https://github.com/ucsd-progsys/liquidhaskell/issues/1892#issuecomment-969032284
-- That example uses "unreflected", I don't think that keyword exists?  So I substituted
-- in the empty list.
{-@ measure  toAList :: Map k v -> AList k v @-}
{-@ assume toAList :: m:Map k v -> {l:AList k v | l = toAList m } @-}
toAList :: Map k v -> AList k v
toAList _ = AEmpty

{-@ assume null :: m:Map k v -> {b:Bool | b <=> emptyA (toAList m) } @-}
null :: Map k v -> Bool
null = DMap.null

{-@ assume empty :: {m:Map k v | toAList m = AEmpty } @-}
empty :: Map k v
empty = DMap.empty

{-@ assume singleton :: key:k -> value:v -> {m:Map k v | (toAList m) = ACons key value AEmpty} @-}
singleton :: k -> v -> Map k v
singleton = DMap.singleton

-- Potentially unsound 
{-@ assume insert :: key:k -> value:v -> pre:Map k v
  -> {post:Map k v | toAList post = insertA key value (toAList pre) }  @-}
insert :: Ord k => k -> v -> Map k v -> Map k v
insert = DMap.insert 

{-@ test2 :: {m:Map Int String |
   not emptyA (toAList m) &&
   keyPresent 1 (toAList m) &&
   not keyPresent 2 (toAList m) } @-}
test2 :: Map Int String
test2 = insert 1 "one" empty

{-@ assume lookup :: key:k -> m:Map k v
   -> {r:Maybe v | r = lookupA key (toAList m)} @-}
lookup :: Ord k => k -> Map k v -> Maybe v
lookup = DMap.lookup

{-@ test3 :: {m:Maybe String | m = Just "one"} @-}
test3 :: Maybe String
test3 = let key = 1 :: Int in LHMap.lookup key (insert key "one" empty)

{-@ test4 :: {m:Maybe String | m = Just "one"} @-}
test4 :: Maybe String
test4 = let key = 1 :: Int in LHMap.lookup key (insert 2 "two" (singleton 1 "one"))

-- Potentially unsound -- list could have been reordered
{-@ assume delete :: key:k -> pre:Map k v ->
  {post:Map k v | toAList post = removeKey key (toAList pre) &&
                  not keyPresent key (toAList post) } @-}
delete :: Ord k => k -> Map k v -> Map k v
delete = DMap.delete

{-@ assume size :: m:Map k v ->
  {n:Int | n = sizeA (toAList m)} @-}
size :: Map k v -> Int
size = DMap.size

{-@ test5 :: {sz:Int | sz = 1} @-}
test5 :: Int
test5 =  let x = singleton 1 "one" in size x
  ? sizeA (ACons 1 "one" AEmpty) === 1

{-@ test6 :: {sz:Int | sz = 2} @-}
test6 :: Int
test6 =  let x = insert 2 "two" (singleton 1 "one") in size x
  ? 2
    === 1 + sizeA (ACons 1 "one" AEmpty)
    === sizeA (ACons 2 "two" (ACons 1 "one" AEmpty))
    === sizeA (ACons 2 "two" (removeKey 2 (ACons 1 "one" AEmpty)))
