module Waltz where

import Data.IORef
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Safe
import System.IO.Unsafe

{-# NOINLINE idRef #-} 
idRef :: IORef Int
idRef = unsafePerformIO $ newIORef 0

{-# NOINLINE withRef #-} 
withRef :: (Int -> b) -> b
withRef f = f $ unsafePerformIO $ do
  id <- readIORef idRef
  writeIORef idRef (id + 1)
  return id


data Change = ListChange ListChange
  deriving (Show)

data ListChange = AddElement Data
                | RemoveElement Data
  deriving (Show)

data Data = ListData [Data]
          | SetData (Set.Set Data)
          | MapData (Map.Map Data Data)
          | StructData (Map.Map Text Data)
          | IntegerData Integer
          | StringData Text
  deriving (Eq, Ord, Show)

class Datable a where
  toData :: a -> Data
  fromData :: Data -> a

instance Datable a => Datable [a] where
  toData as = ListData $ map toData as
  fromData (ListData ds) = map fromData ds

instance (Datable a, Ord a) => Datable (Set.Set a) where
  toData as = SetData $ Set.map toData as
  fromData (SetData ds) = Set.map fromData ds

instance Datable Integer where
  toData i = IntegerData i
  fromData (IntegerData i) = i

instance Datable Text where
  toData s = StringData s
  fromData (StringData s) = s

data WatchableThing = forall a. (Watchable a) => WatchableThing a
                    | forall a. (ContainerWatchable a, Watchable a) => ContainerThing a

data PathElement = StructPath Text | MapPath Data
  deriving Show

data DepGraphAction = DepGraphChange Int (Change -> [Change])
                    | DepGraphStructWalk Text
                    | DepGraphMapWalk Int (Change -> Data)
type DepGraph = [(Int, DepGraphAction)]

fullCompile :: Watchable a => a -> Map.Map Int [DepGraphAction]
fullCompile w = foldr add Map.empty $ compile w 
  where add (n, action) m = Map.alter (set action) n m
        set a Nothing = Just [a]
        set a (Just as) = Just $ a:as

class Watchable a where
  initialValue :: a -> Data
  compile :: a -> DepGraph
  getWatchableId :: a -> Int

class (Watchable a) => ContainerWatchable a where
  initialValueAtPath :: [PathElement] -> a -> Data

data Struct = Struct Int [(Text, WatchableThing)]

structLookup text (Struct _ elems) = fromJustNote ("no struct element " ++ show text) $
                                     lookup text elems

instance Watchable Struct where
  initialValue (Struct _ elems) = StructData $ foldr addElem Map.empty elems
    where addElem (key, WatchableThing v) map = Map.insert key (initialValue v) map
          addElem (key, ContainerThing v) map = Map.insert key (initialValue v) map
  getWatchableId (Struct id _) = id
  compile (Struct _ structElems) = concatMap compileElem structElems
    where compileElem (name, WatchableThing v) = (getWatchableId v, DepGraphStructWalk name):
                                                  (compile v)
          compileElem (name, ContainerThing v) = (getWatchableId v, DepGraphStructWalk name):
                                                  (compile v)
instance ContainerWatchable Struct where
  initialValueAtPath ((StructPath t):[]) struct
    = case structLookup t struct of
        (ContainerThing c) -> initialValue c
        (WatchableThing t) -> initialValue t
  initialValueAtPath ((StructPath t):path) struct
    = case structLookup t struct of
        (ContainerThing c) -> initialValueAtPath path c
        eek -> error $ "can't get initialValueAtPath " ++ show path
  initialValueAtPath [] struct
    = initialValue struct

data List a = forall b. Datable b => MapList Int (b -> a) (List b) 
            | FilterList Int (a -> Bool) (List a) 
            | InputList Int

instance (Datable a) => Watchable (List a) where
  initialValue _ = ListData []
  getWatchableId (MapList n _ _) = n
  getWatchableId (FilterList n _ _) = n
  getWatchableId (InputList n) = n

  compile (MapList id f inner) = (getWatchableId inner, DepGraphChange id (mapf f)):(compile inner)
    where mapf f (ListChange (AddElement elem)) = [ListChange (AddElement (toData $ f $ fromData elem))]
          mapf f (ListChange (RemoveElement elem)) = [ListChange (RemoveElement (toData $ f $ fromData elem))]
  compile (FilterList id f inner) = (getWatchableId inner, DepGraphChange id (filterf f)):(compile inner)
    where filterf f (ListChange (AddElement elem))
            | f $ fromData elem = [ListChange (AddElement elem)]
            | otherwise = []
          filterf f (ListChange (RemoveElement elem))
            | f $ fromData elem = [ListChange (RemoveElement elem)]
            | otherwise = []
  compile (InputList n) = []

data ListDict k v = ShuffleList Int (v -> k) (List v)
                  | forall v0. Datable v0 => MapListDict Int (v0 -> v) (ListDict k v0)

instance (Datable k, Datable v) => Watchable (ListDict k v) where
  initialValue _ = MapData Map.empty
  getWatchableId (ShuffleList n _ _) = n
  getWatchableId (MapListDict n _ _) = n
  compile (ShuffleList id f inner) = (getWatchableId inner, DepGraphMapWalk id (shufflef f)):(compile inner)
    where shufflef f (ListChange (AddElement elem)) = toData $ f $ fromData elem
          shufflef f (ListChange (RemoveElement elem)) = toData $ f $ fromData elem

  compile (MapListDict id f inner) = (getWatchableId inner, DepGraphChange id (mapf f)):(compile inner)
    where mapf f (ListChange (AddElement elem)) = [ListChange (AddElement (toData $ f $ fromData elem))]
          mapf f (ListChange (RemoveElement elem)) = [ListChange (RemoveElement (toData $ f $ fromData elem))]

instance (Datable k, Datable v) => ContainerWatchable (ListDict k v) where
  initialValueAtPath ((MapPath d):[]) (ShuffleList _ _ _) = ListData []
  initialValueAtPath ((MapPath d):[]) (MapListDict _ _ _) = ListData []

applyChange :: Datable a => Map.Map Int [DepGraphAction] -> Struct -> List a -> Data -> a -> Data
applyChange dg struct input state change
   = walkChanges dg
                 struct
                 (getWatchableId input)
                 []
                 state
                 (ListChange $ AddElement $ toData change)

walkChanges :: Map.Map Int [DepGraphAction] -> Struct -> Int -> [PathElement] -> Data -> Change -> Data
walkChanges dg struct input path state change = foldr perform state actions
  where actions = fromJustDef [] $ Map.lookup input dg
        perform (DepGraphChange id f) state
          = foldl (walkChanges dg struct id path) state (f change) 
        perform (DepGraphStructWalk text) state
          = applyChangeAt struct ((StructPath text):path) ((StructPath text):path) change state
        perform (DepGraphMapWalk id f) state
          = walkChanges dg struct id ((MapPath $ f change):path) state change

applyChangeAt :: Struct -> [PathElement] -> [PathElement] -> Change -> Data -> Data
applyChangeAt struct p0 ((StructPath t):path) change (StructData state)
  = StructData $ Map.adjust (applyChangeAt struct p0 path change) t state
applyChangeAt struct p0 ((MapPath d):path) change (MapData state)
  = MapData $ Map.alter set d state
  where set (Just v) = Just $ applyChangeAt struct p0 path change v
        set Nothing  = Just $ applyChangeAt struct p0 path change (initialValueAtPath p0 struct)
applyChangeAt struct p0 [] (ListChange (AddElement elem)) (ListData elems)
  = ListData (elem:elems)
applyChangeAt struct p0 [] (ListChange (RemoveElement elem)) (ListData elems)
  = ListData (List.delete elem elems)
applyChangeAt struct p0 path change d
  = error $ "applyChangeAt got path " ++ show path ++ ", change " ++ show change ++ ", and data " ++ show d

{-
data Set a = forall b. MapSet Int (b -> a) (Set b)
           | FilterSet Int (a -> Bool) (Set a)

instance Watchable (Set a) where
  initialValue _ = SetData Set.empty
  getWatchableId (MapSet n _ _) = n
  getWatchableId (FilterSet n _ _) = n

mapSet f s = MapSet mkRef f s
filterSet f l = FilterSet mkRef f l
data SetDict k v = forall a. ShuffleSet Int (a -> k) (Set a)
-}




{-
class Mappable m a b where
  map :: (a -> b) -> m a -> m b

  class Filterable f a b where
  filter :: (a -> b) -> f a -> f b
-}

mapList :: forall a b. (Datable a, Datable b)
        => (a -> b) -> List a -> List b
mapList f l = (withRef MapList) f l
filterList f l = (withRef FilterList) f l


shuffle :: forall a k. (Datable a, Datable k)
        => (a -> k) -> List a -> ListDict k a
shuffle f list = (withRef ShuffleList) f list

mapListDict :: forall k a b. (Datable k, Datable a, Datable b)
            => (a -> b) -> ListDict k a -> ListDict k b
mapListDict f d = (withRef MapListDict) f d

inputList :: List a
inputList = withRef InputList

struct :: [(Text, WatchableThing)] -> Struct
struct elems = (withRef Struct) elems
