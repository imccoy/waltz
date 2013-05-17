module Waltz where

import Safe
import Data.Text (Text)
import qualified Data.List as List
import qualified Data.Set as Set
import qualified Data.Map as Map

-- What's all this, then?
--
-- We've got a bunch of WatchableThings: Set, List, Dict
-- We have Change, representing changes of values held in those types
-- and we have Data, which represent the values that are changing
--
-- When you construct the watchable things, you get instructions for how to make
-- whichever set, list or dict you wanted. Whenever

data Change = ListChange ListChange
            | SetChange ListChange
            | ChangeInKey Data Change
            | StructElementChange Text [Change]
  deriving (Show)

data ListChange = AddElement Data
                | RemoveElement Data
                | ChangeElement Data Data
  deriving (Show)

data Data = ListData [Data]
          | SetData (Set.Set Data)
          | MapData (Map.Map Data Data)
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


class Watchable a where
  makeWatchers :: a -> [Watcher]
  initialValue :: a -> Data

newtype Watcher = Watcher (Change -> [Change])

data Struct = Struct [(Text, WatchableThing)]

data WatchableThing = forall a. (Watchable a) => WatchableThing a

instance Watchable Struct where
  makeWatchers (Struct s) = map mkChange s
    where mkChange (k, (WatchableThing v))
            = Watcher (\c ->
                [StructElementChange k $ concatMap (\(Watcher w) -> w c) (makeWatchers v)]
              )
  initialValue (Struct s) = MapData $ foldr add Map.empty s
    where add (k, (WatchableThing v)) m = Map.insert (toData k) (initialValue v) m

data List a = forall b. Datable b => MapList (b -> a) (List b) 
            | FilterList (a -> Bool) (List a) 
            | InputList

instance (Datable a) => Watchable (List a) where
  makeWatchers (MapList f l) = (Watcher go):(makeWatchers l)
    where go (ListChange (AddElement elem))
             = [ListChange $ AddElement $ toData (f $ fromData elem)]
          go (ListChange (RemoveElement elem))
             = [ListChange $ RemoveElement $ toData (f $ fromData elem)]
          go (ListChange (ChangeElement elem1 elem2))
             = [ListChange $ ChangeElement (toData (f $ fromData elem1))
                                           (toData (f $ fromData elem2))]
  makeWatchers (FilterList f l) = (Watcher go):(makeWatchers l)
    where go (ListChange (AddElement elem))
            | f $ fromData elem = [ListChange $ AddElement elem]
            | otherwise         = []
          go (ListChange (RemoveElement elem))
            | f $ fromData elem = [ListChange $ RemoveElement elem]
            | otherwise         = []
          go (ListChange (ChangeElement _ _))
            = error "so, this sucks"
  makeWatchers InputList = []

  initialValue _ = ListData []

data Set a = forall b. MapSet (b -> a) (Set b)
           | FilterSet (a -> Bool) (Set a)

data (Datable k, Datable v) =>
     ListDict k v = ShuffleList (v -> k) (List v)
                  | forall v0. Datable v0 => MapListDict (v0 -> v) (ListDict k v0)

instance (Datable k, Datable v) => Watchable (ListDict k v) where
  makeWatchers (ShuffleList f l) = (Watcher go):(makeWatchers l)
    where go change@(ListChange (AddElement elem))
            = [ChangeInKey (toData $ f $ fromData elem) change]
  makeWatchers (MapListDict f d) = [Watcher go]
    where go (ChangeInKey k change)
            = concatMap (\(Watcher w) -> map (ChangeInKey k) (w change)) ws
          ws = makeWatchers d


  initialValue _ = MapData Map.empty

data SetDict k v = forall a. ShuffleSet (a -> k) (Set a)


applyChange :: Data -> Change ->  Data
applyChange (ListData l) (ListChange (AddElement e)) = ListData $ e:l
applyChange (ListData l) (ListChange (RemoveElement e)) = ListData $ List.delete e l
applyChange (ListData l) (ListChange (ChangeElement old new))
   = ListData $ new:(List.delete old l)

applyChange (SetData l) (SetChange (AddElement e)) = SetData $ Set.insert e l
applyChange (SetData l) (SetChange (RemoveElement e)) = SetData $ Set.delete e l
applyChange (SetData l) (SetChange (ChangeElement old new))
   = SetData $ Set.insert new (Set.delete old l)

applyChange (MapData map) (ChangeInKey k c)
   = let valueAtKey = fromJustNote "no value at key" $ Map.lookup k map
         newValue = applyChange valueAtKey c
      in MapData $ Map.insert k newValue map

applyChange (MapData map) (StructElementChange n changes)
  = let value = fromJustNote ("no value at struct member " ++ show n) $ 
                  Map.lookup (toData n) map
        newValue = foldr (flip applyChange) value (reverse changes)
     in MapData $ Map.insert (toData n) newValue map

applyChange d c = error $ "No joy in change " ++ show c ++ " to " ++ show d

{-
class Mappable m a b where
  map :: (a -> b) -> m a -> m b

class Filterable f a b where
  filter :: (a -> b) -> f a -> f b
-}

mapList f l = MapList f l
filterList f l = FilterList f l

mapSet f s = MapSet f s
filterSet f l = FilterSet f l

shuffle :: forall a k. (Datable a, Datable k)
        => (a -> k) -> List a -> ListDict k a
shuffle f list = ShuffleList f list

mapListDict :: forall k a b. (Datable k, Datable a, Datable b)
            => (a -> b) -> ListDict k a -> ListDict k b
mapListDict f d = MapListDict f d
