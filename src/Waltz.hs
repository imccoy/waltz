module Waltz where

import Data.Text (Text)
import qualified Data.Set as Set

type Struct = [(Text, WatchableThing)]

data WatchableThing = forall a. (Watchable a) => WatchableThing a

data Change = ListChange ListChange
            | SetChange ListChange
            | ChangeInKey Data Change

data ListChange = AddElement Data
                | RemoveElement Data
                | ChangeElement Data Data

data Data = ListData [Data]
          | SetData (Set.Set Data)
          | IntegerData Integer
          | StringData Text
  deriving (Eq, Ord)

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

newtype Watcher = Watcher (Change -> [Change])

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

data Set a = forall b. MapSet (b -> a) (Set b)
           | FilterSet (a -> Bool) (Set a)

data (Datable k, Datable v) =>
     ListDict k v = ShuffleList (v -> k) (List v)
                  | forall v0. Datable v0 => MapListDict (v0 -> v) (ListDict k v0)

instance (Datable k, Datable v) => Watchable (ListDict k v) where
  makeWatchers (ShuffleList f l) = (Watcher go):(makeWatchers l)
    where go change@(ListChange (AddElement elem))
            = [ChangeInKey (toData $ f $ fromData elem) change]
  makeWatchers (MapListDict f d) = (makeWatchers d)


data SetDict k v = forall a. ShuffleSet (a -> k) (Set a)

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
