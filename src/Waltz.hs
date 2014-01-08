module Waltz where

import Prelude hiding (Integer)
import qualified Prelude as Prelude

import Data.IORef
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Safe
import System.IO.Unsafe

import qualified Debug.Trace as Trace

debugMode = True

trace = if debugMode then Trace.trace else (\x y -> y)

{-# NOINLINE idRef #-} 
idRef :: IORef Int
idRef = unsafePerformIO $ newIORef 0

{-# NOINLINE withRef #-} 
withRef :: (Int -> b) -> b
withRef f = f $ unsafePerformIO $ do
  id <- readIORef idRef
  writeIORef idRef (id + 1)
  return id


data Change = Change Context Impulse
  deriving (Show)

type Context = Map.Map Int PathElement

data Impulse = ListImpulse !ListImpulse
            | IntImpulse !IntImpulse
  deriving (Show)

data ListImpulse = AddElement !Data
                | RemoveElement !Data
  deriving (Show)

data IntImpulse = AddInteger !Prelude.Integer
  deriving (Show)

data Data = ListData ![Data]
          | SetData !(Set.Set Data)
          | MapData Int !Data !(Map.Map Data Data)
          | StructData Int !(Map.Map Text Data)
          | IntegerData !Prelude.Integer
          | StringData !Text
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

instance Datable Prelude.Integer where
  toData i = IntegerData i
  fromData (IntegerData i) = i

instance Datable Text where
  toData s = StringData s
  fromData (StringData s) = s

data WatchableThing = forall a. (Watchable a) =>
                      WatchableThing a

wtId (WatchableThing a) = getWatchableId a
wtInners (WatchableThing a) = getInners a
wtInitialValue (WatchableThing a) = initialValue a

addToChangeContext loc pathElement (Change cxt impulse) = [Change cxt' impulse]
  where cxt' = Map.insert loc pathElement cxt


data PathElement = StructPath Text | MapPath Data
  deriving Show

type Compiled = Change -> [Change]

class PPrint a => Watchable a where
  initialValue :: a -> Data
  compile :: a -> Compiled
  getWatchableId :: a -> Int
  mkTube :: WatchableThing -> a
  getInners :: a -> [WatchableThing]

data Struct = Struct Int [StructElem]
            | TubeStruct Int WatchableThing
instance Watchable Struct where
  initialValue (Struct id elems) = StructData id $ foldr addElem Map.empty elems
    where addElem elem@(StructElem _ _ key _) map = Map.insert key (initialValue elem) map
  getWatchableId (Struct id _) = id
  compile (Struct id structElems) = return
  getInners struct@(Struct id structElems)
   = map WatchableThing structElems
  mkTube = (withRef TubeStruct)

data StructElem = StructElem Int Struct Text WatchableThing

structElemWatchable (StructElem _ _ _ w) = w

instance Watchable StructElem where
  initialValue (StructElem _ _ label (WatchableThing w)) = initialValue w
  getWatchableId (StructElem id _ _ w) = id
  compile (StructElem id struct label w) = addToChangeContext (getWatchableId struct) (StructPath label)
  getInners elem = [structElemWatchable elem]
  mkTube = error "No StructElem mkTube"

data List a = forall b. Datable b => MapList Int (b -> a) (List b) 
            | FilterList Int (a -> Bool) (List a) 
            | InputList Int
            | TubeList Int WatchableThing

instance (Datable a) => Watchable (List a) where
  initialValue _ = ListData []
  getWatchableId (MapList n _ _) = n
  getWatchableId (FilterList n _ _) = n
  getWatchableId (InputList n) = n
  getWatchableId (TubeList n _) = n

  compile (MapList id f inner) (Change cxt impulse) = [Change cxt (mapf f impulse)]
    where mapf f (ListImpulse (AddElement elem)) = ListImpulse (AddElement (toData $ f $ fromData elem))
          mapf f (ListImpulse (RemoveElement elem)) = ListImpulse (RemoveElement (toData $ f $ fromData elem))
  compile (FilterList id f inner) (Change cxt impulse) = map (Change cxt) (filterf f impulse)
    where filterf f (ListImpulse (AddElement elem))
            | f $ fromData elem = [ListImpulse (AddElement elem)]
            | otherwise = []
          filterf f (ListImpulse (RemoveElement elem))
            | f $ fromData elem = [ListImpulse (RemoveElement elem)]
            | otherwise = []
  compile (InputList n) c = [c]
  compile (TubeList n _) c = [c]

  getInners (MapList _ _ i) = [WatchableThing i]
  getInners (FilterList _ _ i) = [WatchableThing i]
  getInners (InputList _) = []
  getInners (TubeList _ i) = [i]

  mkTube = withRef TubeList

data Dict k v = forall elem. (List elem ~ v, Datable elem, Watchable v) 
                => ShuffleList Int (elem -> k) v
              | forall v0. (Watchable v0, Watchable v)
                => MapDict Int                -- id
                           v                  -- default value in result
                           (v0 -> v)          -- map function
                           Compiled
                           v
                           (Dict k v0)        -- inner
              | TubeDict Int WatchableThing

instance (Datable k, Watchable v) => Watchable (Dict k v) where
  initialValue map = inner `seq` MapData inner
                                         (valueAtKey map)
                                         Map.empty
    where
      inner = ultimateInnerDict map
      valueAtKey :: forall k v. Dict k v -> Data
      valueAtKey (ShuffleList _ _ _) = ListData []
      valueAtKey (MapDict _ d _ _ _ _) = initialValue d
      valueAtKey (TubeDict _ v) = wtInitialValue v
  
  getWatchableId (ShuffleList n _ _) = n
  getWatchableId (MapDict n _ _ _ _ _) = n
  getWatchableId (TubeDict n _) = n

  compile (ShuffleList id f inner) c@(Change cxt impulse) = addToChangeContext id (MapPath $ shufflef f impulse) c
    where shufflef f (ListImpulse (AddElement elem)) = toData $ f $ fromData elem
          shufflef f (ListImpulse (RemoveElement elem)) = toData $ f $ fromData elem

  compile mapDict@(MapDict id _ _ compiled _ _) c = compiled c
  compile (TubeDict _ v) c = [c]

  mkTube = withRef TubeDict
  getInners (ShuffleList _ _ inner) = [WatchableThing inner]
  getInners (MapDict id _ _ _ output inner) = [WatchableThing output]


ultimateInnerDict :: (Datable k, Watchable v) => Dict k v -> Int
ultimateInnerDict (ShuffleList id _ _) = id
ultimateInnerDict (MapDict id _ _ _ _ inner) = ultimateInnerDict inner
          


data Integer = SumInteger Int (List Prelude.Integer)
             | TubeInteger Int WatchableThing

instance Watchable Integer where
  initialValue (SumInteger _ w) = IntegerData 0
  getWatchableId (SumInteger id _) = id
  getWatchableId (TubeInteger id _) = id
  compile (SumInteger id inner) (Change cxt impulse) = [Change cxt (sumf impulse)]
    where sumf (ListImpulse (AddElement (IntegerData d))) = IntImpulse $ AddInteger d
  compile (TubeInteger _ _) c = [c]
  mkTube = withRef TubeInteger
  getInners (SumInteger id inner) = [WatchableThing inner]


type LandingSite = Int
type Propagators = Map.Map Int [Int]
type Modifiers = Map.Map Int (Change -> [Change])

fullCompile :: WatchableThing -> (LandingSite, Propagators, Modifiers)
fullCompile w = (wtId w, compilePropagators w, compileModifiers w)

compilePropagators :: WatchableThing -> Propagators
compilePropagators = (foldr compilePropagators' Map.empty) . allWatchables
compilePropagators' :: WatchableThing -> Propagators -> Propagators
compilePropagators' (WatchableThing to) m
  = trace (show (getWatchableId to) ++ ":  adding propagators " ++ show (map wtId (getInners to))) $
    foldr go m (getInners to)
  where go :: WatchableThing -> Propagators -> Propagators
        go (WatchableThing from) m = add from to m
        add from to m = Map.insert (getWatchableId from)
                                   ((getWatchableId to):(old from m))
                                   m
        old from m = Map.findWithDefault [] (getWatchableId from) m


compileModifiers = (foldr compileOne Map.empty) . allWatchables
  where compileOne (WatchableThing w) = trace (show (getWatchableId w) ++ ": compiling modifiers") $
                                        Map.insert (getWatchableId w)
                                                   (compile w)

allWatchables w = uniqBy wtId $ allWatchables' w
allWatchables' w = w:(concat (map allWatchables $ wtInners w))
uniqBy f [] = []
uniqBy f (w:ws) = w:(uniqBy f [w' | w' <- ws, f w /= f w'])

getLandingChanges :: (LandingSite, Propagators, Modifiers) -> Impulse -> Int -> [Change]
getLandingChanges compiled imp loc = getLandingChanges' compiled change loc
  where change = Change Map.empty imp

getLandingChanges' :: (LandingSite, Propagators, Modifiers) -> Change -> Int -> [Change]
getLandingChanges' compiled@(landingSite, propss, mods) change loc
  = landing ++ (concat [ getLandingChanges' compiled c l
                       | l <- trace (show loc ++ ": jumping to " ++ show props) props,
                         c <- trace (show loc ++ ": transforming " ++ show change) $
                              trace (show loc ++ ": to " ++ show changes) $
                                    changes
                       ])
  where props = maybe [] id $ Map.lookup loc propss
        mod = fromJustNote ("No modifier for " ++ show loc) $ Map.lookup loc mods
        changes = mod change
        landing = if loc == landingSite then [change] else []

applyChange compiled stateWatchable locWatchable stateValue impulse
  = let landingChanges = getLandingChanges compiled impulse (getWatchableId locWatchable)
     in applyChanges stateWatchable landingChanges stateValue

applyChanges stateWatchable changes stateValue
  = foldr (\c s -> let result = applyLandingChange c s
                    in trace ("applying change " ++ show c ++ "\nin " ++ show s) $
                       trace ("yielding " ++  show result ++ "\n\n") $
                       applyLandingChange c s)
          stateValue changes

applyLandingChange (Change context impulse) (MapData id def map)
  = MapData id def $ Map.alter (maybe (trace "defaulting" $ Just $ applyLandingChange (Change context impulse) def)
                                      (Just . (applyLandingChange (Change context impulse))))
                               p
                               map
  where pElem = fromJustNote ("can't find context for map " ++ show id) $
                             Map.lookup id context
        (MapPath p) = pElem
applyLandingChange (Change context impulse) (StructData id struct)
  = StructData id  $ Map.alter (fmap (applyLandingChange $ Change context impulse))
                               p
                               struct
  where pElem = fromJustNote ("can't find context for map " ++ show id) $
                             Map.lookup id context
        (StructPath p) = pElem
applyLandingChange (Change context impulse) value = applyImpulse impulse value

applyImpulse (ListImpulse impulse) (ListData value) = ListData $ go impulse value
  where go (AddElement elem) elems = elem:elems
        go (RemoveElement elem) elems = List.delete elem elems
applyImpulse (IntImpulse impulse) (IntegerData value) = IntegerData $ go impulse value
  where go (AddInteger m) n = m + n
applyImpulse impulse value = error $ "Can't apply impulse " ++ show impulse ++ " to " ++ show value

lengthList :: Datable a => List a -> Integer
lengthList = (withRef SumInteger) . (mapList (\_ -> (1 :: Prelude.Integer)))

mapList :: forall a b. (Datable a, Datable b)
        => (a -> b) -> List a -> List b
mapList f l = (withRef MapList) f l
filterList f l = (withRef FilterList) f l


shuffle :: forall a k. (Datable a, Datable k)
        => (a -> k) -> List a -> Dict k (List a)
shuffle f list = (withRef ShuffleList) f list

mapDict :: forall k v0 v. (Datable k, Watchable v0, Watchable v)
        => (v0 -> v) -> Dict k v0 -> Dict k v
mapDict f d = (withRef MapDict) def
                                f
                                compiled
                                output
                                d
  where def = f $ dictValueWatcher d
        funnel = mkTube $ WatchableThing d
        output = f $ funnel -- TODO confirm application of f to different
                            --      funnels yields watchables with different
                            --      ids.
        compiled = compile output

dictValueWatcher :: Dict k v -> v
dictValueWatcher (ShuffleList _ _ _) = inputList
dictValueWatcher (MapDict _ innerDefaultWatcher _ _ _ _) = innerDefaultWatcher


inputList :: List a
inputList = withRef InputList

struct :: [(Text, WatchableThing)] -> Struct
struct elemTuples = (withRef structN) elemTuples

structN n elemTuples = let struct = Struct n elems
                           elems = [(withRef StructElem) struct t w
                                   |(t,w) <- elemTuples]
                        in struct


pprintw :: Int -> String -> Int -> [String] -> String
pprintw d n id children = (replicate (d*4) ' ') ++ n ++ ":" ++ show id ++
                          "[\n" ++ unlines children ++ (replicate (d*4) ' ') ++ "]"
 
class PPrint a where
  pprint :: Int -> a -> String

instance PPrint WatchableThing where
  pprint d (WatchableThing w) = pprint d w

instance PPrint Struct where
  pprint d (Struct id elems) = pprintw d "Struct" id (map (pprint $ d+1) elems)

instance PPrint StructElem where
  pprint d (StructElem id struct l w) = pprintw d ("StructElem(" ++ show l ++ ")") id [pprint (d+1) w]

instance PPrint (List a) where
  pprint d (MapList id f inner) = pprintw d "MapList" id [pprint (d+1) inner]
  pprint d (FilterList id f inner) = pprintw d "FilterList" id [pprint (d+1)  inner]
  pprint d (InputList id) = pprintw d "InputList" id []
  pprint d (TubeList id inner) = pprintw d "TubeList" id [pprint (d+1) inner]

instance (Datable k, Watchable v) => PPrint (Dict k v) where
  pprint d (ShuffleList id f inner) = pprintw d "ShuffleList" id [pprint (d+1) inner]
  pprint d (MapDict id def f compiled outTube inner)
     = pprintw d "MapDict" id [replicate (d*4 + 2) ' ' ++ "Inner,", pprint (d+1) inner,
                               replicate (d*4 + 2) ' ' ++ "OutTube,", pprint (d+1) outTube]
  pprint d (TubeDict id inner) = pprintw d "TubeDict" id [pprint (d+1) inner]

instance PPrint Integer where
  pprint d (SumInteger id inner) = pprintw d "SumInteger" id [pprint (d+1) inner]
  pprint d (TubeInteger id _) = pprintw d "TubeInteger" id []

