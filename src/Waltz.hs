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

data AnyNode = forall a. (Watchable a) => AnyNode (Node a)


addToChangeContext node pathElement (Change cxt impulse) = [Change cxt' impulse]
  where cxt' = Map.insert node pathElement cxt

data PathElement = StructPath Text | MapPath Data
  deriving Show

type Compiled = Change -> [Change]

class Watchable a where
  initialValue :: Int -> [AnyNode] -> a -> Data
  compile :: a -> Compiled

data Node a = Node Int [AnyNode] a | Tube Int [AnyNode]

nodeId (Node id _ _) = id
nodeId (Tube id _) = id

nodeInners (Node _ inners _) = inners
nodeInners (Tube _ inners) = inners

nodeW (Node _ _ a) = a


nodeInitialValue (Node id inners w) = initialValue id inners w

nodeCompile (Tube _ _) = return
nodeCompile (Node _ _ w) = compile w


aNodeId (AnyNode w) = nodeId w
aNodeInners (AnyNode w) = nodeInners w
aNodeInitialValue (AnyNode w) = nodeInitialValue w

type Struct = Node StructW
data StructW = Struct [StructElem]
instance Watchable StructW where
  initialValue id _ (Struct elems) = StructData id $ foldr addElem Map.empty elems
    where addElem :: StructElem -> (Map.Map Text Data) -> (Map.Map Text Data)
          addElem elem@(Node _ _ (StructElem _ key)) map
             = Map.insert key (nodeInitialValue elem) map
  compile (Struct _) = return

type StructElem = Node StructElemW
data StructElemW = StructElem Int Text

instance Watchable StructElemW where
  initialValue _ [w] (StructElem _ _) = aNodeInitialValue w
  compile (StructElem structId label) = addToChangeContext structId
                                                           (StructPath label)

type List a = Node (ListW a)
data ListW a = forall b. (Datable b) => MapList (b -> a)
             | FilterList (a -> Bool)

instance (Datable a) => Watchable (ListW a) where
  initialValue _ _ _ = ListData []

  compile (MapList f) (Change cxt impulse) = [Change cxt (mapf f impulse)]
    where mapf f (ListImpulse (AddElement elem)) = ListImpulse (AddElement (toData $ f $ fromData elem))
          mapf f (ListImpulse (RemoveElement elem)) = ListImpulse (RemoveElement (toData $ f $ fromData elem))
  compile (FilterList f) (Change cxt impulse) = map (Change cxt) (filterf f impulse)
    where filterf f (ListImpulse (AddElement elem))
            | f $ fromData elem = [ListImpulse (AddElement elem)]
            | otherwise = []
          filterf f (ListImpulse (RemoveElement elem))
            | f $ fromData elem = [ListImpulse (RemoveElement elem)]
            | otherwise = []


type Dict k v = Node (DictW k v)
data DictW k v = forall elem. (Datable elem) 
               => ShuffleList Int (elem -> k)
               | forall v'. (v ~ Node v', Watchable v')
               => MapDict Int        -- id of the Dict that gives us our context
                          Data       -- default value in result
                          (Node v')  -- actual result value, constructed by
                                     --  applying the map function to a tube being
                                     --  filled by the dict being mapped over

instance (Datable k, Watchable v) => Watchable (DictW k (Node v)) where
  initialValue id inners map = MapData inner
                                       (valueAtKey map)
                                       Map.empty
    where
      inner = ultimateInnerDict map
      valueAtKey (ShuffleList _ _) = ListData []
      valueAtKey (MapDict _ d _) = d
  
  compile (ShuffleList id f) c@(Change cxt impulse) = addToChangeContext id (MapPath $ shufflef f impulse) c
    where shufflef f (ListImpulse (AddElement elem)) = toData $ f $ fromData elem
          shufflef f (ListImpulse (RemoveElement elem)) = toData $ f $ fromData elem

  compile mapDict@(MapDict _ _ v) c = nodeCompile v c

ultimateInnerDict :: DictW k v -> Int
ultimateInnerDict (ShuffleList id _) = id
ultimateInnerDict (MapDict id _ _) = id

type Integer = Node IntegerW
data IntegerW = SumInteger

instance Watchable IntegerW where
  initialValue id _ (SumInteger) = IntegerData 0
  compile (SumInteger) (Change cxt impulse) = [Change cxt (sumf impulse)]
    where sumf (ListImpulse (AddElement (IntegerData d))) = IntImpulse $ AddInteger d

type LandingSite = Int
type Propagators = Map.Map Int [Int]
type Modifiers = Map.Map Int (Change -> [Change])

fullCompile :: AnyNode -> (LandingSite, Propagators, Modifiers)
fullCompile w = (aNodeId w, compilePropagators w, compileModifiers w)

compilePropagators :: AnyNode -> Propagators
compilePropagators = (foldr compilePropagators' Map.empty) . allWatchables
compilePropagators' :: AnyNode -> Propagators -> Propagators
compilePropagators' (AnyNode to) m
  = trace (show (nodeId to) ++ ":  adding propagators " ++ show (map aNodeId (nodeInners to))) $
    foldr go m (nodeInners to)
  where go :: AnyNode -> Propagators -> Propagators
        go (AnyNode from) m = add from to m
        add from to m = Map.insert (nodeId from)
                                   ((nodeId to):(old from m))
                                   m
        old from m = Map.findWithDefault [] (nodeId from) m


compileModifiers = (foldr compileOne Map.empty) . allWatchables
  where compileOne (AnyNode w) = trace (show (nodeId w) ++ ": compiling modifiers") $
                                        Map.insert (nodeId w)
                                                   (nodeCompile w)

allWatchables w = uniqBy aNodeId $ allWatchables' w
allWatchables' w = w:(concat (map allWatchables $ aNodeInners w))
uniqBy f [] = []
uniqBy f (w:ws) = w:(uniqBy f [w' | w' <- ws, f w /= f w'])

getLandingChanges :: (LandingSite, Propagators, Modifiers) -> Impulse -> Int -> [Change]
getLandingChanges compiled imp node = getLandingChanges' compiled change node
  where change = Change Map.empty imp

getLandingChanges' :: (LandingSite, Propagators, Modifiers) -> Change -> Int -> [Change]
getLandingChanges' compiled@(landingSite, propss, mods) change node
  = landing ++ (concat [ getLandingChanges' compiled c l
                       | l <- trace (show node ++ ": jumping to " ++ show props) props,
                         c <- trace (show node ++ ": transforming " ++ show change) $
                              trace (show node ++ ": to " ++ show changes) $
                                    changes
                       ])
  where props = maybe [] id $ Map.lookup node propss
        mod = fromJustNote ("No modifier for " ++ show node) $ Map.lookup node mods
        changes = mod change
        landing = if node == landingSite then [change] else []

applyChange compiled stateWatchable nodeWatchable stateValue impulse
  = let landingChanges = getLandingChanges compiled impulse (nodeId nodeWatchable)
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

mkWatchable inners = (withRef Node) inners

lengthList :: Datable a => List a -> Integer
lengthList l = mkWatchable [AnyNode $ mapList (\_ -> (1 :: Prelude.Integer)) l]
                           SumInteger

mapList :: forall a b. (Datable a, Datable b)
        => (a -> b) -> List a -> List b
mapList f l = mkWatchable [AnyNode l] (MapList f)
filterList :: forall a. (Datable a)
           => (a -> Bool) -> List a -> List a
filterList f l = mkWatchable [AnyNode l] (FilterList f)


shuffle :: forall a k. (Datable a, Datable k)
        => (a -> k) -> List a -> Dict k (List a)
shuffle f l = withRef (\n -> Node n [AnyNode l] (ShuffleList n f))

mapDict :: forall k v0 v. (Datable k, Watchable v0, Watchable v)
        => ((Node v0) -> (Node v)) -> Dict k (Node v0) -> Dict k (Node v)
mapDict f d = mkWatchable [AnyNode output]
                          (MapDict context def output)
  where 
        context :: Int
        context = ultimateInnerDict (nodeW d)
        def :: Data
        def = nodeInitialValue output
        funnel :: Node v0
        funnel = (withRef Tube) [AnyNode d]
        output :: Node v
        output = f funnel -- TODO confirm application of f to different
                          --      funnels yields watchables with different
                          --      ids.


inputList :: List a
inputList = (withRef Tube) []

struct :: [(Text, AnyNode)] -> Struct
struct elemTuples = (withRef structN) elemTuples

structN :: Int -> [(Text, AnyNode)] -> Struct
structN n elemTuples = let struct = Node n (map AnyNode elems) (Struct elems)
                           elems = [mkWatchable [w] (StructElem n t)
                                   |(t,w) <- elemTuples]
                        in struct

