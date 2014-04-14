module Waltz where

import Prelude hiding (Integer, Float)
import qualified Prelude as Prelude

import Control.Monad.State
import qualified Data.Function
import qualified Data.Graph as Graph
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Safe

import qualified Debug.Trace as Trace

debugMode = True

trace = if debugMode then Trace.trace else (\x y -> y)

data Change = Change Context Impulse
            | AddWatcher Int Data -- what to watch
                         Context  -- what is watching
  deriving (Show)

type Context = Map.Map Int PathElement

data Impulse = ListImpulse !ListImpulse
             | IntImpulse !IntImpulse
             | FloatImpulse !FloatImpulse
             | ReplaceImpulse !Data
             | AddWatcherImpulse !Int !Int !Data !Context
  deriving (Show)

data ListImpulse = AddElement !Data
                 | RemoveElement !Data
  deriving (Show)

data IntImpulse = AddInteger !Prelude.Integer
                | MultiplyIntegerF !Prelude.Double
                | MultiplyInteger !Prelude.Integer
  deriving (Show)

data FloatImpulse = AddFloat !Prelude.Double
                  | MultiplyFloat !Prelude.Double
  deriving (Show)

data Data = ListData ![Data]
          | MapData !Int -- the id of the map
                    !Int -- the id of the relevant shuffler
                    !DefaultNode -- default value
                    !(Map.Map Data (Set.Set (Int, Context))) -- watchers
                    !(Map.Map Data Data) -- actual data
          | StructData !Int !(Map.Map Text Data)
          | IntegerData !Prelude.Integer
          | FloatData !Prelude.Double
          | StringData !Text
  deriving (Eq, Ord)

data DefaultNode = forall v. Watchable v => DefaultNode (Node v)
instance Eq DefaultNode where
  (DefaultNode (Node a _ _)) == (DefaultNode (Node b _ _)) = a == b
instance Ord DefaultNode where
  (DefaultNode (Node a _ _)) `compare` (DefaultNode (Node b _ _)) = a `compare` b
defaultValue (DefaultNode node) = nodeInitialValue node

instance Show Data where
  show x = showData x


showData (ListData xs) = show xs
showData (MapData _ _ _ _ m) = show m
showData (StructData _ m) = show m
showData (IntegerData i) = show i
showData (FloatData f) = show f
showData (StringData t) = show t

class Datable a where
  toData :: a -> Data
  fromData :: Data -> a

instance Datable a => Datable [a] where
  toData as = ListData $ map toData as
  fromData (ListData ds) = map fromData ds

instance Datable Prelude.Integer where
  toData i = IntegerData i
  fromData (IntegerData i) = i

instance Datable Prelude.Double where
  toData f = FloatData f
  fromData (FloatData f) = f

instance Datable Text where
  toData s = StringData s
  fromData (StringData s) = s



data AnyNode = forall a. (Watchable a, PPrint a) => AnyNode !(Node a)

addToChangeContext node pathElement = go
  where
    go (Change cxt impulse) = let cxt' = Map.insert node pathElement cxt
                               in [Change cxt' impulse]

data PathElement = StructPath Text | MapPath Data
  deriving (Show, Eq, Ord)

data Compiled = SimpleCompilation (Change -> [Change])
              | StatefulCompilation (Maybe Int) (Change -> Data -> [Change])
              | PartiallyTargetedCompilation (Maybe Int) (Change -> Data -> ([Change],[(Int,Change)]))
              | TargetedCompilation (Maybe Int) (Change -> Data -> [(Int, Change)])

class PPrint a => Watchable a where
  initialValue' :: Int -> [AnyNode] -> a -> Data
  initialValue :: Int -> [AnyNode] -> Context -> a -> (Data, [(Int, Change)])
  initialValue id inners cxt node = (initialValue' id inners node, [])
  compile :: a -> Compiled
  watchablePaths :: Int -> a -> [(Lookup, Maybe AnyNode)]
  watchablePaths _ _ = []

data Node a = Node !Int [AnyNode] (Maybe a)

data Lookup = LookupMap Int Int | LookupStruct Int Text
  deriving (Show)



nodeId (Node id _ _) = id
nodeInners (Node _ inners _) = inners
nodeW (Node _ _ (Just a)) = a

nodeInitialValue :: Watchable a => Node a -> Context -> (Data, [(Int, Change)])
nodeInitialValue (Node id inners (Just w)) cxt = trace ("nodeinitialvalue here at " ++ show id) $ initialValue id inners cxt w
nodeInitialValue (Node id (inner:_) Nothing) cxt = trace ("nodeinitialvalue at " ++ show id ++ " -> " ++ show (aNodeId inner)) $ aNodeInitialValue inner cxt

nodeCompile (Node _ _ Nothing) = SimpleCompilation $ return
nodeCompile (Node _ _ (Just w)) = compile w


aNodeId (AnyNode w) = nodeId w
aNodeInners (AnyNode w) = nodeInners w
aNodeInitialValue :: AnyNode -> Context -> (Data, [(Int, Change)])
aNodeInitialValue (AnyNode w) cxt = nodeInitialValue w cxt

type Const k = Node (ConstW k)
data ConstW k = (Datable k) => Const k
instance Watchable (ConstW k) where
  initialValue' id _ (Const k) = toData k
  compile (Const _) = SimpleCompilation $ error "Const is confused"

type Struct = Node StructW
data StructW = Struct [StructElem]
instance Watchable StructW where
  initialValue' _ _ _ = error "should always go to initialValue, not initialValue'"
  initialValue id _ cxt (Struct elems) = (StructData id val, watchers)
    where addElem :: StructElem -> (Map.Map Text Data, [(Int,Change)]) -> (Map.Map Text Data, [(Int,Change)])
          addElem elem@(Node _ _ (Just (StructElem _ key _))) (map, ws)
             = let (v, w) = nodeInitialValue elem cxt
                in (Map.insert key v map, w ++ ws)
          (val, watchers) = foldr addElem (Map.empty, []) elems
  compile (Struct _) = SimpleCompilation return
  watchablePaths structId (Struct elems) = concatMap (watchablePaths structId . nodeW) elems

type StructElem = Node StructElemW
data StructElemW = StructElem Int Text AnyNode

instance Watchable StructElemW where
  initialValue' _ _ _ = error "should always go to initialValue, not initialValue'"
  initialValue _ [w] cxt (StructElem _ _ _) = aNodeInitialValue w cxt
  compile (StructElem structId label _) = SimpleCompilation $
                                            addToChangeContext structId
                                                               (StructPath label)
  watchablePaths structId (StructElem _ label value) = [(LookupStruct structId label, Just value)]

type List a = Node (ListW a)
data ListW a = forall b. (Datable b) => MapList (b -> a)
             | FilterList (a -> Bool)

instance (Datable a) => Watchable (ListW a) where
  initialValue' _ _ _ = ListData []

  compile (MapList f) = SimpleCompilation $ \(Change cxt impulse) -> [Change cxt (mapf f impulse)]
    where mapf f (ListImpulse (AddElement elem)) = ListImpulse (AddElement (toData $ f $ fromData elem))
          mapf f (ListImpulse (RemoveElement elem)) = ListImpulse (RemoveElement (toData $ f $ fromData elem))
  compile (FilterList f) = SimpleCompilation $ \(Change cxt impulse) -> map (Change cxt) (filterf f impulse)
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
                          (Node v')  -- actual result value, constructed by
                                     --  applying the map function to a tube being
                                     --  filled by the dict being mapped over

data DictKey k = forall v. (Datable k, Watchable v) =>
                 DictKey (Dict k (Node v))  -- map whose key we're looking up

data DictSlowKey k = forall k0 v. (Datable k0, Datable k, Watchable v) =>
                     DictSlowKey (Dict k0 (Node v)) (k0 -> k)

instance (Datable k, Watchable v) => Watchable (DictW k (Node v)) where
  initialValue' id inners map = MapData id
                                        inner
                                        (DefaultNode $ dictMembersDefaultValue map)
                                        Map.empty
                                        Map.empty
    where
      inner = dictShuffler map
  
  compile (ShuffleList id f) = SimpleCompilation $ 
    \c@(Change cxt impulse) -> 
      addToChangeContext id (MapPath $ shufflef f impulse) c
    where shufflef f (ListImpulse (AddElement elem)) = trace ("shuffling " ++ show id ++  " " ++ show elem ++ " to " ++ show (toData $ f $ fromData elem)) $ 
                                                       toData $ f $ fromData elem
          shufflef f (ListImpulse (RemoveElement elem)) = toData $ f $ fromData elem

  compile (MapDict _ v) = SimpleCompilation $ return
  watchablePaths mapId (ShuffleList id _) = [(LookupMap mapId id, Nothing)]
  watchablePaths mapId (MapDict id v) = [(LookupMap mapId id, Just $ AnyNode v)]

dictMembersDefaultValue :: (Watchable v) => DictW k (Node v) -> (Node v)
dictMembersDefaultValue (ShuffleList _ _) = (Node (-1) [] Nothing)
dictMembersDefaultValue (MapDict _ d) = d

dictShuffler :: DictW k v -> Int
dictShuffler (ShuffleList id _) = id
dictShuffler (MapDict id _) = id

type DictLookup k v = Node (DictLookupW k)
data DictLookupW k = DictLookup (DictKey k) Int DefaultNode

instance Watchable (DictLookupW v) where
  initialValue' _ _ _ = error "should always go to initialValue, not initialValue'"
  initialValue _ _ cxt (DictLookup (DictKey _) _ def) = defaultValue def cxt
  compile (DictLookup (DictKey context) dictId _) = SimpleCompilation go
    where go change@(Change cxt _) = trace ("DictLookup " ++ show contextId ++ " -> " ++ show dictId) $
                                     addToChangeContext contextId p change
            where p = fromJustNote ("DictLookup " ++ show contextId ++ "->" ++ show dictId ++ " stymied") $
                                     Map.lookup dictId cxt
                  contextId = dictShuffler $ nodeW context


type StructLookup v = Node (StructLookupW)
data StructLookupW = StructLookup Text Struct

instance Watchable (StructLookupW) where
  initialValue' _ _ _ = error "should always go to initialValue, not initialValue'"
  initialValue _ _ cxt (StructLookup key struct) = let (StructData _ d, changes) = nodeInitialValue struct cxt
                                                    in (fromJustNote ("no default valuue for key " ++ show key ++ " in " ++ show d) $
                                                                     Map.lookup key d,
                                                       changes)
  compile (StructLookup key struct) = SimpleCompilation go
    where go change@(Change cxt _)
            | p == (StructPath key)  = [change]
            | otherwise              = []
            where p = fromJustNote ("StructLookup " ++ show (nodeId struct) ++ " stymied") $
                                     Map.lookup (nodeId struct) cxt



type MSet a = Node (MSetW a)
data MSetW a = forall a'. (a ~ Node a', Watchable a') =>
               DictValuesMSet Int (Node a')

instance Watchable (MSetW a) where
  initialValue' id _ (DictValuesMSet shufflerId d) = MapData id
                                                            shufflerId
                                                            (DefaultNode d)
                                                            Map.empty
                                                            Map.empty
  compile (DictValuesMSet _ _) = SimpleCompilation return


type DictSlowLookup k = Node (DictSlowLookupW k)
data DictSlowLookupW k = DictSlowLookup (DictSlowKey k) Int Int DefaultNode

instance Watchable (DictSlowLookupW v) where
  initialValue' _ _ _ = error "should always go to initialValue, not initialValue'"
  initialValue id _ cxt (DictSlowLookup key dictId _ def)
    = let (v, changes) = defaultValue def cxt
       in (v, (id, AddWatcher dictId (dictSlowLookupOutKey key cxt) cxt):changes)

  compile (DictSlowLookup key dictId shufflerId _)
    = PartiallyTargetedCompilation (Just dictId) $ \(Change cxt _) (MapData _ _ def _ map) ->
        let outKey = dictSlowLookupOutKey key cxt
            maybeValue = Map.lookup outKey map
            maybeValueWithChanges = fmap (,[]) maybeValue
            (value, changes) = fromJustDef (defaultValue def cxt) maybeValueWithChanges
         in ([Change cxt (ReplaceImpulse value),
              AddWatcher dictId outKey cxt],
             changes)
dictSlowLookupOutKey (DictSlowKey context f) cxt = toData $ f $ fromData inKey
  where contextId = dictShuffler $ nodeW context
        (MapPath inKey) = fromJustNote ("DictSlowLookup " ++ show contextId ++ " styimed in " ++ show cxt) $
                                       Map.lookup contextId cxt


type DictSlowLookupPropagator = Node DictSlowLookupPropagatorW
data DictSlowLookupPropagatorW = DictSlowLookupPropagator Int

instance Watchable DictSlowLookupPropagatorW where
  initialValue' _ _ _ = error "DictSlowLookupPropagator initialValue"
  compile (DictSlowLookupPropagator dictId)
    = TargetedCompilation (Just dictId) $ \(Change cxt impulse) (MapData _ shufflerId _ watcherMap _) ->
      let (MapPath shuffleKey) = fromJustNote ("DictSlowLookupPropagator failed lookup") $
                                              Map.lookup shufflerId cxt
          watchers = fromJustDef Set.empty $ Map.lookup shuffleKey watcherMap
       in [trace ("DictSlowLookupPropagator " ++ show dictId ++ " going to " ++ show i) $
           (i,(Change (Map.union c cxt) impulse)) | (i,c) <- Set.toList watchers]

type Integer = Node IntegerW
data IntegerW = SumInteger
              | ProductInteger
              | ToReplaceInteger
              | IntegerReplaceToProduct
              | IntegerReplaceToSum

instance Watchable IntegerW where
  initialValue' id _ (SumInteger) = IntegerData 0
  initialValue' id _ (ToReplaceInteger) = IntegerData 0
  initialValue' id _ (IntegerReplaceToProduct) = IntegerData 1
  initialValue' id _ (IntegerReplaceToSum) = IntegerData 0
  initialValue' id _ (ProductInteger) = IntegerData 1
  compile (SumInteger) 
    = SimpleCompilation $ \(Change cxt impulse) -> 
                            [Change cxt (sumf impulse)]
    where sumf (ListImpulse (AddElement (IntegerData d))) = IntImpulse $ AddInteger d
          sumf (ReplaceImpulse (IntegerData n)) = IntImpulse (AddInteger n) 
  compile (ProductInteger) 
    = SimpleCompilation $ \(Change cxt impulse) -> case impulse of
                            ReplaceImpulse (IntegerData n) -> [Change cxt (IntImpulse (MultiplyInteger n))]
                            otherwise -> [Change cxt impulse]
  compile (ToReplaceInteger)
    = StatefulCompilation Nothing $
                          \(Change cxt impulse) (IntegerData n) -> 
                            [Change cxt $ ReplaceImpulse $ replace impulse n]
    where replace (IntImpulse (AddInteger n')) n = IntegerData $ n' + n
          replace (IntImpulse (MultiplyInteger n')) n = IntegerData $ n' * n
  compile (IntegerReplaceToProduct)
    = StatefulCompilation Nothing $
                          \(Change cxt impulse) (IntegerData n) ->
                            [Change cxt $ prodf impulse n]
    where prodf (ReplaceImpulse (IntegerData 0)) oldn = ReplaceImpulse $ IntegerData 0
          prodf (ReplaceImpulse n) 0 = ReplaceImpulse n
          prodf (ReplaceImpulse (IntegerData n)) oldn
            = IntImpulse $ MultiplyIntegerF $ fromInteger n / fromInteger oldn
  compile (IntegerReplaceToSum)
    = StatefulCompilation Nothing $
                          \(Change cxt impulse) (IntegerData n) ->
                            [Change cxt $ prodf impulse n]
    where prodf (ReplaceImpulse (IntegerData 1)) oldn = ReplaceImpulse $ IntegerData 0
          prodf (ReplaceImpulse n) 1 = ReplaceImpulse n
          prodf (ReplaceImpulse (IntegerData n)) oldn
            = IntImpulse $ AddInteger $ fromInteger n - fromInteger oldn



type Float = Node FloatW
data FloatW = SumFloat
            | ProductFloat
            | InvFloat
            | IntToFloat
            | FloatReplaceToSum
            | FloatReplaceToProduct
            | ToReplaceFloat

instance Watchable FloatW where
  initialValue' _ _ _ = error "should always go to initialValue, not initialValue'"
  initialValue id _ _ (SumFloat) = (FloatData 0,[])
  initialValue id _ _ (ToReplaceFloat) = (FloatData 0,[])
  initialValue id _ _ (ProductFloat) = (FloatData 1,[])
  initialValue id _ _ (FloatReplaceToSum) = (FloatData 0,[])
  initialValue id _ _ (FloatReplaceToProduct) = (FloatData 1,[])
  initialValue id _ _ (InvFloat) = (FloatData 1,[])
  initialValue id [node] cxt (IntToFloat)
    = case aNodeInitialValue node cxt of
        (IntegerData n, changes) -> (FloatData $ fromIntegral n, changes)
        err                      -> error $ "No initialValue IntToFloat " ++ show err
  compile (SumFloat) 
    = SimpleCompilation $ \(Change cxt impulse) -> 
                            [Change cxt (sumf impulse)]
    where sumf (ListImpulse (AddElement (FloatData d))) = FloatImpulse $ AddFloat d
          sumf (ReplaceImpulse (FloatData d)) = FloatImpulse (AddFloat d)
          sumf (FloatImpulse (AddFloat n)) = FloatImpulse (AddFloat n)
  compile (ProductFloat) 
    = SimpleCompilation $ \(Change cxt impulse) -> case impulse of
                            ReplaceImpulse (FloatData n) -> [Change cxt (FloatImpulse (MultiplyFloat n))]
                            otherwise -> [Change cxt impulse]
  compile (InvFloat)
    = SimpleCompilation $ \(Change cxt impulse) -> 
                            [Change cxt (invf impulse)]
    where invf (FloatImpulse (MultiplyFloat f)) = FloatImpulse $ MultiplyFloat (1 / f)
          invf (ReplaceImpulse (FloatData n)) = ReplaceImpulse $ FloatData (1 / n)
          invf imp = error $ "can't InvFloat " ++ show imp
  compile (IntToFloat)
    = SimpleCompilation $ \(Change cxt impulse) ->
                            [Change cxt (toFf impulse)]
    where toFf (IntImpulse (MultiplyIntegerF n)) = FloatImpulse $ MultiplyFloat n
          toFf (IntImpulse (MultiplyInteger n)) = FloatImpulse $ MultiplyFloat $ fromInteger n
          toFf (IntImpulse (AddInteger n)) = FloatImpulse $ AddFloat $ fromInteger n
          toFf (ReplaceImpulse (IntegerData n)) = ReplaceImpulse $ FloatData $ fromInteger n
  compile (ToReplaceFloat)
    = StatefulCompilation Nothing $
                          \(Change cxt impulse) (FloatData n) -> 
                            [Change cxt $ ReplaceImpulse $ replace impulse n]
    where replace (FloatImpulse (AddFloat n')) n = FloatData $ n' + n
          replace (FloatImpulse (MultiplyFloat n')) n = FloatData $ n' * n
          replace (ReplaceImpulse n) _ = n
  compile (FloatReplaceToProduct)
    = StatefulCompilation Nothing $
                          \(Change cxt impulse) (FloatData n) ->
                            [Change cxt $ prodf impulse n]
    where prodf (ReplaceImpulse (FloatData 0)) oldn = ReplaceImpulse $ FloatData 0
          prodf (ReplaceImpulse n) 0 = ReplaceImpulse n
          prodf (ReplaceImpulse (FloatData n)) oldn
            = FloatImpulse $ MultiplyFloat $ n / oldn
  compile (FloatReplaceToSum)
    = StatefulCompilation Nothing $
                          \(Change cxt impulse) (FloatData n) ->
                            [Change cxt $ prodf impulse n]
    where prodf ~(ReplaceImpulse n) 1 = ReplaceImpulse n
          prodf (ReplaceImpulse (FloatData n)) oldn
            = FloatImpulse $ AddFloat $ n - oldn




type LandingSite = Int
type Propagators = Map.Map Int [Int]
type Modifiers = Map.Map Int Compiled
type LookupPaths = Map.Map Int [Lookup]
type PropOrder = Map.Map Int Int

fullCompile :: AnyNode -> (LandingSite, Propagators, Modifiers, LookupPaths, PropOrder)
fullCompile w = (aNodeId w,
                 compilePropagators w,
                 compileModifiers w,
                 compileLookupPaths w,
                 aNodePropOrder w)

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

compileLookupPaths :: AnyNode -> LookupPaths
compileLookupPaths = Map.map reverse . compileLookupPaths' [] . Just

compileLookupPaths' _ Nothing = Map.empty
compileLookupPaths' p (Just (AnyNode w)) = Map.unions (empty:more)
  where empty = Map.insert (nodeId w) p Map.empty
        more = [compileLookupPaths' (l:p) n
               |(l,n) <- watchablePaths (nodeId w) (nodeW w)]

mergeChanges :: (LandingSite, Propagators, Modifiers, LookupPaths, PropOrder) ->
                [(Int,Change)] ->
                [(Int,Change)] ->
                [(Int,Change)]
             
mergeChanges (_,_,_,_,propOrder) changes1 changes2
  = List.sortBy (compare `Data.Function.on` ((flip (Map.findWithDefault 0) propOrder) . fst)) $ changes1 ++ changes2

getNextChanges :: (LandingSite, Propagators, Modifiers, LookupPaths, PropOrder) ->
                      Change ->
                      Data ->
                      Int ->
                      [(Int,Change)]
getNextChanges compiled@(landingSite, propss, mods, paths, proporder)
               change@(Change contextFromChange _)
               stateValue
               node
  = [(prop, hereChange) | prop <- props, hereChange <- hereChanges] ++
    elsewhereChanges
  where props = maybe [] id $ Map.lookup node propss
        mod = fromJustNote ("No modifier for " ++ show node) $ Map.lookup node mods
        locatedChanges = case mod of 
                           SimpleCompilation f -> 
                             [(node, c) | c <- f change]
                           StatefulCompilation stateId f -> 
                             [(node, c)
                             | c <- f change (stateValueAt stateId)] ++ 
                             (stateValueWatchers stateId)
                           PartiallyTargetedCompilation stateId f ->
                             let (untargeted, targeted) = f change (stateValueAt stateId)
                              in [(node, c) | c <- untargeted] ++ targeted
                           TargetedCompilation stateId f ->
                             (f change (stateValueAt stateId)) ++ 
                             (stateValueWatchers stateId)
        hereChanges      = [c      | (l, c) <- locatedChanges, l == node]
        elsewhereChanges = [(l, c) | (l, c) <- locatedChanges, l /= node]
                             
        getStateValue stateId = let i = fromJustDef node stateId
                                    mp = Map.lookup i paths
                                    p = fromJustNote ("No path for " ++ show i ++ 
                                                        " for " ++ show paths)
                                                       mp
                                 in lookupByPath p contextFromChange stateValue
        stateValueWatchers = snd . getStateValue
        stateValueAt = fst . getStateValue

getNextChanges (landingSite, _, _, paths,_)
               change@(AddWatcher nodeToWatch keyToWatch watchingContext)
               stateValue
               watchingNode
  = [(landingSite,
      Change (Map.insert nodeToWatch 
                        (MapPath keyToWatch)
                        (addPathToContext p watchingContext))
             (AddWatcherImpulse nodeToWatch
                                watchingNode
                                keyToWatch
                                watchingContext))]
  where mp = Map.lookup nodeToWatch paths
        p = fromJustNote ("No path for AddWatcher " ++ show nodeToWatch ++
                          " for " ++ show paths)
                         mp
        addPathToContext ((LookupMap mapId shufflerId):path) ctx
          = let ctx' = addPathToContext path ctx
                p = fromJustNote ("no path for addPathToContext map " ++
                                                show shufflerId ++ " in " ++ show ctx) $
                                Map.lookup shufflerId ctx'
              in Map.insert mapId p ctx'
        addPathToContext ((LookupStruct structId structWalk):path) ctx
          = Map.insert structId
                       (StructPath structWalk)
                       (addPathToContext path ctx)
        addPathToContext [] ctx = ctx
       
lookupByPath [] _ v = (v, [])
lookupByPath ((LookupMap _ k):p) ctx (MapData _ _ d _ m)
  = (v', changes ++ changes')
  where ctxElement = fromJustNote ("No " ++ show k ++ 
                                    " in context when doing path lookup") $
                                  Map.lookup k ctx
        ctxPath = case ctxElement of
                    MapPath v -> v
                    _ -> error "Got structpath when needed mappath"
        maybeValue = Map.lookup ctxPath m
        maybeValueWithChanges = fmap (,[]) maybeValue
        (v,changes) = fromJustDef (defaultValue d ctx) maybeValueWithChanges
        (v',changes') = lookupByPath p ctx v
lookupByPath ((LookupStruct _ t):p) ctx (StructData _ m)
  = lookupByPath p ctx v
  where v = fromJustNote ("No " ++ show t ++ 
                          " in context when doing path lookup") $ 
                         Map.lookup t m

applyChange compiled stateWatchable nodeWatchable stateValue impulse
  = applyChanges compiled
                 stateValue
                 [(nodeId nodeWatchable, Change Map.empty impulse)]

compiledLandingSite (landingSite, _, _, _, _) = landingSite

applyChanges compiled stateValue [] = stateValue
applyChanges compiled stateValue ((nodeId, change):changes)
  = trace (show nodeId ++ ":\ttaking " ++ show change ++
                               "\n        to     " ++ show newChanges) $
    applyChanges compiled stateValue' $ changesFromDefaults ++
                                        (mergeChanges compiled changes newChanges)
  where newChanges = getNextChanges compiled change stateValue nodeId
        (stateValue', changesFromDefaults) | nodeId == compiledLandingSite compiled 
                                           = trace (show nodeId ++ " landing " ++ show change) $
                                             applyLandingChange change stateValue
                                           | otherwise
                                           = (stateValue,[])

applyLandingChange (Change context impulse) mapData@(MapData id shufflerId def watchers map)
  = case impulse of
      (AddWatcherImpulse mapToWatchId _ _ _) ->
        if mapToWatchId == id
          then (applyImpulse impulse mapData,[])
          else recurse
      otherwise ->
        recurse
  where pElem = fromJustNote ("can't find context for map " ++ show shufflerId
                                 ++ " in " ++ show context
                                 ++  " for " ++ show impulse) $
                             Map.lookup shufflerId context
        (MapPath p) = pElem
        maybeOldValue = Map.lookup p map
        (oldValue, newWatchers) = case maybeOldValue of
                                    Nothing -> defaultValue def context
                                    Just v -> (v, [])
        (value, newWatchers') = applyLandingChange (Change context impulse) oldValue
        map' = Map.insert p value map
        recurse = (MapData id shufflerId def watchers map', newWatchers ++ newWatchers')
applyLandingChange (Change context impulse) (StructData id struct)
  = case Map.lookup p struct of
      Just a -> let (v, changes) = applyLandingChange (Change context
                                                              impulse)
                                                      a
                 in (StructData id $ Map.insert p v struct, changes)
      Nothing -> error "this should never happen"
 
  where pElem = fromJustNote ("can't find context for struct " ++ show id) $
                             Map.lookup id context
        (StructPath p) = pElem
applyLandingChange (Change context impulse) value = (applyImpulse impulse value,[])

applyImpulse (ReplaceImpulse d) _ = d
applyImpulse (ListImpulse impulse) (ListData value) = ListData $ go impulse value
  where go (AddElement elem) elems = elem:elems
        go (RemoveElement elem) elems = List.delete elem elems
applyImpulse (IntImpulse impulse) (IntegerData value) = IntegerData $ go impulse value
  where go (AddInteger m) n = m + n
        go (MultiplyIntegerF m) n = round $ m * (fromInteger n)
        go (MultiplyInteger m) n = m * n
applyImpulse (FloatImpulse impulse) (FloatData value) = FloatData $ go impulse value
  where go (AddFloat m) n = m + n
        go (MultiplyFloat m) n = m * n
applyImpulse (AddWatcherImpulse nodeToWatch watchId key context) (MapData id shufflerId def watchers map)
  = trace ("watching " ++ show id ++ " key=" ++ show key) $ MapData id shufflerId def newWatchers map
  where newWatchers = Map.alter go key watchers
        elt = (watchId, context)
        go Nothing = Just $ Set.singleton elt
        go (Just s) = Just $ Set.insert elt s
applyImpulse impulse value = error $ "Can't apply impulse " ++ show impulse ++ " to " ++ show value

type Func = State Int

mkWatchable :: forall w. (Watchable w) => [AnyNode] -> w -> Func (Node w)
mkWatchable inners watchable = do id <- getNextId
                                  return $ Node id inners (Just watchable)
mkTube inners = do id <- getNextId
                   return $ Node id inners Nothing

getNextId :: Func Int
getNextId = do i <- get
               let i' = i + 1
               i' `seq` put i'
               return i

anyNode :: (Watchable a, PPrint a) => Node a -> Func AnyNode
anyNode n = return $ AnyNode n

-- precondition: ns only receive add changes
sumList :: List Prelude.Integer -> Func Integer
sumList ns = mkWatchable [AnyNode ns] SumInteger

-- precondition: ns only receive add changes
sumMSet :: MSet Float -> Func Float
sumMSet ns = mkWatchable [AnyNode ns] SumFloat

-- precondition: ns only receive multiply changes
productMSet :: MSet Integer -> Func Integer
productMSet ns = mkWatchable [AnyNode ns] ProductInteger

integerToReplace :: Integer -> Func Integer
integerToReplace n = mkWatchable [AnyNode n] ToReplaceInteger

integerReplaceToProduct :: Integer -> Func Integer
integerReplaceToProduct n = mkWatchable [AnyNode n] IntegerReplaceToProduct


floatToReplace :: Float -> Func Float
floatToReplace n = mkWatchable [AnyNode n] ToReplaceFloat

floatReplaceToSum :: Float -> Func Float
floatReplaceToSum n = mkWatchable [AnyNode n] FloatReplaceToSum

floatReplaceToProduct :: Float -> Func Float
floatReplaceToProduct n = mkWatchable [AnyNode n] FloatReplaceToProduct

intToFloat :: Integer -> Func Float
intToFloat n = mkWatchable [AnyNode n] IntToFloat

-- precondition: n only receives multiply changes
invFloat :: Float -> Func Float
invFloat n = mkWatchable [AnyNode n] InvFloat

-- precondition: b only receives multiply changes
divide :: Float -> Float -> Func Float
divide a b = do b' <- invFloat b
                mkWatchable [AnyNode a, AnyNode b'] ProductFloat

lengthList :: Datable a => List a -> Func Integer
lengthList l = do ones <- mapList (\_ -> (1 :: Prelude.Integer)) l
                  sumList ones

mapList :: forall a b. (Datable a, Datable b)
        => (a -> b) -> List a -> Func (List b)
mapList f l = mkWatchable [AnyNode l] (MapList f)
filterList :: forall a. (Datable a)
           => (a -> Bool) -> List a -> Func (List a)
filterList f l = mkWatchable [AnyNode l] (FilterList f)

shuffle :: forall a k. (Datable a, Datable k)
        => (a -> k) -> List a -> Func (Dict k (List a))
shuffle f l = do id <- getNextId
                 return $ Node id [AnyNode l] (Just $ ShuffleList id f)

mapDict :: forall k v0 v. (Datable k, Watchable v0, Watchable v)
        => ((Node v0) -> Func (Node v)) -> Dict k (Node v0) -> Func (Dict k (Node v))
mapDict f = mapDictWithKey (\k v -> f v)

mapDictWithKey :: forall k v0 v. (Datable k, Watchable v0, Watchable v)
               => (DictKey k -> Node v0 -> Func (Node v)) -> Dict k (Node v0) -> Func (Dict k (Node v))
mapDictWithKey f d = do output <- case nodeW d of
                                    (MapDict _ n) -> f (DictKey d) n
                                    otherwise -> do funnel <- mkTube [AnyNode d]
                                                    f (DictKey d) funnel
                        result <- mkWatchable [AnyNode output]
                                              (MapDict context output)
                        return result
      where context :: Int
            context = dictShuffler (nodeW d)

dictValues :: forall k v. (Datable k, Watchable v) => Dict k (Node v) -> Func (MSet (Node v))
dictValues node@(Node _ _ (Just dict))
  = mkWatchable [AnyNode node] $
                DictValuesMSet (dictShuffler dict)
                               (dictMembersDefaultValue dict)


structLookup :: Watchable a => Text -> Struct -> Func (Node a)
structLookup key struct
  = do lookup <- mkWatchable [AnyNode struct]
                             (StructLookup key struct)
       id <- getNextId
       return $ Node id [AnyNode lookup] Nothing

dictLookup :: (Datable k, Watchable v) =>
               DictKey k ->
               Dict k (Node v) ->
               Func (Node v)
dictLookup key map
  = do lookup <- mkWatchable [AnyNode map] 
                             (DictLookup key
                                         (dictShuffler $ nodeW map)
                                         (DefaultNode $ dictMembersDefaultValue $ nodeW map))
       id <- getNextId
       return $ Node id [AnyNode lookup] Nothing -- make a tube so it can come out with the right type

dictSlowLookup :: (PPrint v, Datable k, Watchable v) =>
                  DictSlowKey k ->
                  Dict k (Node v) ->
                  Func (Node v)
dictSlowLookup key@(DictSlowKey context f) map
 = do lookup <- mkWatchable [AnyNode context]
                            (DictSlowLookup key
                                            (nodeId map)
                                            (dictShuffler $ nodeW map)
                                            (DefaultNode $ dictMembersDefaultValue $ nodeW map))
      escaper <- mkWatchable [AnyNode map]
                             (DictSlowLookupPropagator (nodeId map))
      id <- getNextId
      return $ Node id [AnyNode lookup,AnyNode escaper] Nothing

dictSlowKey :: (Datable k, Datable k') => DictKey k -> (k -> k') -> DictSlowKey k'
dictSlowKey (DictKey n) f = DictSlowKey n f

mapSlowKey :: (Datable k, Datable k') => DictSlowKey k -> (k -> k') -> DictSlowKey k'
mapSlowKey (DictSlowKey n f1) f2 = DictSlowKey n (f2 . f1)

-- this is totally not typesafe
const :: (Datable k, Watchable w) => k -> Func (Node w)
const c = do a <- mkWatchable [] (Const c)
             mkTube [AnyNode a]

inputList :: Func (List a)
inputList = mkTube []

struct :: [(Text, Func AnyNode)] -> Func Struct
struct elemTuples = do id <- getNextId
                       elems <- mapM (elem id)
                                     elemTuples
                       return $ Node id (map AnyNode elems) (Just $ Struct elems)
  where elem structId (label, value)
          = do v <- value
               elemId <- getNextId
               return $ Node elemId
                             [v]
                             (Just $ StructElem structId label v)

anyNodeEdges (AnyNode node) = nodeEdges node
nodeEdges :: forall a. Node a -> [Graph.Edge]
nodeEdges node = [(aNodeId i,nodeId node) | i <- nodeInners node] ++ 
                 (concatMap anyNodeEdges (nodeInners node))

nodeGraph node = Graph.buildG (least,most) edges
  where edges = nodeEdges node
        allVertices = (map fst edges) ++ (map snd edges)
        least = minimum allVertices
        most = maximum allVertices
nodePropOrder = mkMap . reverse . Graph.topSort . nodeGraph
  where mkMap ids = Map.fromList $ zip ids [0..]
aNodePropOrder (AnyNode a) = nodePropOrder a

class PPrint a where
  pprint :: a -> String

instance PPrint (ConstW k) where
  pprint (Const _) = "Const"
instance PPrint StructW where
  pprint (Struct _) = "Struct"
instance PPrint StructElemW where
  pprint (StructElem _ text _) = show text
instance PPrint (ListW a) where
  pprint (MapList _) = "MapList"
  pprint (FilterList _) = "FilterList"
instance PPrint (DictW k v) where
  pprint (ShuffleList _ _) = "ShuffleList"
  pprint (MapDict shufflerId _) = "MapDict(shufflerId=" ++ show shufflerId ++ ")"
instance PPrint (MSetW a) where
  pprint (DictValuesMSet _ _) = "DictValuesMSet"
instance PPrint (DictLookupW v) where
  pprint (DictLookup _ _ _) = "DictLookup"
instance PPrint (StructLookupW) where
  pprint (StructLookup _ _) = "StructLookup"
instance PPrint (DictSlowLookupW v) where
  pprint (DictSlowLookup _ _ _ _) = "DictSlowLookup"
instance PPrint (DictSlowLookupPropagatorW) where
  pprint (DictSlowLookupPropagator _) = "DictSlowLookupPropagator"
instance PPrint (IntegerW) where
  pprint (SumInteger) = "SumInteger"
  pprint (ProductInteger) = "ProductInteger"
  pprint (ToReplaceInteger) = "ToReplaceInteger"
  pprint (IntegerReplaceToProduct) = "IntegerReplaceToProduct"
  pprint (IntegerReplaceToSum) = "IntegerReplaceToSum"
instance PPrint (FloatW) where
  pprint (SumFloat) = "SumFloat"
  pprint (ProductFloat) = "ProductFloat"
  pprint (FloatReplaceToSum) = "FloatReplaceToSum"
  pprint (FloatReplaceToProduct) = "FloatReplaceToProduct"
  pprint (ToReplaceFloat) = "ToReplaceFloat"
  pprint (InvFloat) = "InvFloat"
  pprint (IntToFloat) = "IntToFloat"

printNode :: Watchable a => Node a -> String
printNode node = show (nodeId node) ++ ":" ++ nodeString ++ 
                      "[\n" ++ 
                      unlines ["  " ++ l | l <- concatMap lines innerStrings] ++ 
                      "\n]"
  where innerStrings = map (\(AnyNode n) -> printNode n)
                           (nodeInners node)
        nodeString = case node of
                       Node _ _ Nothing -> "Tube"
                       Node _ _ (Just w) -> pprint w
