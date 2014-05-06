module Waltz where

import Prelude hiding (Integer, Float, all, elem)
import qualified Prelude as Prelude

import Control.Monad.State
import Data.Foldable (all, elem)
import qualified Data.Function
import qualified Data.Graph as Graph
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set
import Data.Text (Text)
import Safe

import qualified Debug.Trace as Trace

debugMode = True

trace = if debugMode then Trace.trace else (\x y -> y)

data Change = Change Context Impulse

instance Show Change where
  show (Change cxt imp) = "Change " ++ show imp ++ "@[" ++ show cxt ++ "]"

data Watch = Watch Int Context  -- what is watching
                   Int Context  -- what is being watched
  deriving (Show)

type Context = Map.Map Int Data

data Impulse = ListImpulse !ListImpulse
             | IntImpulse !IntImpulse
             | FloatImpulse !FloatImpulse
             | ReplaceImpulse !Data
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
          | IntegerData !Prelude.Integer
          | FloatData !Prelude.Double
          | StringData !Text
  deriving (Eq, Ord)

data UniverseData = UniverseData Data
                  | UniverseList [UniverseData]
                  | UniverseDict (Map.Map Data UniverseData)
                  | UniverseStruct (Map.Map Text UniverseData)
  deriving (Show)

type DefaultValue = Data
type RequiredContext = Set.Set Int
type UniverseSlice = (DefaultValue, RequiredContext, Map.Map Context (Data, Set.Set (Int,Context)))
type Universe = Map.Map Int UniverseSlice

universeSliceRequiredContext :: UniverseSlice -> RequiredContext
universeSliceRequiredContext (_, rc, _) = rc

universeSliceValues (_, _, m) = m
universeSliceDefault (d, _, _) = d

universeSliceGet :: UniverseSlice -> Context -> (Data, Set.Set (Int,Context))
universeSliceGet (d, rc, m) cxt = fromJustDef (d, Set.empty) $ Map.lookup (requiredContextReduceContext rc cxt) m

requiredContextAcceptsContext :: RequiredContext -> Context -> Bool
requiredContextAcceptsContext rc cxt = all (`elem` Map.keys cxt) $ rc

requiredContextReduceContext :: RequiredContext -> Context -> Context
requiredContextReduceContext rc cxt = Map.filterWithKey (\k v -> k `elem` rc) cxt

universeSliceAcceptsContext :: UniverseSlice -> Context -> Bool
universeSliceAcceptsContext us c = requiredContextAcceptsContext (universeSliceRequiredContext us) c

universeSliceReduceContext :: UniverseSlice -> Context -> Context
universeSliceReduceContext us c = requiredContextReduceContext (universeSliceRequiredContext us) c

instance Show Data where
  show x = showData x


showData (ListData xs) = show xs
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



data AnyNode = forall a. (Watchable a, PPrint a, UniverseDatable a) => AnyNode !(Node a)

addToChangeContext node pathElement = go
  where
    go (Change cxt impulse) = let cxt' = Map.insert node pathElement cxt
                               in [Change cxt' impulse]

data Compiled = SimpleCompilation (Change -> [Change])
              | StatefulCompilation (Change -> Data -> [Change])
              | DictLookupCompilation (Change -> (Int, Int, Data))

class PPrint a => Watchable a where
  compile :: a -> Compiled
  dictValId :: Node a -> Int
  dictValId (Node id _ (Just _)) = id
  dictValId (Node _ [AnyNode n] Nothing) = dictValId n
  eval :: Node a -> Context -> (Data, [Watch])
  eval node@(Node _ ns _) cxt = (evalValue node, concat [snd (eval n cxt)|(AnyNode n) <- ns])
  evalValue :: Node a -> Data
  evalValue _ = error "no evalValue"
  nodeDependencies :: Node a -> [AnyNode]
  nodeDependencies (Node _ ds _) = ds

data Node a = Node !Int [AnyNode] (Maybe a)

nodeId (Node id _ _) = id
nodeInners (Node _ inners _) = inners
nodeW (Node _ _ (Just a)) = a

nodeCompile (Node _ _ Nothing) = SimpleCompilation $ return
nodeCompile (Node _ _ (Just w)) = compile w


aNodeId (AnyNode w) = nodeId w
aNodeInners (AnyNode w) = nodeInners w
aInitialUniverse rc (AnyNode w) = initialUniverse rc w
aToUniverseData (AnyNode w) = toUniverseData w

type Const k = Node (ConstW k)
data ConstW k = (Datable k) => Const k
instance Watchable (ConstW k) where
  compile (Const _) = SimpleCompilation $ error "Const is confused"
  eval (Node _ _ (Just (Const v))) _ = (toData v, [])

type Struct = Node StructW
data StructW = Struct [(Text, AnyNode)]
instance Watchable StructW where
  compile (Struct _) = SimpleCompilation return

type List a = Node (ListW a)
data ListW a = forall b. (Datable b) => MapList (b -> a)
             | FilterList (a -> Bool)

instance (Datable a) => Watchable (ListW a) where
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
  evalValue _ = ListData []

type Dict k v = Node (DictW k v)
data DictW k v = forall elem. (v ~ List elem, Datable elem, UniverseDatable elem) 
               => ShuffleList Int (elem -> k)
               | forall v'. (v ~ Node v', Watchable v', UniverseDatable v')
               => MapDict Int        -- id of the Dict that gives us our context
                          (Node v')  -- actual result value, constructed by
                                     --  applying the map function to a tube being
                                     --  filled by the dict being mapped over

data DictKey k = forall v. (Datable k, Watchable v) =>
                 DictKey (Dict k (Node v))  -- map whose key we're looking up

data DictSlowKey k = forall k0 v. (Datable k0, Datable k, Watchable v) =>
                     DictSlowKey (Dict k0 (Node v)) (k0 -> k)

instance (Datable k, Watchable v) => Watchable (DictW k (Node v)) where
  compile (ShuffleList id f) = SimpleCompilation $ 
    \c@(Change cxt impulse) -> 
      addToChangeContext id (shufflef f impulse) c
    where shufflef f (ListImpulse (AddElement elem)) = trace ("shuffling " ++ show id ++  " " ++ show elem ++ " to " ++ show (toData $ f $ fromData elem)) $ 
                                                       toData $ f $ fromData elem
          shufflef f (ListImpulse (RemoveElement elem)) = toData $ f $ fromData elem

  compile (MapDict _ v) = SimpleCompilation $ return
  dictValId (Node id _ (Just (MapDict _ d))) = dictValId d
  dictValId node = nodeId node

dictMembersDefaultValue :: (Watchable v) => DictW k (Node v) -> (Node v)
dictMembersDefaultValue (ShuffleList _ _) = (Node (-1) [] Nothing)
dictMembersDefaultValue (MapDict _ d) = d

dictShuffler :: DictW k v -> Int
dictShuffler (ShuffleList id _) = id
dictShuffler (MapDict id _) = id

type DictLookup k v = Node (DictLookupW k)
data DictLookupW k = DictLookup (DictKey k) Int

instance Watchable (DictLookupW v) where
  compile (DictLookup (DictKey context) dictId) = SimpleCompilation go
    where go change@(Change cxt _) = trace ("DictLookup " ++ show contextId ++ " -> " ++ show dictId) $
                                     addToChangeContext contextId p change
            where p = fromJustNote ("DictLookup " ++ show contextId ++ "->" ++ show dictId ++ " stymied") $
                                     Map.lookup dictId cxt
                  contextId = dictShuffler $ nodeW context
  eval node@(Node _ ns (Just (DictLookup (DictKey context) dictId))) cxt
    = (error "no value dictlookup", concat [snd (eval n cxt')|(AnyNode n) <- ns])
    where cxt' = Map.insert contextId p cxt
          contextId = dictShuffler $ nodeW context
          p = fromJustNote ("DictLookup eval " ++ show contextId ++ "->" ++ show dictId ++ " stymied") $
              Map.lookup dictId cxt

type MSet a = Node (MSetW a)
data MSetW a = forall a' k. (a ~ Node a', Watchable a') =>
               DictValuesMSet Int (Dict k a)

instance Watchable (MSetW a) where
  compile (DictValuesMSet _ _) = SimpleCompilation return


type DictSlowLookup k = Node (DictSlowLookupW k)
data DictSlowLookupW k = forall v. (Watchable v, Datable k) => DictSlowLookup (DictSlowKey k) (Dict k (Node v)) 
instance Watchable (DictSlowLookupW k) where

  compile (DictSlowLookup key map)
    = DictLookupCompilation $ \(Change cxt _) ->
        let valId = dictValId map
            shufflerId = dictShuffler $ nodeW map
            outKey = dictSlowLookupOutKey key cxt
         in trace ("DictSlowLookup going to key " ++ show outKey ++ " at " ++ show (valId, shufflerId)) (valId, shufflerId, outKey)
  eval (Node id [AnyNode d] (Just (DictSlowLookup key map))) cxt
    = (v, watch:ws)
    where outKey = dictSlowLookupOutKey key cxt
          watch = Watch id cxt
                        (dictValId map) cxt'
          (v, ws) = eval d cxt'
          cxt' = (Map.insert (dictShuffler $ nodeW map) outKey cxt)

  nodeDependencies (Node _ ds (Just (DictSlowLookup _ map))) = (AnyNode map):ds
dictSlowLookupOutKey (DictSlowKey context f) cxt = toData $ f $ fromData inKey
  where contextId = dictShuffler $ nodeW context
        inKey = fromJustNote ("DictSlowLookup " ++ show contextId ++ " stymied in " ++ show cxt) $
                             Map.lookup contextId cxt


type Integer = Node IntegerW
data IntegerW = SumInteger
              | ProductInteger
              | ToReplaceInteger
              | IntegerReplaceToProduct
              | IntegerReplaceToSum

instance Watchable IntegerW where
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
    = StatefulCompilation $ \(Change cxt impulse) (IntegerData n) -> 
                            [Change cxt $ ReplaceImpulse $ replace impulse n]
    where replace (IntImpulse (AddInteger n')) n = IntegerData $ n' + n
          replace (IntImpulse (MultiplyInteger n')) n = IntegerData $ n' * n
  compile (IntegerReplaceToProduct)
    = StatefulCompilation $ \(Change cxt impulse) (IntegerData n) ->
                            [Change cxt $ prodf impulse n]
    where prodf (ReplaceImpulse (IntegerData 0)) oldn = ReplaceImpulse $ IntegerData 0
          prodf (ReplaceImpulse n) 0 = ReplaceImpulse n
          prodf (ReplaceImpulse (IntegerData n)) oldn
            = IntImpulse $ MultiplyIntegerF $ fromInteger n / fromInteger oldn
  compile (IntegerReplaceToSum)
    = StatefulCompilation $ \(Change cxt impulse) (IntegerData n) ->
                            [Change cxt $ prodf impulse n]
    where prodf (ReplaceImpulse (IntegerData 1)) oldn = ReplaceImpulse $ IntegerData 0
          prodf (ReplaceImpulse n) 1 = ReplaceImpulse n
          prodf (ReplaceImpulse (IntegerData n)) oldn
            = IntImpulse $ AddInteger $ fromInteger n - fromInteger oldn
  evalValue (Node _ ns (Just v)) = go v
    where go SumInteger = IntegerData 0
          go ProductInteger = IntegerData 1
          go IntegerReplaceToProduct = IntegerData 1
          go IntegerReplaceToSum = IntegerData 0
          go _ = case ns of
                   [AnyNode n] -> evalValue n



type Float = Node FloatW
data FloatW = SumFloat
            | ProductFloat
            | InvFloat
            | IntToFloat
            | FloatReplaceToSum
            | FloatReplaceToProduct
            | ToReplaceFloat

instance Watchable FloatW where
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
    = StatefulCompilation $ \(Change cxt impulse) (FloatData n) -> 
                            [Change cxt $ ReplaceImpulse $ replace impulse n]
    where replace (FloatImpulse (AddFloat n')) n = FloatData $ n' + n
          replace (FloatImpulse (MultiplyFloat n')) n = FloatData $ n' * n
          replace (ReplaceImpulse n) _ = n
  compile (FloatReplaceToProduct)
    = StatefulCompilation $ \(Change cxt impulse) (FloatData n) ->
                            [Change cxt $ prodf impulse n]
    where prodf (ReplaceImpulse (FloatData 0)) oldn = ReplaceImpulse $ FloatData 0
          prodf (ReplaceImpulse n) 0 = ReplaceImpulse n
          prodf (ReplaceImpulse (FloatData n)) oldn
            = FloatImpulse $ MultiplyFloat $ n / oldn
  compile (FloatReplaceToSum)
    = StatefulCompilation $ \(Change cxt impulse) (FloatData n) ->
                            [Change cxt $ prodf impulse n]
    where prodf ~(ReplaceImpulse n) 0 = ReplaceImpulse n
          prodf (ReplaceImpulse (FloatData n)) oldn
            = FloatImpulse $ AddFloat $ n - oldn
  evalValue (Node _ ns (Just v)) = go v
    where go SumFloat = FloatData 0
          go ProductFloat = FloatData 1
          go InvFloat = FloatData 1
          go FloatReplaceToProduct = FloatData 1
          go FloatReplaceToSum = FloatData 0
          go IntToFloat = case ns of
                            [AnyNode n] -> let (IntegerData d) = evalValue n
                                            in FloatData $ fromIntegral d
          go _ = case ns of
                   [AnyNode n] -> evalValue n

class UniverseDatable a where
  initialUniverse' :: Set.Set Int -> Node a -> Universe
  toUniverseData' :: Node a -> Universe -> UniverseData

initialUniverse :: UniverseDatable a => Set.Set Int -> Node a -> Universe
initialUniverse rc (Node _ (n:_) Nothing) = aInitialUniverse rc n
initialUniverse rc n = initialUniverse' rc n

toUniverseData :: UniverseDatable a => Node a -> Universe -> UniverseData
toUniverseData (Node _ (n:_) Nothing) = aToUniverseData n
toUniverseData n = toUniverseData' n

instance UniverseDatable StructW where
  initialUniverse' rc (Node id _ (Just (Struct elems))) = Map.unions $ map universeElem elems
    where universeElem (label, w) = aInitialUniverse rc w
  toUniverseData' (Node id inners (Just (Struct elems))) universe
    = UniverseStruct $ foldr addElem Map.empty elems
    where addElem (label, w) map = Map.insert label (aToUniverseData w universe) map

instance UniverseDatable (DictW k v) where
  initialUniverse' rc (Node id _ (Just (ShuffleList _ _)))
    = Map.singleton id (ListData [], Set.insert id rc, Map.empty)
  initialUniverse' rc (Node id _ (Just (MapDict shufflerId v)))
    = initialUniverse (Set.insert shufflerId rc) v

  toUniverseData' (Node id inners (Just dict)) universe
    = UniverseDict $ toUniverseDataDict (dictShuffler dict) dict universe

instance UniverseDatable (MSetW v) where
  toUniverseData' (Node _ _ (Just (DictValuesMSet id dict))) universe
    = UniverseList $ Map.elems $ toUniverseDataDict id (nodeW dict) universe

  initialUniverse' rc (Node id _ (Just (DictValuesMSet _ dict)))
    = initialUniverse rc dict 

toUniverseDataDict :: Int -> DictW k v -> Universe -> Map.Map Data UniverseData
toUniverseDataDict id dict universe = Set.foldr addKeyContents Map.empty allKeys
  where allKeys :: Set.Set Data
        allKeys = Map.foldr addKeysInStruct Set.empty universe
        addKeysInStruct :: UniverseSlice -> Set.Set Data -> Set.Set Data
        addKeysInStruct (_, _, struct) ks = Map.foldrWithKey (\cxt v ks -> addKeysInContext cxt ks) ks struct
        addKeysInContext :: Context -> Set.Set Data -> Set.Set Data
        addKeysInContext context ks = case Map.lookup id context of
                                        Just k -> Set.insert k ks
                                        Nothing -> ks
        addKeyContents :: Data -> Map.Map Data UniverseData -> Map.Map Data UniverseData
        addKeyContents k map = Map.insert k (keyContents dict k) map
        keyContents :: (DictW k v) -> Data -> UniverseData
        keyContents dict k = case dict of
                               (MapDict _ d)     -> toUniverseData d $ relevantUniverse k
                               (ShuffleList _ _) -> toUniverseData list $ relevantUniverse k
        list = (Node 0 [] Nothing) :: List v
        relevantUniverse :: Data -> Universe
        relevantUniverse k = Map.map (relevantUniverseSlice k) universe
        relevantUniverseSlice :: Data -> UniverseSlice -> UniverseSlice
        relevantUniverseSlice k (def, rc, universeSlice) = (def, rc, Map.filterWithKey (isKey k) universeSlice)
        isKey :: Data -> Context -> (Data, Set.Set (Int,Context)) -> Bool
        isKey k cxt _ = Map.lookup id cxt == Just k
          
instance UniverseDatable (ListW e) where
  toUniverseData' = toUniverseDataScalar
  initialUniverse' = initialUniverseScalar (ListData [])
instance UniverseDatable IntegerW where
  toUniverseData' = toUniverseDataScalar
  initialUniverse' rc n@(Node _ _ (Just i)) = initialUniverseScalar (go i) rc n
    where go SumInteger = IntegerData 0
          go ToReplaceInteger = IntegerData 0
          go IntegerReplaceToProduct = IntegerData 1
          go IntegerReplaceToSum = IntegerData 0
          go ProductInteger = IntegerData 1
instance UniverseDatable FloatW where
  toUniverseData' = toUniverseDataScalar
  initialUniverse' rc n@(Node _ [vs] Nothing) = aInitialUniverse rc vs
  initialUniverse' rc n@(Node _ _ (Just f)) = initialUniverseScalar (go f) rc n
    where go SumFloat = FloatData 0
          go ToReplaceFloat = FloatData 0
          go FloatReplaceToProduct = FloatData 1
          go FloatReplaceToSum = FloatData 0
          go ProductFloat = FloatData 1


toUniverseDataScalar :: Node a -> Universe -> UniverseData
toUniverseDataScalar (Node id _ _) universe
  = case Map.toList $ universeSliceValues universeSlice of
      [(k, (v, ws))] -> UniverseData v
      [] -> UniverseData $ universeSliceDefault universeSlice
      vws -> error $ "universe for scalar too big " ++ show id ++ ":\n" ++ unlines [show vw | vw <- vws]
  where universeSlice = fromJustNote ("no universe slice " ++ show id ++ " for scalar") $ 
                        Map.lookup id universe


initialUniverseScalar v rc node = Map.singleton id (v, rc, Map.empty)
  where id = nodeId node 

instance UniverseDatable (ConstW v) where
  toUniverseData' _ universe
    = UniverseData $ StringData "This is a constant"
  initialUniverse' _ _ = Map.empty
instance UniverseDatable (DictLookupW v) where
  toUniverseData' _ universe
    = UniverseData $ StringData "This is a dict lookup"
  initialUniverse' _ _ = Map.empty
instance UniverseDatable (DictSlowLookupW v) where
  toUniverseData' _ universe
    = UniverseData $ StringData "This is a slow dict lookup"
  initialUniverse' rc node = Map.empty

type Propagators = Map.Map Int [Int]
type Modifiers = Map.Map Int Compiled
type PropOrder = Map.Map Int Int
type Nodes = Map.Map Int AnyNode

fullCompile :: AnyNode -> (Nodes, Propagators, Modifiers, PropOrder)
fullCompile w = (compileNodes w,
                 compilePropagators w,
                 compileModifiers w,
                 aNodePropOrder w)

compileNodes :: AnyNode -> Nodes
compileNodes w = Map.insert (aNodeId w) w $ Map.unions (map compileNodes $ aNodeInners w)

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

mergeChanges :: (Nodes, Propagators, Modifiers, PropOrder) ->
                [(Int,Change)] ->
                [(Int,Change)] ->
                [(Int,Change)]
             
mergeChanges (_,_,_,propOrder) changes1 changes2
  = List.sortBy (compare `Data.Function.on` ((flip (Map.findWithDefault 0) propOrder) . fst)) $ changes1 ++ changes2

getNextChanges :: (Nodes, Propagators, Modifiers, PropOrder) ->
                      Change ->
                      Universe ->
                      Int ->
                      ([(Int,Change)],[Watch])
getNextChanges compiled@(_, propss, mods, _)
               change@(Change contextFromChange impulse)
               universe
               node
  = ([(prop, change) | prop <- props, change <- changes], watchers)
  where props = maybe [] id $ Map.lookup node propss
        mod = fromJustNote ("No modifier for " ++ show node) $ Map.lookup node mods
        (changes,watchers) = case mod of 
                               SimpleCompilation f -> 
                                 (f change,[])
                               StatefulCompilation f -> 
                                 trace ("STATEFUL " ++ show node ++ " on " ++ show stateValue) ((f change stateValue),[])
                               DictLookupCompilation f ->
                                 let (dictId,shufflerId,outKey) = f change
                                     context = Map.insert shufflerId outKey contextFromChange
                                     universeSlice = Map.lookup dictId universe
                                     justUniverseSlice = fromJustNote ("no universe slice at " ++ show dictId) $
                                                                      universeSlice
                                     (value, watchers) = universeSliceGet justUniverseSlice context
                                  in case isJust universeSlice && universeSliceAcceptsContext justUniverseSlice context of
                                       True  -> ([Change contextFromChange $ ReplaceImpulse value],
                                                 [Watch node contextFromChange
                                                        dictId context])
                                       False -> ([Change (Map.insert dictId outKey contextFromChange) impulse], [])
                                 
        stateValue = let msu = Map.lookup node universe
                         msu :: Maybe UniverseSlice
                         su = fromJustNote ("No universe for " ++ show node ++ 
                                                  " for " ++ show universe)
                                                  msu
                      in fst $ universeSliceGet su contextFromChange
applyChange compiled stateWatchable nodeWatchable stateValue impulse
  = applyChanges compiled
                 stateValue
                 [(nodeId nodeWatchable, Change Map.empty impulse)]

applyChanges compiled universe [] = universe
applyChanges compiled universe ((nodeId, change):changes)
  = trace (show nodeId ++ ":\ttaking " ++ show change ++
                               "\n        to     " ++
                                concat (List.intersperse "\n               "
                                                         [show c ++ " at " ++ show i | (i,c) <- newChanges])) $
    applyChanges compiled
                 (addWatches watchersFromChange universe')
                 (mergeChanges compiled changes $ newChanges ++ slowChanges)
  where (newChanges, watchersFromChange) = getNextChanges compiled change universe nodeId
        valueForNode = Map.lookup nodeId universe
        (universe', slowChanges) = case valueForNode of
          Just v -> let (v',cs) = applyLandingChange (snd $ head newChanges) v
                     in trace ("landing at " ++ show nodeId) $ (Map.insert nodeId v' universe, cs)
          Nothing -> (universe, [])
        addWatches [] universe = universe
        -- TODO: are watchedId and watchedContext always equal to nodeId and the context from the change?
        addWatches ((Watch watchingId watchingContext watchedId watchedContext):ws) universe
          = let (def, rc, su) = fromJustNote ("addWatch can't find universeSlice " ++ show watchedId) $
                                             Map.lookup watchedId universe
                reducedWatchedContext = requiredContextReduceContext rc watchedContext
                ((val, watchers), ws') = case Map.lookup reducedWatchedContext su of
                                           Just n -> (n, [])
                                           Nothing -> evalNode compiled watchedId watchedContext
                watchers' = Set.insert (watchingId, watchingContext) watchers
                su' = Map.insert reducedWatchedContext
                                 (val, watchers')
                                 su
             in addWatches (ws ++ ws') $ Map.insert watchedId (def, rc, su') universe

evalNode (nodes,_,_,_) nodeId context = ((val, Set.empty), watches)
  where aNode = fromJustNote ("Can't eval " ++ show nodeId) $ Map.lookup nodeId nodes
        (val, watches) = case aNode of
                           AnyNode node -> eval node context

applyLandingChange :: Change -> UniverseSlice -> (UniverseSlice, [(Int, Change)])
applyLandingChange (Change context impulse) (def, rc, vs)
  = ((def, rc, Map.insert reducedContext (newValue, ws) vs), 
     [(id, Change cxt impulse) | (id,cxt) <- Set.toList ws])
  where (currentValue,ws) = universeSliceGet (def, rc, vs) reducedContext
        newValue = applyImpulse impulse currentValue
        reducedContext = requiredContextReduceContext rc context

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

anyNode :: (Watchable a, PPrint a, UniverseDatable a) => Node a -> Func AnyNode
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

shuffle :: forall a k. (Datable a, Datable k, UniverseDatable a)
        => (a -> k) -> List a -> Func (Dict k (List a))
shuffle f l = do id <- getNextId
                 return $ Node id [AnyNode l] (Just $ ShuffleList id f)

mapDict :: forall k v0 v. (Datable k, Watchable v0, Watchable v, UniverseDatable v)
        => ((Node v0) -> Func (Node v)) -> Dict k (Node v0) -> Func (Dict k (Node v))
mapDict f = mapDictWithKey (\k v -> f v)

mapDictWithKey :: forall k v0 v. (Datable k, Watchable v0, Watchable v, UniverseDatable v)
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
                DictValuesMSet (dictShuffler dict) node

structLookup :: Watchable a => Text -> Struct -> Func (Node a)
structLookup key (Node id _ (Just (Struct elems))) = go elems
  where go [] = error $ "couldn't lookup " ++ show key ++ " in struct " ++ show id
        go ((label,node):elems) | label == key = mkTube [node]
                                | otherwise = go elems

dictLookup :: (Datable k, Watchable v) =>
               DictKey k ->
               Dict k (Node v) ->
               Func (Node v)
dictLookup key map
  = do lookup <- mkWatchable [AnyNode map] 
                             (DictLookup key
                                         (dictShuffler $ nodeW map))
       id <- getNextId
       return $ Node id [AnyNode lookup] Nothing -- make a tube so it can come out with the right type

dictSlowLookup :: (PPrint v, Datable k, Watchable v) =>
                  DictSlowKey k ->
                  Dict k (Node v) ->
                  Func (Node v)
dictSlowLookup key@(DictSlowKey context f) map
 = do lookup <- mkWatchable [AnyNode context]
                            (DictSlowLookup key map)
      id <- getNextId
      return $ Node id [AnyNode lookup] Nothing

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
struct elemTuples = do elems <- mapM elem elemTuples
                       mkWatchable (map snd elems) $ Struct elems
  where elem (label, value)
          = do v <- value
               return (label, v)

anyNodeEdges (AnyNode node) = nodeEdges node
nodeEdges :: forall a. Watchable a => Node a -> [Graph.Edge]
nodeEdges node = [(aNodeId i,nodeId node) | i <- nodeDependencies node] ++ 
                 (concatMap anyNodeEdges (nodeDependencies node))

nodeGraph :: forall a. Watchable a => Node a -> Graph.Graph
nodeGraph node = Graph.buildG (least,most) edges
  where edges = nodeEdges node
        allVertices = (map fst edges) ++ (map snd edges)
        least = minimum allVertices
        most = maximum allVertices
nodePropOrder :: forall a. Watchable a => Node a -> Map.Map Int Int
nodePropOrder = mkMap . Graph.topSort . nodeGraph
  where mkMap ids = Map.fromList $ zip ids [0..]
aNodePropOrder (AnyNode a) = nodePropOrder a

class PPrint a where
  pprint :: a -> String

instance PPrint (ConstW k) where
  pprint (Const _) = "Const"
instance PPrint StructW where
  pprint (Struct _) = "Struct"
instance PPrint (ListW a) where
  pprint (MapList _) = "MapList"
  pprint (FilterList _) = "FilterList"
instance PPrint (DictW k v) where
  pprint (ShuffleList _ _) = "ShuffleList"
  pprint (MapDict shufflerId _) = "MapDict(shufflerId=" ++ show shufflerId ++ ")"
instance PPrint (MSetW a) where
  pprint (DictValuesMSet _ _) = "DictValuesMSet"
instance PPrint (DictLookupW v) where
  pprint (DictLookup _ _) = "DictLookup"
instance PPrint (DictSlowLookupW v) where
  pprint (DictSlowLookup _ _) = "DictSlowLookup"
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

printUniverseData = go 0
  where go n (UniverseData d) = prefix n (show d)
        go n (UniverseList l) = prefix n "[\n" ++
                                concat (map (go (n+1)) l) ++
                                prefix n "]\n"
        go n (UniverseStruct m) = prefix n "{[\n" ++
                                  concat [ prefix (n+1) (show k ++ ":") ++ "\n" ++ 
                                           go (n+2) v ++ "\n"
                                         | (k,v) <- Map.toList m] ++
                                  prefix n "]}\n"
        go n (UniverseDict m) = prefix n "{\n" ++
                                concat [ prefix (n+1) (show k ++ ":") ++ "\n" ++ 
                                         go (n+2) v ++ "\n"
                                       | (k,v) <- Map.toList m] ++
                                prefix n "}\n"
        prefix :: Int -> String -> String
        prefix n s = replicate (2*n) ' ' ++ s
