module Waltz where

import Prelude hiding (Integer, Float)
import qualified Prelude as Prelude

import Control.Monad.State
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
  deriving (Show)

data FloatImpulse = AddFloat !Prelude.Double
                  | MultiplyFloat !Prelude.Double
  deriving (Show)

data Data = ListData ![Data]
          | MapData !Int -- the id of the map
                    !Int -- the id of the relevant shuffler
                    !Data -- default value
                    !(Map.Map Data (Set.Set (Int, Context))) -- watchers
                    !(Map.Map Data Data) -- actual data
          | StructData !Int !(Map.Map Text Data)
          | IntegerData !Prelude.Integer
          | FloatData !Prelude.Double
          | StringData !Text
  deriving (Eq, Ord)

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
              | TargetedCompilation (Maybe Int) (Change -> Data -> [(Int, Change)])

class PPrint a => Watchable a where
  initialValue :: Int -> [AnyNode] -> a -> Data
  compile :: a -> Compiled
  watchablePaths :: Int -> a -> [(Lookup, Maybe AnyNode)]
  watchablePaths _ _ = []

data Node a = Node !Int [AnyNode] (Maybe a)

data Lookup = LookupMap Int Int | LookupStruct Int Text
  deriving (Show)



nodeId (Node id _ _) = id
nodeInners (Node _ inners _) = inners
nodeW (Node _ _ (Just a)) = a

nodeInitialValue :: Watchable a => Node a -> Data
nodeInitialValue (Node id inners (Just w)) = initialValue id inners w
nodeInitialValue (Node id [inner] Nothing) = aNodeInitialValue inner

nodeCompile (Node _ _ Nothing) = SimpleCompilation $ return
nodeCompile (Node _ _ (Just w)) = compile w


aNodeId (AnyNode w) = nodeId w
aNodeInners (AnyNode w) = nodeInners w
aNodeInitialValue (AnyNode w) = nodeInitialValue w

type Struct = Node StructW
data StructW = Struct [StructElem]
instance Watchable StructW where
  initialValue id _ (Struct elems) = StructData id $ foldr addElem Map.empty elems
    where addElem :: StructElem -> (Map.Map Text Data) -> (Map.Map Text Data)
          addElem elem@(Node _ _ (Just (StructElem _ key _))) map
             = Map.insert key (nodeInitialValue elem) map
  compile (Struct _) = SimpleCompilation return
  watchablePaths structId (Struct elems) = concatMap (watchablePaths structId . nodeW) elems

type StructElem = Node StructElemW
data StructElemW = StructElem Int Text AnyNode

instance Watchable StructElemW where
  initialValue _ [w] (StructElem _ _ _) = aNodeInitialValue w
  compile (StructElem structId label _) = SimpleCompilation $
                                            addToChangeContext structId
                                                               (StructPath label)
  watchablePaths structId (StructElem _ label value) = [(LookupStruct structId label, Just value)]

type List a = Node (ListW a)
data ListW a = forall b. (Datable b) => MapList (b -> a)
             | FilterList (a -> Bool)

instance (Datable a) => Watchable (ListW a) where
  initialValue _ _ _ = ListData []

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
                          Data       -- default value in result
                          (Node v')  -- actual result value, constructed by
                                     --  applying the map function to a tube being
                                     --  filled by the dict being mapped over

data DictKey k = forall v. (Datable k, Watchable v) => DictKey (Dict k (Node v))  -- map whose key we're looking up

data DictSlowKey k = forall k0 v. (Datable k0, Datable k, Watchable v) => DictSlowKey (Dict k0 (Node v)) (k0 -> k)

instance (Datable k, Watchable v) => Watchable (DictW k (Node v)) where
  initialValue id inners map = MapData id
                                       inner
                                       (dictMembersDefaultValue map)
                                       Map.empty
                                       Map.empty
    where
      inner = dictShuffler map
  
  compile (ShuffleList id f) = SimpleCompilation $ 
    \c@(Change cxt impulse) -> 
      addToChangeContext id (MapPath $ shufflef f impulse) c
    where shufflef f (ListImpulse (AddElement elem)) = trace ("shuffling " ++ show id ++  " " ++ show elem ++ " to " ++ show (toData $ f $ fromData elem)) $ toData $ f $ fromData elem
          shufflef f (ListImpulse (RemoveElement elem)) = toData $ f $ fromData elem

  compile (MapDict _ _ v) = SimpleCompilation $ return
  watchablePaths mapId (ShuffleList id _) = [(LookupMap mapId id, Nothing)]
  watchablePaths mapId (MapDict id _ v) = [(LookupMap mapId id, Just $ AnyNode v)]

dictMembersDefaultValue (ShuffleList _ _) = ListData []
dictMembersDefaultValue (MapDict _ d _) = d

dictShuffler :: DictW k v -> Int
dictShuffler (ShuffleList id _) = id
dictShuffler (MapDict id _ _) = id

type DictLookup k v = Node (DictLookupW k)
data DictLookupW k = DictLookup (DictKey k) Int Data

instance Watchable (DictLookupW v) where
  initialValue _ _ (DictLookup (DictKey _) _ def) = def
  compile (DictLookup (DictKey context) dictId _) = SimpleCompilation go
    where go change@(Change cxt _) = trace ("DictLookup " ++ show contextId ++ " -> " ++ show dictId) $
                                     addToChangeContext contextId p change
            where p = fromJustNote ("DictLookup " ++ show contextId ++ "->" ++ show dictId ++ " stymied") $
                                     Map.lookup dictId cxt
                  contextId = dictShuffler $ nodeW context

type MSet a = Node (MSetW a)
data MSetW a = DictValuesMSet Int Data

instance Watchable (MSetW a) where
  initialValue id _ (DictValuesMSet shufflerId d) = MapData id shufflerId d Map.empty Map.empty
  compile (DictValuesMSet _ _) = SimpleCompilation return


type DictSlowLookup k = Node (DictSlowLookupW k)
data DictSlowLookupW k = DictSlowLookup (DictSlowKey k) Int Int Data

instance Watchable (DictSlowLookupW v) where
  initialValue _ _ (DictSlowLookup (DictSlowKey _ _) _ _ def) = def
  compile (DictSlowLookup (DictSlowKey context f) dictId shufflerId _)
    = StatefulCompilation (Just dictId) $ \(Change cxt _) (MapData _ _ def _ map) ->
        let contextId = dictShuffler $ nodeW context
            inKeyElt = fromJustNote ("DictSlowLookup " ++ show contextId ++ "->" ++ show (dictId, shufflerId) ++ " styimed in " ++ show cxt) $
                                    Map.lookup contextId cxt
            (MapPath inKey) = inKeyElt
            outKey = toData $ f $ fromData inKey
            value = fromJustDef def $ Map.lookup outKey map
         in [Change cxt (ReplaceImpulse value),
             AddWatcher dictId outKey cxt]

type DictSlowLookupPropagator = Node DictSlowLookupPropagatorW
data DictSlowLookupPropagatorW = DictSlowLookupPropagator Int

instance Watchable DictSlowLookupPropagatorW where
  initialValue _ _ _ = error "DictSlowLookupPropagator initialValue"
  compile (DictSlowLookupPropagator dictId)
    = TargetedCompilation (Just dictId) $ \(Change cxt impulse) (MapData _ shufflerId _ watcherMap _) ->
      let (MapPath shuffleKey) = fromJustNote ("DictSlowLookupPropagator failed lookup") $
                                              Map.lookup shufflerId cxt
          watchers = fromJustDef Set.empty $ Map.lookup shuffleKey watcherMap
       in [(i,(Change (Map.union c cxt) impulse)) | (i,c) <- Set.toList watchers]

type Integer = Node IntegerW
data IntegerW = SumInteger
              | ProductInteger
              | SumToReplaceInteger
              | ReplaceToProduct

instance Watchable IntegerW where
  initialValue id _ (SumInteger) = IntegerData 0
  initialValue id _ (SumToReplaceInteger) = IntegerData 0
  initialValue id _ (ReplaceToProduct) = IntegerData 1
  initialValue id _ (ProductInteger) = IntegerData 1
  compile (SumInteger) 
    = SimpleCompilation $ \(Change cxt impulse) -> 
                            [Change cxt (sumf impulse)]
    where sumf (ListImpulse (AddElement (IntegerData d))) = IntImpulse $ AddInteger d
  compile (ProductInteger) 
    = SimpleCompilation $ \(Change cxt impulse) -> case impulse of
                            ReplaceImpulse (IntegerData n) -> [Change cxt (IntImpulse (MultiplyIntegerF (fromIntegral n)))]
                            otherwise -> [Change cxt impulse]
  compile (SumToReplaceInteger)
    = StatefulCompilation Nothing $
                          \(Change cxt impulse) (IntegerData n) -> 
                            [Change cxt $ ReplaceImpulse $ replace impulse n]
    where replace (IntImpulse (AddInteger n')) n = IntegerData $ n' + n
  compile (ReplaceToProduct)
    = StatefulCompilation Nothing $
                          \(Change cxt impulse) (IntegerData n) ->
                            [Change cxt $ prodf impulse n]
    where prodf (ReplaceImpulse (IntegerData 0)) oldn = ReplaceImpulse $ IntegerData 0
          prodf (ReplaceImpulse n) 0 = ReplaceImpulse n
          prodf (ReplaceImpulse (IntegerData n)) oldn
            = IntImpulse $ MultiplyIntegerF $ fromInteger n / fromInteger oldn

type Float = Node FloatW
data FloatW = SumFloat
            | ProductFloat
            | InvFloat
            | IntToFloat
            | SumToReplaceFloat

instance Watchable FloatW where
  initialValue id _ (SumFloat) = FloatData 0
  initialValue id _ (SumToReplaceFloat) = FloatData 0
  initialValue id _ (ProductFloat) = FloatData 1
  initialValue id _ (InvFloat) = FloatData 1
  initialValue id [node] (IntToFloat) = case aNodeInitialValue node of
                                          IntegerData n -> FloatData $ fromIntegral n
                                          otherwise     -> FloatData 1 --- TODO: fix this
  compile (SumFloat) 
    = SimpleCompilation $ \(Change cxt impulse) -> 
                            [Change cxt (sumf impulse)]
    where sumf (ListImpulse (AddElement (FloatData d))) = FloatImpulse $ AddFloat d
  compile (ProductFloat) 
    = SimpleCompilation $ \(Change cxt impulse) -> case impulse of
                            ReplaceImpulse (FloatData n) -> [Change cxt (FloatImpulse (MultiplyFloat n))]
                            otherwise -> [Change cxt impulse]
  compile (InvFloat)
    = SimpleCompilation $ \(Change cxt impulse) -> 
                            [Change cxt (invf impulse)]
    where invf (FloatImpulse (MultiplyFloat f)) = FloatImpulse $ MultiplyFloat (1 / f)
  compile (IntToFloat)
    = SimpleCompilation $ \(Change cxt impulse) ->
                            [Change cxt (toFf impulse)]
    where toFf (IntImpulse (MultiplyIntegerF f)) = FloatImpulse $ MultiplyFloat f
          toFf (IntImpulse (AddInteger f)) = FloatImpulse $ AddFloat $ fromInteger f
  compile (SumToReplaceFloat)
    = StatefulCompilation Nothing $
                          \(Change cxt impulse) (FloatData n) -> 
                            [Change cxt $ ReplaceImpulse $ replace impulse n]
    where replace (FloatImpulse (AddFloat n')) n = FloatData $ n' + n


type LandingSite = Int
type Propagators = Map.Map Int [Int]
type Modifiers = Map.Map Int Compiled
type LookupPaths = Map.Map Int [Lookup]

fullCompile :: AnyNode -> (LandingSite, Propagators, Modifiers, LookupPaths)
fullCompile w = (aNodeId w,
                 compilePropagators w,
                 compileModifiers w,
                 compileLookupPaths w)

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

getLandingChanges :: (LandingSite, Propagators, Modifiers, LookupPaths) -> 
                     Impulse ->
                     Data -> 
                     Int -> 
                     [Change]
getLandingChanges compiled imp stateValue node
  = getLandingChanges' compiled change stateValue node
  where change = Change Map.empty imp

getLandingChanges' :: (LandingSite, Propagators, Modifiers, LookupPaths) ->
                      Change ->
                      Data ->
                      Int ->
                      [Change]
getLandingChanges' compiled@(landingSite, propss, mods, paths)
                   change@(Change contextFromChange _)
                   stateValue
                   node
  = landing ++ 
    (concat [ getLandingChanges' compiled c stateValue l
            | l <- trace (show node ++ ": jumping to " ++ show props) props,
              c <- trace (show node ++ ": transforming " ++ show change) $
                   trace (show node ++ ": to " ++ show hereChanges) $
                         hereChanges
            ]) ++
    (concat [getLandingChanges' compiled c stateValue l
            |(l,c) <- elsewhereChanges])
  where props = maybe [] id $ Map.lookup node propss
        mod = fromJustNote ("No modifier for " ++ show node) $ Map.lookup node mods
        locatedChanges = case mod of 
                           SimpleCompilation f -> 
                             [(node, c) | c <- f change]
                           StatefulCompilation stateId f -> 
                             [(node, c) | c <- f change (stateValueAt stateId)]
                           TargetedCompilation stateId f ->
                             f change (stateValueAt stateId)
        hereChanges      = [c      | (l, c) <- locatedChanges, l == node]
        elsewhereChanges = [(l, c) | (l, c) <- locatedChanges, l /= node]
                             
        stateValueAt stateId = let i = fromJustDef node stateId
                                   mp = Map.lookup i paths
                                   p = fromJustNote ("No path for " ++ show i ++ 
                                                     " for " ++ show paths)
                                                    mp
                                in lookupByPath p contextFromChange stateValue


        landing = if node == landingSite then hereChanges else []
getLandingChanges' (_, _, _, paths)
                   change@(AddWatcher nodeToWatch keyToWatch watchingContext)
                   stateValue
                   watchingNode
  = [Change (Map.insert nodeToWatch 
                       (MapPath keyToWatch)
                       (addPathToContext p watchingContext))
            (AddWatcherImpulse nodeToWatch
                               watchingNode
                               keyToWatch
                               watchingContext)]
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
       
lookupByPath [] _ v = v
lookupByPath ((LookupMap _ k):p) ctx (MapData _ _ d _ m)
  = lookupByPath p ctx v
  where ctxElement = fromJustNote ("No " ++ show k ++ 
                                    " in context when doing path lookup") $
                                  Map.lookup k ctx
        ctxPath = case ctxElement of
                    MapPath v -> v
                    _ -> error "Got structpath when needed mappath"
        v = fromJustDef d $ Map.lookup ctxPath m
lookupByPath ((LookupStruct _ t):p) ctx (StructData _ m)
  = lookupByPath p ctx v
  where v = fromJustNote ("No " ++ show t ++ 
                          " in context when doing path lookup") $ 
                         Map.lookup t m

applyChange compiled stateWatchable nodeWatchable stateValue impulse
  = let landingChanges = getLandingChanges compiled impulse stateValue (nodeId nodeWatchable)
     in applyChanges stateWatchable landingChanges stateValue

applyChanges stateWatchable changes stateValue
  = foldr (\c s -> let result = applyLandingChange c s
                    in trace ("applying change " ++ show c ++ 
                              "\n  to state " ++ show s ++ 
                              "\n  yielding " ++ show result) $
                       applyLandingChange c s)
          stateValue changes

applyLandingChange (Change context impulse) mapData@(MapData id shufflerId def watchers map)
  = case impulse of
      (AddWatcherImpulse mapToWatchId _ _ _) ->
        if trace ("checking addWatcherImpulse " ++ show (mapToWatchId, id)) $ mapToWatchId == id
          then applyImpulse impulse mapData
          else recurse
      otherwise ->
        recurse
  where pElem = fromJustNote ("can't find context for map " ++ show shufflerId ++ " in " ++ show context ++ " for " ++ show impulse) $
                             Map.lookup shufflerId context
        (MapPath p) = pElem
        recurse = MapData id shufflerId def watchers $ Map.alter go
                                                                 p
                                                                 map
        go = Just . applyLandingChange (Change context impulse) . fromJustDef def
applyLandingChange (Change context impulse) (StructData id struct)
  = StructData id  $ Map.alter (fmap (applyLandingChange $ Change context impulse))
                               p
                               struct
  where pElem = fromJustNote ("can't find context for map " ++ show id) $
                             Map.lookup id context
        (StructPath p) = pElem
applyLandingChange (Change context impulse) value = applyImpulse impulse value

applyImpulse (ReplaceImpulse d) _ = d
applyImpulse (ListImpulse impulse) (ListData value) = ListData $ go impulse value
  where go (AddElement elem) elems = elem:elems
        go (RemoveElement elem) elems = List.delete elem elems
applyImpulse (IntImpulse impulse) (IntegerData value) = IntegerData $ go impulse value
  where go (AddInteger m) n = m + n
        go (MultiplyIntegerF m) n = round $ m * (fromInteger n)
applyImpulse (FloatImpulse impulse) (FloatData value) = FloatData $ go impulse value
  where go (AddFloat m) n = m + n
        go (MultiplyFloat m) n = m * n
applyImpulse (AddWatcherImpulse nodeToWatch watchId key context) (MapData id shufflerId def watchers map)
  = MapData id shufflerId def newWatchers map
  where newWatchers = Map.alter go key watchers
        elt = (watchId, context)
        go Nothing = Just $ Set.singleton elt
        go (Just s) = Just $ Set.insert elt s
applyImpulse impulse value = error $ "Can't apply impulse " ++ show impulse ++ " to " ++ show value

type Func = State Int

mkWatchable :: forall w. (Watchable w) => [AnyNode] -> w -> Func (Node w)
mkWatchable inners watchable = do id <- getNextId
                                  return $ Node id inners (Just watchable)
getNextId :: Func Int
getNextId = do i <- get
               let i' = i + 1
               i' `seq` put i'
               return i

-- precondition: ns only receive add changes
sumList :: List Prelude.Integer -> Func Integer
sumList ns = mkWatchable [AnyNode ns] SumInteger

-- precondition: ns only receive multiply changes
productMSet :: MSet Integer -> Func Integer
productMSet ns = mkWatchable [AnyNode ns] ProductInteger

sumToReplace :: Integer -> Func Integer
sumToReplace n = mkWatchable [AnyNode n] SumToReplaceInteger

replaceToProduct :: Integer -> Func Integer
replaceToProduct n = mkWatchable [AnyNode n] ReplaceToProduct

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

dictValues :: (Datable k, Watchable v) => Dict k (Node v) -> Func (MSet (Node v))
dictValues node@(Node _ _ (Just dict))
  = mkWatchable [AnyNode node] $
                DictValuesMSet (dictShuffler dict)
                               (dictMembersDefaultValue dict)

shuffle :: forall a k. (Datable a, Datable k)
        => (a -> k) -> List a -> Func (Dict k (List a))
shuffle f l = do id <- getNextId
                 return $ Node id [AnyNode l] (Just $ ShuffleList id f)

mapDict :: forall k v0 v. (Datable k, Watchable v0, Watchable v)
        => ((Node v0) -> Func (Node v)) -> Dict k (Node v0) -> Func (Dict k (Node v))
mapDict f = mapDictWithKey (\k v -> f v)

mapDictWithKey :: forall k v0 v. (Datable k, Watchable v0, Watchable v)
               => (DictKey k -> Node v0 -> Func (Node v)) -> Dict k (Node v0) -> Func (Dict k (Node v))
mapDictWithKey f d = do funnelId <- getNextId
                        let funnel = Node funnelId [AnyNode d] Nothing
                        output <- f (DictKey d) funnel
                        let def = nodeInitialValue output
                        result <- mkWatchable [AnyNode output]
                                              (MapDict context def output)
                        return result
      where context :: Int
            context = dictShuffler (nodeW d)


dictLookup :: (Datable k, Watchable v) =>
               DictKey k ->
               Dict k (Node v) ->
               Func (Node v)
dictLookup key map
  = do lookup <- mkWatchable [AnyNode map] 
                             (DictLookup key
                                         (dictShuffler $ nodeW map)
                                         (dictMembersDefaultValue $ nodeW map))
       id <- getNextId
       return $ Node id [AnyNode lookup] Nothing

dictSlowLookup :: (PPrint v, Datable k, Watchable v) =>
                  DictSlowKey k ->
                  Dict k (Node v) ->
                  Func (Node v)
dictSlowLookup key@(DictSlowKey context f) map
 = do lookup <- mkWatchable [AnyNode context]
                            (DictSlowLookup key
                                            (nodeId map)
                                            (dictShuffler $ nodeW map)
                                            (dictMembersDefaultValue $ nodeW map))
      escaper <- mkWatchable [AnyNode map]
                             (DictSlowLookupPropagator (nodeId map))
      id <- getNextId
      return $ Node id [AnyNode lookup,AnyNode escaper] Nothing

dictSlowKey :: (Datable k, Datable k') => DictKey k -> (k -> k') -> DictSlowKey k'
dictSlowKey (DictKey n) f = DictSlowKey n f

mapSlowKey :: (Datable k, Datable k') => DictSlowKey k -> (k -> k') -> DictSlowKey k'
mapSlowKey (DictSlowKey n f1) f2 = DictSlowKey n (f2 . f1)

inputList :: Func (List a)
inputList = do id <- getNextId
               return $ Node id [] Nothing

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

class PPrint a where
  pprint :: a -> String

instance PPrint StructW where
  pprint (Struct _) = "Struct"
instance PPrint StructElemW where
  pprint (StructElem _ text _) = show text
instance PPrint (ListW a) where
  pprint (MapList _) = "MapList"
  pprint (FilterList _) = "FilterList"
instance PPrint (DictW k v) where
  pprint (ShuffleList _ _) = "ShuffleList"
  pprint (MapDict shufflerId _ _) = "MapDict(shufflerId=" ++ show shufflerId ++ ")"
instance PPrint (MSetW a) where
  pprint (DictValuesMSet _ _) = "DictValuesMSet"
instance PPrint (DictLookupW v) where
  pprint (DictLookup _ _ _) = "DictLookup"
instance PPrint (DictSlowLookupW v) where
  pprint (DictSlowLookup _ _ _ _) = "DictSlowLookup"
instance PPrint (DictSlowLookupPropagatorW) where
  pprint (DictSlowLookupPropagator _) = "DictSlowLookupPropagator"
instance PPrint (IntegerW) where
  pprint (SumInteger) = "SumInteger"
  pprint (ProductInteger) = "ProductInteger"
  pprint (SumToReplaceInteger) = "SumToReplaceInteger"
  pprint (ReplaceToProduct) = "ReplaceToProduct"
instance PPrint (FloatW) where
  pprint (SumFloat) = "SumFloat"
  pprint (ProductFloat) = "ProductFloat"
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
