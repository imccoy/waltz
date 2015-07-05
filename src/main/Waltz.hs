module Waltz where

import Prelude hiding (Integer)
import qualified Prelude as Prelude

import Control.Monad.State
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Text (Text)
import Safe

import qualified Debug.Trace as Trace

debugMode = True

trace = if debugMode then Trace.trace else (\x y -> y)

data Change = Change Context Impulse
  deriving (Show)

type Context = Map.Map Int PathElement

data Impulse = ListImpulse !ListImpulse
             | IntImpulse !IntImpulse
             | ReplaceImpulse !Data
  deriving (Show)

data ListImpulse = AddElement !Data
                 | RemoveElement !Data
  deriving (Show)

data IntImpulse = AddInteger !Prelude.Integer
                | MultiplyIntegerF !Prelude.Double
  deriving (Show)


data Data = ListData ![Data]
          | MapData !Int !Data !(Map.Map Data Data)
          | StructData !Int !(Map.Map Text Data)
          | IntegerData !Prelude.Integer
          | StringData !Text
  deriving (Eq, Ord)

instance Show Data where
  show x = showData x


showData (ListData xs) = show xs
showData (MapData _ _ m) = show m
showData (StructData _ m) = show m
showData (IntegerData i) = show i
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

instance Datable Text where
  toData s = StringData s
  fromData (StringData s) = s



data AnyNode = forall a. (Watchable a, PPrint a) => AnyNode !(Node a)

addToChangeContext node pathElement = go
  where
    go (Change cxt impulse) = let cxt' = Map.insert node pathElement cxt
                               in [Change cxt' impulse]

data PathElement = StructPath Text | MapPath Data
  deriving (Show, Eq)

data Compiled = SimpleCompilation (Change -> [Change])
              | StatefulCompilation (Change -> Data -> [Change])

class PPrint a => Watchable a where
  initialValue :: Int -> [AnyNode] -> a -> Data
  compile :: a -> Compiled
  watchablePaths :: a -> [(Lookup, Maybe AnyNode)]
  watchablePaths _ = []

data Node a = Node !Int [AnyNode] (Maybe a)

data Lookup = LookupMap Int | LookupStruct Text
  deriving (Show)



nodeId (Node id _ _) = id
nodeInners (Node _ inners _) = inners
nodeW (Node _ _ (Just a)) = a

nodeInitialValue (Node id inners (Just w)) = initialValue id inners w

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
  watchablePaths (Struct elems) = concatMap (watchablePaths . nodeW) elems

type StructElem = Node StructElemW
data StructElemW = StructElem Int Text AnyNode

instance Watchable StructElemW where
  initialValue _ [w] (StructElem _ _ _) = aNodeInitialValue w
  compile (StructElem structId label _) = SimpleCompilation $
                                            addToChangeContext structId
                                                               (StructPath label)
  watchablePaths (StructElem _ label value) = [(LookupStruct label, Just value)]

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

data DictKey k = DictKey Int  -- the id of the (shuffled) map whose value we
                              -- we are looking up

instance (Datable k, Watchable v) => Watchable (DictW k (Node v)) where
  initialValue id inners map = MapData inner
                                       (dictMembersDefaultValue map)
                                       Map.empty
    where
      inner = dictShuffler map
  
  compile (ShuffleList id f) = SimpleCompilation $ 
    \c@(Change cxt impulse) -> 
      addToChangeContext id (MapPath $ shufflef f impulse) c
    where shufflef f (ListImpulse (AddElement elem)) = toData $ f $ fromData elem
          shufflef f (ListImpulse (RemoveElement elem)) = toData $ f $ fromData elem

  compile (MapDict _ _ v) = SimpleCompilation $ return
  watchablePaths (ShuffleList id _) = [(LookupMap id, Nothing)]
  watchablePaths (MapDict id _ v) = [(LookupMap id, Just $ AnyNode v)]

dictMembersDefaultValue (ShuffleList _ _) = ListData []
dictMembersDefaultValue (MapDict _ d _) = d

dictShuffler :: DictW k v -> Int
dictShuffler (ShuffleList id _) = id
dictShuffler (MapDict id _ _) = id

type DictLookup k v = Node (DictLookupW k)
data DictLookupW k = DictLookup (DictKey k) Int Data

instance Watchable (DictLookupW v) where
  initialValue _ _ (DictLookup (DictKey _) _ def) = def
  compile (DictLookup (DictKey contextId) dictId _) = SimpleCompilation go
    where go change@(Change cxt _) = trace ("picked up a " ++ show p ++ " from " ++ show contextId ++ " for " ++ show dictId) $ 
                                     addToChangeContext contextId p change
            where p = fromJustNote ("DictLookup " ++ show contextId ++ "->" ++ show dictId ++ " stymied") $
                                     Map.lookup dictId cxt

type MSet a = Node (MSetW a)
data MSetW a = DictValuesMSet Int Data

instance Watchable (MSetW a) where
  initialValue _ _ (DictValuesMSet id d) = MapData id d Map.empty
  compile (DictValuesMSet _ _) = SimpleCompilation return


type Integer = Node IntegerW
data IntegerW = SumInteger
              | ProductInteger
              | SumToReplace 
              | ReplaceToProduct

instance Watchable IntegerW where
  initialValue id _ (SumInteger) = IntegerData 0
  initialValue id _ (SumToReplace) = IntegerData 0
  initialValue id _ (ReplaceToProduct) = IntegerData 1
  initialValue id _ (ProductInteger) = IntegerData 1
  compile (SumInteger) 
    = SimpleCompilation $ \(Change cxt impulse) -> 
                            [Change cxt (sumf impulse)]
    where sumf (ListImpulse (AddElement (IntegerData d))) = IntImpulse $ AddInteger d
  compile (ProductInteger) 
    = SimpleCompilation return
  compile (SumToReplace)
    = StatefulCompilation $ \(Change cxt impulse) (IntegerData n) -> 
                              [Change cxt $ ReplaceImpulse $ replace impulse n]
    where replace (IntImpulse (AddInteger n')) n = IntegerData $ n' + n
  compile (ReplaceToProduct)
    = StatefulCompilation $ \(Change cxt impulse) (IntegerData n) ->
                              [Change cxt $ prodf impulse n]
    where prodf (ReplaceImpulse (IntegerData 0)) oldn = ReplaceImpulse $ IntegerData 0
          prodf (ReplaceImpulse n) 0 = ReplaceImpulse n
          prodf (ReplaceImpulse (IntegerData n)) oldn
            = IntImpulse $ MultiplyIntegerF $ fromInteger n / fromInteger oldn

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
               |(l,n) <- watchablePaths $ nodeW w]

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
getLandingChanges' compiled@(landingSite, propss, mods, paths) change stateValue node
  = landing ++ (concat [ getLandingChanges' compiled c stateValue l
                       | l <- trace (show node ++ ": jumping to " ++ show props) props,
                         c <- trace (show node ++ ": transforming " ++ show change) $
                              trace (show node ++ ": to " ++ show changes) $
                                    changes
                       ])
  where props = maybe [] id $ Map.lookup node propss
        mod = fromJustNote ("No modifier for " ++ show node) $ Map.lookup node mods
        (Change contextFromChange _) = change
        changes = case mod of 
                    SimpleCompilation f -> f change 
                    StatefulCompilation f -> let mp = Map.lookup node paths
                                                 p = fromJustNote ("No path for " ++ show p) mp
                                                 v = lookupByPath p contextFromChange stateValue
                                              in f change v
        landing = if node == landingSite then changes else []

lookupByPath [] _ v = v
lookupByPath ((LookupMap k):p) ctx (MapData id d m)
  = lookupByPath p ctx v
  where ctxElement = fromJustNote ("No " ++ show k ++ 
                                    " in context when doing path lookup") $
                                  Map.lookup k ctx
        ctxPath = case ctxElement of
                    MapPath v -> v
                    _ -> error "Got structpath when needed mappath"
        v = fromJustDef d $ Map.lookup ctxPath m
lookupByPath ((LookupStruct t):p) ctx (StructData _ m)
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

applyLandingChange (Change context impulse) (MapData id def map)
  = MapData id def $ Map.alter go
                               p
                               map
  where pElem = fromJustNote ("can't find context for map " ++ show id) $
                             Map.lookup id context
        (MapPath p) = pElem
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

sumList :: List Prelude.Integer -> Func Integer
sumList ns = mkWatchable [AnyNode ns] SumInteger

productList :: MSet Integer -> Func Integer
productList ns = mkWatchable [AnyNode ns] ProductInteger

sumToReplace :: Integer -> Func Integer
sumToReplace n = mkWatchable [AnyNode n] SumToReplace

replaceToProduct :: Integer -> Func Integer
replaceToProduct n = mkWatchable [AnyNode n] ReplaceToProduct

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
                        output <- f (DictKey context) funnel
                        let def = nodeInitialValue output
                        mkWatchable [AnyNode output]
                                    (MapDict context def output)
      where   
            context :: Int
            context = dictShuffler (nodeW d)


dictLookup :: (Datable k, Watchable v) =>
               DictKey k ->
               Dict k (Node v) ->
               Func (DictLookup k v)
dictLookup key map = mkWatchable [AnyNode map] 
                                 (DictLookup key
                                             (dictShuffler $ nodeW map)
                                             (dictMembersDefaultValue $ nodeW map))


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
  pprint (MapDict _ _ _) = "MapDict"
instance PPrint (MSetW a) where
  pprint (DictValuesMSet _ _) = "DictValuesMSet"
instance PPrint (DictLookupW v) where
  pprint (DictLookup _ _ _) = "DictLookup"
instance PPrint (IntegerW) where
  pprint (SumInteger) = "SumInteger"
  pprint (ProductInteger) = "ProductInteger"
  pprint (SumToReplace) = "SumToReplace"
  pprint (ReplaceToProduct) = "ReplaceToProduct"

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
