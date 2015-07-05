import qualified Waltz as W
import Waltz (Data (..), Datable (..))
import Control.Monad.State
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Set as Set 

data Link = Link Url Url
linkFrom (Link from _) = from
linkTo (Link _ to) = to

instance Datable Link where
  toData (Link from to) = ListData [StringData "Link", toData from, toData to]
  fromData (ListData [StringData "Link", from, to]) = Link (fromData from) (fromData to)
  fromData e = error $ "Can't fromData event " ++ show e

instance W.UniverseDatable Link where
  toUniverseData' = W.toUniverseDataScalar
  initialUniverse' = error "can't initialUniverse a link"

type Url = Text
type InLinks = W.MSet Url
type OutDegree = W.Integer
type Score = W.Float
pageRankIteration :: W.Dict Url (W.List Link) ->
                     W.Dict Url OutDegree -> 
                     W.Dict Url Score ->
                     W.Func (W.Dict Url Score, W.Struct)
pageRankIteration web outdegrees scores
  = do let outScore k s = do d <- W.dictLookup k outdegrees
                             d' <- W.intToFloat d
                             s `W.divide` d'
       outScores <- W.mapDictWithKey outScore scores
       let inScore inLink _ = W.dictLookup inLink outScores
       let score k inlinks = do dict <- W.shuffle linkFrom inlinks
                                scoresDict <- W.mapDictWithKey inScore dict
                                scoresDictAsReplaces <- W.mapDict W.floatToReplace scoresDict
                                scoresDictAsSums <- W.mapDict W.floatReplaceToSum scoresDictAsReplaces
                                scoreAsSum <- W.sumMSet =<< W.dictValues scoresDictAsSums
                                scoreAsReplace <- W.floatToReplace scoreAsSum
                                score <- W.floatReplaceToProduct scoreAsReplace
                                W.struct [("scoresDict", W.anyNode scoresDict),
                                          ("scoresDictAsReplaces", W.anyNode scoresDictAsReplaces),
                                          ("scoresDictAsSums", W.anyNode scoresDictAsSums),
                                          ("scoreAsSum", W.anyNode scoreAsSum),
                                          ("scoreAsReplace", W.anyNode scoreAsReplace),
                                          ("score", W.anyNode score)]
       scoreStructs <- W.mapDictWithKey score web
       scores <- W.mapDict (W.structLookup "score") scoreStructs
       retstuff <- W.struct [("scores",W.anyNode scoreStructs),
                             ("outScores'", W.anyNode outScores)]
       return (scores, retstuff)

--       scoresDicts <- W.mapDict (\inlinks -> W.mapDictWithKey inScore =<<
--                                                   W.shuffle linkFrom inlinks)
--                                web
--       scoresDictsAsReplaces <- W.mapDict (W.mapDict W.floatToReplace) scoresDicts
--       scoresDictsAsSums <- W.mapDict (W.mapDict W.floatReplaceToSum) scoresDicts
--       scores <- W.mapDict (\scoresDictAsSum -> W.sumMSet =<< W.dictValues scoresDictAsSum)
--                           scoresDictsAsSums
--       retstuff <- W.struct [("scores",W.anyNode scores),
--                             ("scoresDicts", W.anyNode scoresDicts),
--                             ("scoresDictsAsReplaces", W.anyNode scoresDictsAsReplaces),
--                             ("scoresDictsAsSums", W.anyNode scoresDictsAsSums),
--                             ("outScores'", W.anyNode outScores)]
--       return (scores, retstuff)



pageRank n links = do
  web <- W.shuffle linkTo links
  outdegreesAsSum <- W.mapDict W.lengthList =<< W.shuffle linkFrom links
  outdegreesAsReplaces <- W.mapDict W.integerToReplace outdegreesAsSum
  outdegrees <- W.mapDict W.integerReplaceToProduct outdegreesAsReplaces
  scores0 <- W.mapDict (\_ -> W.const (1::Double)) web
  (scores, structElems) <- pageRank' 0 n web outdegrees scores0
  W.struct $ ("outdegrees", W.anyNode outdegrees):
             ("outdegreesAsSum", W.anyNode outdegreesAsSum):
             ("outdegreesAsReplaces", W.anyNode outdegreesAsReplaces):
             ("scores0", W.anyNode scores0):
             structElems

pageRank' n' n web outdegrees scores0
 | n' == n   = do return (scores0, [])
 | otherwise = do (scores1, struct0) <- pageRankIteration web outdegrees scores0
                  (scores, struct) <- pageRank' (n'+1) n web outdegrees scores1
                  return (scores, (Text.pack ("iteration" ++ show n'), W.anyNode struct0):struct)


--data Event = A Text Integer
--           | B Text Text
--
--instance Datable Event where
--  toData (A w d) = ListData [StringData "A", toData w, toData d]
--  toData (B w1 w2) = ListData [StringData "B", toData w1, toData w2]
--  fromData (ListData [StringData "A", w, d]) = A (fromData w) (fromData d)
--  fromData (ListData [StringData "B", w1, w2]) = B (fromData w1) (fromData w2)
--  fromData e = error $ "Can't fromData event " ++ show e
--
--isA (A _ _) = True
--isA _ = False
--
--numA (A _ n) = n
--textA (A t _) = t
--
--t1B (B t _) = t
--t2B (B _ t) = t
--
--
--appState :: W.List Event -> W.Func W.Struct
--appState evts = 
--  do sumOfA <- return evts >>=
--               W.filterList isA >>=
--               W.shuffle textA >>=
--               W.mapDict (\as -> W.mapList numA as >>=
--                                 W.sumList)
--     sumOfAAsReplaces <- W.mapDict W.integerToReplace sumOfA
--     sumOfAAsProducts <- W.mapDict W.integerReplaceToProduct sumOfAAsReplaces
--     shuffledBs <- return evts >>= W.filterList (not . isA) >>= W.shuffle t1B
--     bs <- W.mapDict (\bs ->
--                        W.shuffle t2B bs >>= 
--                        W.mapDictWithKey (\k _ -> W.dictSlowLookup (W.dictSlowKey k id) sumOfAAsProducts)  >>=
--                        W.dictValues >>=
--                        W.productMSet)
--                      shuffledBs
--     bsAsFloat <- W.mapDict W.intToFloat bs
--     bsLengths <- W.mapDict (\bs -> W.lengthList bs)
--                            shuffledBs
--     bsLengthsAsReplaces <- W.mapDict W.integerToReplace bsLengths
--     bsLengthsAsProducts <- W.mapDict W.integerReplaceToProduct bsLengthsAsReplaces
--     bsLengthsAsFloat <- W.mapDict W.intToFloat bsLengthsAsProducts
--     W.struct [
--       ("sum", W.anyNode sumOfA),
--       ("sumOfAAsReplaces", W.anyNode sumOfAAsReplaces),
--       ("sumOfAAsProducts", W.anyNode sumOfAAsProducts),
--       ("productOfSums", fmap W.AnyNode $ W.productMSet =<< W.dictValues sumOfAAsProducts),
--       ("bs", W.anyNode bs),
--       ("bsLengths", W.anyNode bsLengths),
--       ("bsLengthsAsReplaces", W.anyNode bsLengthsAsReplaces),
--       ("bsLengthsAsProducts", W.anyNode bsLengthsAsProducts),
--       ("bsLengthsAsFloat", W.anyNode bsLengthsAsFloat),
--       ("quotients", fmap W.AnyNode $ W.mapDictWithKey (\k bsLength -> do
--                                                          bs' <- W.dictLookup k bsAsFloat
--                                                          W.divide bs' bsLength
--                                                       )
--                                                       bsLengthsAsFloat)]

prepare :: (W.Func (W.List e)) -> (W.List e -> (W.Func s)) -> ((W.List e),s)
prepare input f = evalState go 0
  where go = do i <- input
                s <- f i
                return (i,s)
                     

main = do
{-
          let changes = [A "fish" 2
                        ,A "fish" 4
                        ,A "cat" 5
                        ,A "tiger" 3
                        ,A "tiger" 1
                        ,B "feline" "cat"
                        ,B "feline" "tiger"
                        ]
          let (inputList, state) = prepare W.inputList appState
-}
          let links = [Link "A" "B",
                       Link "A" "C"
                     ]
          let (inputList, state) = prepare W.inputList (pageRank 1)
          let universe = W.initialUniverse Set.empty state 
          putStrLn $ W.printNode state
          putStrLn $ unlines [ show u | u <- Map.toList universe]
          let compiled = W.fullCompile $ W.AnyNode state
          let finalUniverse = foldl (\s i -> W.trace (W.printUniverseData $ W.toUniverseData state s) $ W.applyChange compiled state inputList s i)
                                 universe
                                 [W.ListImpulse $ W.AddElement $ W.toData c | c <- links]
                             --  [W.ListImpulse $ W.AddElement $ W.toData c | c <- changes]
          putStrLn $ W.printUniverseData $ W.toUniverseData state finalUniverse
          --let structMap (StructData _ m) = m
          --let dictMap (MapData _ _ _ _ m) = m
          --let iteration = Map.findWithDefault undefined "iteration0" $ structMap finalState
          --let scores = dictMap $ Map.findWithDefault undefined "scores" $ structMap iteration
          --putStrLn $ show $ Map.map (\s -> Map.findWithDefault undefined "score" $ structMap s) scores
