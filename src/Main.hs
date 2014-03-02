import qualified Waltz as W
import Waltz (Data (..), Datable (..))
import Control.Monad.State
import Data.Text (Text)

data Event = A Text Integer
           | B Text Text

instance Datable Event where
  toData (A w d) = ListData [StringData "A", toData w, toData d]
  toData (B w1 w2) = ListData [StringData "B", toData w1, toData w2]
  fromData (ListData [StringData "A", w, d]) = A (fromData w) (fromData d)
  fromData (ListData [StringData "B", w1, w2]) = B (fromData w1) (fromData w2)
  fromData e = error $ "Can't fromData event " ++ show e

isA (A _ _) = True
isA _ = False

numA (A _ n) = n
textA (A t _) = t

t1B (B t _) = t
t2B (B _ t) = t

appState :: W.List Event -> W.Func W.Struct
appState evts = 
  do sumOfA <- return evts >>=
               W.filterList isA >>=
               W.shuffle textA >>=
               W.mapDict (\as -> W.mapList numA as >>=
                                 W.sumList)
     sumOfAAsReplaces <- W.mapDict W.sumToReplace sumOfA
     sumOfAAsProducts <- W.mapDict W.replaceToProduct sumOfAAsReplaces
     shuffledBs <- return evts >>= W.filterList (not . isA) >>= W.shuffle t1B
     bs <- W.mapDict (\bs ->
                        W.shuffle t2B bs >>= 
                        W.mapDictWithKey (\k _ -> W.dictSlowLookup (W.dictSlowKey k id) sumOfAAsProducts)  >>=
                        W.dictValues >>=
                        W.productMSet)
                      shuffledBs
     bsAsFloat <- W.mapDict W.intToFloat bs
     bsLengths <- W.mapDict (\bs -> W.lengthList bs)
                            shuffledBs
     bsLengthsAsReplaces <- W.mapDict W.sumToReplace bsLengths
     bsLengthsAsProducts <- W.mapDict W.replaceToProduct bsLengthsAsReplaces
     bsLengthsAsFloat <- W.mapDict W.intToFloat bsLengthsAsProducts
     W.struct [
       ("sum", fmap W.AnyNode $ return sumOfA),
       ("sumOfAAsReplaces", fmap W.AnyNode $ return sumOfAAsReplaces),
       ("sumOfAAsProducts", fmap W.AnyNode $ return sumOfAAsProducts),
       ("productOfSums", fmap W.AnyNode $ W.productMSet =<< W.dictValues sumOfAAsProducts),
       ("bs", fmap W.AnyNode $ return bs),
       ("bsLengths", fmap W.AnyNode $ return bsLengths),
       ("bsLengthsAsReplaces", fmap W.AnyNode $ return bsLengthsAsReplaces),
       ("bsLengthsAsProducts", fmap W.AnyNode $ return bsLengthsAsProducts),
       ("bsLengthsAsFloat", fmap W.AnyNode $ return bsLengthsAsFloat),
       ("quotients", fmap W.AnyNode $ W.mapDictWithKey (\k bsLength -> do
                                                          bs' <- W.dictLookup k bsAsFloat
                                                          W.divide bs' bsLength
                                                       )
                                                       bsLengthsAsFloat)]

prepare :: (W.Func (W.List e)) -> (W.List e -> (W.Func s)) -> ((W.List e),s)
prepare input f = evalState go 0
  where go = do i <- input
                s <- f i
                return (i,s)
                     

main = do let changes = [A "fish" 2
                        ,A "fish" 4
                        ,B "feline" "cat"
                        ,B "feline" "tiger"
                        ,A "cat" 5
                        ,A "tiger" 3
                        ,A "tiger" 1
                        ]

          let (inputList, state) = prepare W.inputList appState
          let initialState = W.nodeInitialValue $ state
          putStrLn $ W.printNode state
          let compiled = W.fullCompile $ W.AnyNode state
          let finalState = foldl (\s i -> W.trace (show s) $ W.applyChange compiled state inputList s i)
                                 initialState
                                 [W.ListImpulse $ W.AddElement $ W.toData c | c <- changes]
          putStrLn $ show finalState
