import qualified Waltz as W
import Waltz (Data (..), Datable (..))
import Control.Monad.State
import Data.Text (Text)

data Event = A Text Integer

instance Datable Event where
  toData (A w d) = ListData [toData w, toData d]
  fromData (ListData [w, d]) = A (fromData w) (fromData d)
  fromData e = error $ "Can't fromData event " ++ show e

numA (A _ n) = n
textA (A t _) = t

appState :: W.List Event -> W.Func W.Struct
appState evts = 
  do sumOfA <- return evts >>=
               W.shuffle textA >>=
               W.mapDict (\as -> W.mapList numA as >>=
                                 W.sumList)
     sumOfAAsReplaces <- W.mapDict W.sumToReplace sumOfA
     sumOfAAsProducts <- W.mapDict W.replaceToProduct sumOfAAsReplaces
     W.struct [
       ("sum", fmap W.AnyNode $ return sumOfA),
       ("sumOfAAsReplaces", fmap W.AnyNode $ return sumOfAAsReplaces),
       ("sumOfAAsProducts", fmap W.AnyNode $ return sumOfAAsProducts),
       ("productOfSums", fmap W.AnyNode $ W.productList =<< W.dictValues sumOfAAsProducts)]

prepare :: (W.Func (W.List e)) -> (W.List e -> (W.Func s)) -> ((W.List e),s)
prepare input f = evalState go 0
  where go = do i <- input
                s <- f i
                return (i,s)
                     

main = do let changes = [A "fish" 2
                        ,A "fish" 4
                        ,A "cat" 5]

          let (inputList, state) = prepare W.inputList appState
          let initialState = W.nodeInitialValue $ state
          putStrLn $ W.printNode state
          let compiled = W.fullCompile $ W.AnyNode state
          let finalState = foldl (W.applyChange compiled state inputList)
                                 initialState
                                 [W.ListImpulse $ W.AddElement $ W.toData c | c <- (reverse changes)]
          putStrLn $ show finalState
