import qualified Waltz as W
import Waltz (Data (..), Datable (..))
import Control.Monad.State
import Data.Text (Text)

data Event = NewWord Text
           | NewDefinition Text Text

instance Datable Event where
  toData (NewWord s) = toData ["NewWord", s]
  toData (NewDefinition w d) = toData ["NewDefinition", w, d]
  fromData (ListData ((StringData e):args))
    | e == "NewWord"       = let [w] = args
                              in NewWord (fromData w)
    | e == "NewDefinition" = let [w,d] = args
                              in NewDefinition (fromData w) (fromData d)
  fromData e = error $ "Can't fromData event " ++ show e

isNewWord (NewWord _) = True
isNewWord _ = False

isNewDefinition (NewDefinition _ _) = True
isNewDefinition _ = False

eventWord a = eventWord' a
eventWord' (NewWord w) = w
eventWord' (NewDefinition w _) = w

eventDefinition (NewDefinition _ d) = d
eventDefinition _ = error "no definition"

appState :: W.List Event -> W.Func W.Struct
appState evts = W.struct [
                 ("words", fmap W.AnyNode $ 
                           return evts >>= 
                           W.filterList isNewWord >>= 
                           W.mapList eventWord),
                 ("defns", fmap W.AnyNode $
                           return evts >>=
                           W.filterList isNewDefinition >>=
                           W.shuffle eventWord >>=
                           W.mapDict (\defnEvents -> W.struct [
                                      ("bodies", fmap W.AnyNode $
                                                 return defnEvents >>= 
                                                 W.mapList eventDefinition),
                                      ("count", fmap W.AnyNode $
                                                return defnEvents >>= 
                                                W.lengthList)
                                    ]))
                 ]


prepare :: (W.Func (W.List e)) -> (W.List e -> (W.Func s)) -> ((W.List e),s)
prepare input f = evalState (prepare' input f) 0

prepare' :: (W.Func (W.List e)) -> (W.List e -> (W.Func s)) -> W.Func ((W.List e),s)
prepare' input f = do i <- input
                      s <- f i
                      return (i,s)
                     

main = do let changes = [NewWord "Dog"
                        ,NewDefinition "Dog" "Man's best friend"
                        ,NewDefinition "Dog" "A Wolfish Beast"]

          let (inputList, state) = prepare W.inputList appState
          let initialState = W.nodeInitialValue $ state
          putStrLn $ W.printNode state
          let compiled = W.fullCompile $ W.AnyNode state
          let finalState = foldl (W.applyChange compiled state inputList)
                                 initialState
                                 [W.ListImpulse $ W.AddElement $ W.toData c | c <- (reverse changes)]
          print $ show finalState
