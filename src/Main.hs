import qualified Waltz as W
import Waltz (Data (..), Datable (..))

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

eventWord (NewWord w) = w
eventWord (NewDefinition w _) = w

eventDefinition (NewDefinition _ d) = d
eventDefinition _ = error "no definition"

appState :: W.List Event -> W.Struct
appState evts = W.struct [
                 ("words", W.WatchableThing $
                           ((W.mapList eventWord) . 
                            (W.filterList isNewWord))
                            evts),
                 ("defns", W.WatchableThing $
                           ((W.mapDict (\defnEvents -> W.structN 1000 [
                              ("bodies", W.WatchableThing $ W.mapList eventDefinition defnEvents),
                              ("count", W.WatchableThing $ W.lengthList defnEvents)
                            ])) .
                            (W.shuffle eventWord) .
                            (W.filterList isNewDefinition))
                            evts)
                 ]

main = do let changes = [NewWord "Dog"
                        ,NewDefinition "Dog" "Man's best friend"
                        ,NewDefinition "Dog" "A Wolfish Beast"]
          let inputList = W.inputList :: (W.List Event)
          let state = appState inputList
          let initialState = W.initialValue $ state
          putStrLn (W.pprint 0 state)
          let compiled = W.fullCompile $ W.WatchableThing state
          let finalState = foldl (W.applyChange compiled state inputList)
                                 initialState
                                 [W.ListImpulse $ W.AddElement $ W.toData c | c <- (reverse changes)]
          print $ show finalState
