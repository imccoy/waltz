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

isNewWord (NewWord _) = True
isNewWord _ = False

isNewDefinition (NewDefinition _ _) = True
isNewDefinition _ = False

eventWord (NewWord w) = w
eventWord (NewDefinition w _) = w

eventDefinition (NewDefinition _ d) = d
eventDefinition _ = error "no definition"

appState :: W.List Event -> W.Struct
appState evts = W.Struct [
                 ("words", W.WatchableThing $
                           ((W.mapList eventWord) . 
                            (W.filterList isNewWord))
                            evts),
                 ("defns", W.WatchableThing $
                           ((W.mapListDict eventDefinition) .
                            (W.shuffle eventWord) .
                            (W.filterList isNewDefinition))
                            evts)]

main = do let changes = [NewWord "Dog"
                        ,NewDefinition "Dog" "Man's best friend"]
          let initialState = W.initialValue $ appState W.InputList
          let (W.Struct structElems) = appState W.InputList
          let finalState = foldl W.applyChange initialState $
                             concatMap (\c -> map (\(n, _) -> W.StructElementChange n [
                                               W.ListChange $ W.AddElement $ toData c])
                                            structElems
                                 ) changes
          print $ show finalState
