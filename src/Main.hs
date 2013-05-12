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

data AppState = AppState (W.List Text) (W.ListDict Text Text)

appState :: W.List Event -> AppState
appState evts = AppState (((W.mapList eventWord) . 
                           (W.filterList isNewWord))
                          evts)
                         (((W.mapListDict eventDefinition) .
                           (W.shuffle eventWord) .
                           (W.filterList isNewDefinition))
                          evts)

main = return ()
