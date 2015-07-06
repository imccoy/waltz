import Control.Monad.State
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Text as T

import Test.Tasty
import Test.Tasty.HUnit
import qualified Test.Tasty.SmallCheck as SC
import qualified Test.Tasty.QuickCheck as QC

import qualified Waltz as W

prepare input f = evalState go 0
  where go = do i <- input
                s <- f i
                return (i,s)

run inputList state impulses = foldl (W.applyChange compiled state inputList)
                                     initialState
                                     impulses
  where initialState = W.nodeInitialValue state
        compiled = W.fullCompile $ W.AnyNode state
                               

runList :: (W.Datable a, W.Datable b)
        => (W.List a -> W.Func (W.List b)) -> [a] -> [b]
runList f args = let (inputList, state) = prepare W.inputList f
                  in W.fromData $ run inputList state [W.ListImpulse $ W.AddElement $ W.toData c | c <- args]


runListToDict :: (Ord k, W.Datable a, W.Datable b, W.Datable k)
              => (W.List a -> W.Func (W.Dict k (W.List b))) -> [a] -> Map k [b]
runListToDict f args = let (inputList, state) = prepare W.inputList f
                        in W.fromData $ run inputList state [W.ListImpulse $ W.AddElement $ W.toData c | c <- args]

main = defaultMain tests

tests = testGroup "Tests" [listTests, shuffleTests]

listTests = testGroup "Lists"
  [ testCase "the input can pass through unchanged " $
    [1 :: Integer, 2] `compare` runList (\inp -> return inp) [1 :: Integer, 2] @?= EQ
  , SC.testProperty "map int->int" $
    \(as :: [Integer]) -> 
      let f = (* 3)
       in map f as == runList (\inp -> W.mapList f inp) as
  , SC.testProperty "map int->string" $
    \(as :: [Integer]) -> 
      let f = (T.pack . show)
       in map f as == runList (\inp -> W.mapList f inp) as
  ]

shuffleTests = testGroup "Shuffling" $
  let hsShuffle f as = Map.fromListWith (flip (++)) [(f a, [a]) | a <- as]
   in [ testCase "works with the identity shuffler" $
        Map.fromList [(1 :: Integer, [1 :: Integer, 1]), (-2, [-2])] `compare` runListToDict (\inp -> W.shuffle id inp) [1 :: Integer,1,-2] @?= EQ
      , QC.testProperty "works with a simple shuffler" $
        \(as :: [Integer]) ->
          let f n = n `mod` 4
           in (hsShuffle f as) == runListToDict (\inp -> W.shuffle f inp) as
      ]
