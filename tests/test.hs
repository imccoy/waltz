import Control.Monad.State
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Text as T

import Test.Tasty
import Test.Tasty.HUnit
import qualified Test.Tasty.QuickCheck as QC

import qualified Waltz as W

prepare input f = evalState go 0
  where go = do i <- input
                s <- f i
                return (i,s)

compileAndRun inputList state impulses = foldl (W.applyChange compiled state inputList)
                                               initialState
                                               impulses
            where initialState = W.nodeInitialValue state
                  compiled = W.fullCompile $ W.AnyNode state
                               

-- WARNING: There is no typesafety on the relationship between b' and b.
run :: (W.Watchable b', W.Datable a, W.Datable b)
     => (W.List a -> W.Func (W.Node b')) -> [a] -> b
run f args = let (inputList, state) = prepare W.inputList f
              in W.fromData $ compileAndRun inputList state [W.ListImpulse $ W.AddElement $ W.toData c | c <- args]

main = defaultMain tests

tests = testGroup "Tests" [listTests, shuffleTests]

listTests = testGroup "Lists"
  [ testCase "the input can pass through unchanged " $
    [1 :: Integer, 2] `compare` run (\inp -> return inp) [1 :: Integer, 2] @?= EQ
  , QC.testProperty "map int->int" $
    \(as :: [Integer]) -> 
      let f = (* 3)
       in map f as == run (\inp -> W.mapList f inp) as
  , QC.testProperty "map int->int->int" $
    \(as :: [Integer]) -> 
      let f = (* 3)
          g = (+ 2)
       in map f (map g as) == run (\inp -> W.mapList f =<< W.mapList g inp) as
  , QC.testProperty "map int->string" $
    \(as :: [Integer]) -> 
      let f = (T.pack . show)
       in map f as == run (\inp -> W.mapList f inp) as
  ]


shuffleTests = testGroup "Shuffling" $
  let hsShuffle f as = Map.fromListWith (flip (++)) [(f a, [a]) | a <- as]
   in [ testCase "works with the identity shuffler" $
        Map.fromList [(1 :: Integer, [1 :: Integer, 1]), (-2, [-2])] `compare` run (\inp -> W.shuffle id inp) [1 :: Integer,1,-2] @?= EQ
      , QC.testProperty "works with a simple shuffler" $
        \(as :: [Integer]) ->
          let f n = n `mod` 4
           in (hsShuffle f as) == run (\inp -> W.shuffle f inp) as
      , QC.testProperty "can map over a shuffled list" $
        \(as :: [Integer]) ->
          let f n = n `mod` 4
           in (==) (Map.map (map (*2)) (hsShuffle f as))
                   (run (\inp -> W.mapDict (W.mapList (*2)) =<< W.shuffle f inp) as)
      , QC.testProperty "can fold over a shuffled list" $
        \(as :: [Integer]) ->
          let f n = n `mod` 4
           in (==) (Map.map sum (hsShuffle f as))
                   (run (\inp -> W.mapDict W.sumList =<< W.shuffle f inp) as)
 
      ]
