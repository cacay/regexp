{-# LANGUAGE GADTs #-}

module RegExp.OperationsSpec where

import Test.Hspec
import Test.QuickCheck
import Helpers

import RegExp.RegExp
import RegExp.Operations
import qualified RegExp.Derivative as RegExp

import Data.GSet(GSet)


spec :: Spec
spec = do
    describe "intersection with equation solving" $ do
        it "is equivalent to intersection with DFAs" $ do
            mapSize (`div` 4) $
                property $ \(r1 :: RegExp Helpers.Small) r2 ->
                    (r1 `intersectionEquation` r2) `shouldMatch` (r1 `intersection` r2)

    describe "complement with equation solving" $ do
        it "is equivalent to complement with DFAs" $ do
            mapSize (`div` 4) $
                property $ \(r :: RegExp Helpers.Small) ->
                    complement r `shouldMatch` complementEquation r


-- | Set the expectation that the given regular expression
-- should be equivalent.
shouldMatch :: (GSet c, Show c, Eq c) => RegExp c -> RegExp c -> Expectation
shouldMatch r1 r2 =
    RegExp.equivalent r1 r2 `shouldBe` Right ()
