{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedLists #-}

module RegExp.Internal.DFASpec where

import Test.Hspec
import Test.QuickCheck
import Helpers

import Data.Either(isRight)

import RegExp.RegExp
import RegExp.Internal.DFA
import RegExp.Derivative(equivalent)

import Data.GSet()


spec :: Spec
spec = do
    describe "regexp" $ do
        it "is the inverse of fromRegExp" $ do
            mapSize (`div` 4) $
                property $ \(r :: RegExp Helpers.Small) ->
                    regexp (fromRegExp r) `shouldSatisfy` (isRight . equivalent r)
