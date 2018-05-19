{-# LANGUAGE GADTs #-}

module Data.GSetSpec where

import Test.Hspec
import Test.Hspec.SmallCheck
import Test.SmallCheck
import Helpers

import GHC.Exts (IsList(..))

import Data.GSet
import Data.BooleanAlgebra


spec :: Spec
spec = do
    describe "Eq.(==)" $ do
        it "is reflexive" $ do
            property $ \(s :: Set Small) -> s `shouldBe` s

        it "agrees with Ord.compare" $ do
            property $ \(s :: Set Small) t -> compare s t == EQ ==> s `shouldBe` t

        it "handles compelements" $ do
            property $ \(s :: Set Small) ->
                s `shouldBe` complement (fromList [a | a <- [A .. ], not (a `member` s)])



    describe "Ord.compare" $ do
        it "is reflexive" $ do
            property $ \(s :: Set Small) -> compare s s `shouldBe` EQ

        it "agrees with Eq.(==)" $ do
            property $ \(s :: Set Small) t -> s == t ==> compare s t `shouldBe` EQ

        it "is flippable" $ do
            property $ \(s :: Set Small) t -> compare s t == LT ==> compare t s`shouldBe` GT
        it "is flippable" $ do
            property $ \(s :: Set Small) t -> compare s t == GT ==> compare t s`shouldBe` LT

        it "is transitive" $ do
            property $ \(s :: Set Small) t u ->
                s <= t ==> t <= u ==> s <= u `shouldBe` True


