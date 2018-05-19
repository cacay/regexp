{-# LANGUAGE GADTs #-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module RegExp.RegExpSpec where

import Test.Hspec
import Test.QuickCheck

import RegExp.RegExp
import RegExp.Derivative (matches)

import Data.GSet


spec :: Spec
spec = do
    describe "zero" $ do
        it "does not match the empty string" $ do
            (rZero `matches` "") `shouldBe` False
        it "does not match non-empty strings" $ do
            (rZero `matches` "a") `shouldBe` False
            (rZero `matches` "abc") `shouldBe` False
        it "does not match any string" $ do
            property $ \(w :: String) -> (rZero `matches` w) `shouldBe` False

    describe "one" $ do
        it "matches the empty string" $ do
            (rOne `matches` "") `shouldBe` True
        it "does not match non-empty strings" $ do
            property $ \c (w :: String) -> (rZero `matches` (c : w)) `shouldBe` False

    describe "plus" $ do
        it "matches when either subexpression matches" $ do
            let r1 = "abc"
            let r2 = "def"
            (rPlus r1 r2 `matches` "a") `shouldBe` True

    describe "times" $ do
        it "matches when both subexpressions match in order" $ do
            let r1 = "abc"
            let r2 = "def"
            (rTimes r1 r2 `matches` "af") `shouldBe` True

    describe "star" $ do
        it "matches the empty string" $ do
            (rStar "abc" `matches` "") `shouldBe` True
        it "matches once" $ do
            (rStar "abc" `matches` "c") `shouldBe` True
        it "matches multiple times" $ do
            (rStar "abc" `matches` "abcbabc") `shouldBe` True

    describe "literal" $ do
        it "matches one of the options" $ do
            (rLiteral "ab" `matches` "a") `shouldBe` True
            (rLiteral "ab" `matches` "b") `shouldBe` True
        it "does not match characters not in the class" $ do
            (rLiteral "ab" `matches` "c") `shouldBe` False


    describe "hide" $ do
        it "is the inverse of view" $ do
            property $ \(r :: RegExp Char) -> hide (view r) `shouldBe` r

        it "is the deep inverse of view" $ do
            property $ \(r :: RegExp Char) -> hideAll (viewAll r) `shouldBe` r


    describe "read" $ do
        it "is the inverse of show" $ do
            withMaxSuccess 5 $ -- Reading and/or printing is super slow!
                property $ \(r :: RegExp Char) -> read (show r) `shouldBe` r



-- | Fixed point of a functor.
data Fix f = Fix {unFix :: f (Fix f)}

deriving instance Eq (f (Fix f)) => Eq (Fix f)
deriving instance Ord (f (Fix f)) => Ord (Fix f)
deriving instance Show (f (Fix f)) => Show (Fix f)


-- | Like 'view', but fully unfolds all subtrees.
viewAll :: GSet c => RegExp c -> Fix (RegExpView c)
viewAll r =
    Fix $ fmap viewAll $ view r


-- | Like 'hide', but works on a fully viewed regular expression.
hideAll :: GSet c => Fix (RegExpView c) -> RegExp c
hideAll r =
    hide (fmap hideAll $ unFix r)