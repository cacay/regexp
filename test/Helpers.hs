{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}


-- | Helper functions for testing.
module Helpers where

import GHC.Generics

import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Gen
import Test.SmallCheck.Series


-- | A finite data type with a few constructors. Useful with SmallCheck.
data Small
    = A
    | B
    | C
    deriving (Eq, Ord, Bounded, Enum, Show, Read, Generic)


instance Monad m => Serial m Small

instance Arbitrary Small where
    arbitrary =
        elements [minBound.. ]

