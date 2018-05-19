{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | A very cruddy implementation of sparse vectors. We define vectors
-- with a known length @n@ so we can define a 'Semiring' instance.
--
-- TODO: find a package or make nicer
module SparseVector
    ( SparseVector
    , vector
    , (!)
    , length

    , (++)
    , split

    , map
    , zipWith

    , sum
    , nonZero
    , toList
    ) where

import Prelude hiding (length, map, sum, zipWith, (++))
import Control.Exception (assert)

import Data.Finite
import Data.Singletons
import Data.Singletons.Prelude
import Data.Singletons.TypeLits

import qualified Data.IntMap.Strict as IntMap
import Data.Semiring (Semiring(..), DetectableZero(..))


-- | Sparse vectors of length @n@ over elements of type @a@.
newtype SparseVector (n :: Nat) a =
    UnsafeMakeSparseVector {
        elements :: IntMap.IntMap a
    }


-- | Construct a sparse vector from a list of indexed elements. Indexes
-- not in the list are all set to zero. Duplicate indexes are combined
-- with '(<+>)'. We need to be able to tell when elements are zero so we
-- can filter them out.
vector :: (DetectableZero a, KnownNat n) => [(Finite n, a)] -> SparseVector n a
vector l =
    UnsafeMakeSparseVector {
        elements =
            removeZeros $
                IntMap.fromListWith (<+>) [(fromIntegral i, a) | (i, a) <- l]
    }


-- | The value at a given index.
(!) :: (Semiring a, KnownNat n) => SparseVector n a -> Finite n -> a
v ! i =
    IntMap.findWithDefault zero (fromIntegral i) (elements v)


-- | Length of a vector.
length :: forall n a r. (KnownNat n, Integral r) => SparseVector n a -> r
length _ =
    fromIntegral $ fromSing (sing :: SNat n)


-- | Sum of all elements in a vector.
sum :: Semiring a => SparseVector n a -> a
sum v =
    IntMap.foldr (<+>) zero (elements v)


-- | Concatenate two vectors.
(++) :: KnownNat n
     => SparseVector n a
     -> SparseVector m a
     -> SparseVector (n + m) a
v1 ++ v2 =
    UnsafeMakeSparseVector {
        elements =
            IntMap.union
                (elements v1)
                (IntMap.mapKeysMonotonic (length v1 +) (elements v2))
    }


-- | We can map from vectors with one type for elements to another given
-- a semiring homomorphism. Note that this does not work for arbitrary
-- functions. Specifically, this function must map zeros to zeros.
map :: (DetectableZero a, DetectableZero b)
    => (a -> b)
    -> SparseVector n a
    -> SparseVector n b
map f v =
    assert (isZero $ f zero) $
    UnsafeMakeSparseVector {
        elements =
            removeZeros $
                IntMap.map f (elements v)
    }


-- | Combine two vectors of equal length with the given function.
-- The function should return zero when /both/ its arguments are
-- zero.
zipWith :: (DetectableZero a, DetectableZero b, DetectableZero c)
        => (a -> b -> c)
        -> SparseVector n a
        -> SparseVector n b
        -> SparseVector n c
zipWith f v1 v2 =
    assert (isZero $ f zero zero) $
    UnsafeMakeSparseVector {
        elements =
            removeZeros $
                IntMap.mergeWithKey
                    (\_ a b -> Just (f a b))
                    (IntMap.map (`f` zero))
                    (IntMap.map (zero `f`))
                    (elements v1)
                    (elements v2)
    }



-- | Split a vector into two vectors.
split :: forall n m a. (KnownNat n, KnownNat m)
      => SparseVector (n + m) a
      -> (SparseVector n a, SparseVector m a)
split v =
    ( UnsafeMakeSparseVector { elements = v1 }
    , UnsafeMakeSparseVector { elements = v2 }
    )
    where
        (v1, v2') =
            IntMap.partitionWithKey (\k _ -> k < n) (elements v)

        v2 =
            IntMap.mapKeysMonotonic (subtract n) v2'

        n =
            fromIntegral $ fromSing (sing :: SNat n)



-- | Iterate over non-zero elements in a vector.
nonZero :: KnownNat n => SparseVector n a -> [(Finite n, a)]
nonZero v =
    fmap (\(i, x) -> (finite $ fromIntegral i, x)) (IntMap.toList $ elements v)


-- | Convert a vector to a list.
toList :: (Semiring a, KnownNat n) => SparseVector n a -> [a]
toList v =
    [v ! i | i <- finites]


-- | Vectors of length @n@ over elements drawn from a semiring also
-- form a semiring.
instance (DetectableZero a, KnownNat n) => Semiring (SparseVector n a) where

    -- | Vector where all entries are zero.
    zero =
        UnsafeMakeSparseVector {
            elements =
                IntMap.empty
        }


    -- | Vector where all entries are one.
    one =
        -- We need to treat the trivial semiring as a special case
        if isZero (one :: a) then
            zero
        else
            UnsafeMakeSparseVector {
                elements =
                    IntMap.fromList [(i, one) | i <- [0 .. length - 1]]
            }
        where
            length =
                fromIntegral $ fromSing (sing :: SNat n)


    -- | Vector addition.
    v1 <+> v2 =
        UnsafeMakeSparseVector {
            elements =
                removeZeros $
                    IntMap.unionWith (<+>) (elements v1) (elements v2)
        }


    -- | Vector dot product.
    v1 <.> v2 =
        UnsafeMakeSparseVector {
            elements =
                removeZeros $
                    IntMap.intersectionWith (<.>) (elements v1) (elements v2)
        }


-- | We can recognize the zero vector.
instance (DetectableZero a, KnownNat n) => DetectableZero (SparseVector n a) where
    isZero v1 =
        IntMap.null (elements v1)


-- | Equality of vectors is decidable.
deriving instance Eq a => Eq (SparseVector n a)


-- | We can totally order vectors.
deriving instance Ord a => Ord (SparseVector n a)


instance (Semiring a, KnownNat n, Show a) => Show (SparseVector n a) where
    show =
        show . toList



-- * Helper functions

-- | Remove zero elements.
removeZeros :: DetectableZero a => IntMap.IntMap a -> IntMap.IntMap a
removeZeros =
    IntMap.filter (not . isZero)

