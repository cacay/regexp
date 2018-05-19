{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

-- TODO: remove
{-# LANGUAGE AllowAmbiguousTypes #-}

-- | A very cruddy implementation of sparse matrices. I couldn't
-- find an existing implementation that had all that I needed, so
-- I cooked this up.
--
-- TODO: find a package or make nicer
module SparseMatrix
    ( SparseMatrix
    , matrix
    , fromRows
    , (!)
    , nthRow

    , plus
    , times
    , transpose

    , map
    , nonZero
    , nonZeroRows
    , toList
    ) where

import Flow
import Prelude hiding (map)

import Data.Function (on)
import Data.List (sortBy, groupBy, intercalate)
import Data.Ord (comparing)

import Data.Finite
import Data.Singletons
import Data.Singletons.Decide
import Data.Singletons.Prelude
import Data.Singletons.TypeLits

import Data.Semiring (Semiring(..), DetectableZero(..))
import Data.KleeneAlgebra

import SparseVector (SparseVector)
import qualified SparseVector as Vector



-- | A sparse matrix with @r@ rows and @c@ columns over
-- elements of type @a@.
newtype SparseMatrix (r :: Nat) (c :: Nat) a =
    UnsafeMakeSparseMatrix {
        rows :: SparseVector r (SparseVector c a)
    }


-- | Value at the given row and column.
(!) :: (DetectableZero a, KnownNat r, KnownNat c)
    => SparseMatrix r c a
    -> (Finite r, Finite c)
    -> a
m ! (r, c) =
    (rows m Vector.! r) Vector.! c


-- | Row with the given index.
nthRow :: (DetectableZero a, KnownNat r, KnownNat c)
    => Finite r
    -> SparseMatrix r c a
    -> SparseVector c a
nthRow r m =
    rows m Vector.! r


-- | Construct a sparse matrix from a list of indexed elements. Indices
-- that don't appear in the list are all set to zero. Duplicate indexes
-- are combined with '(<+>)'.
--
-- We need detectable zeros so we can filter them out.
matrix :: (DetectableZero a, KnownNat r, KnownNat c)
       => [((Finite r, Finite c), a)]
       -> SparseMatrix r c a
matrix l =
    UnsafeMakeSparseMatrix {
        rows =
            sortBy (comparing (fst . fst)) l
                |> groupBy ((==) `on` (fst . fst))
                |> fmap (\l -> (fst $ fst $ head l, fmap dropRow l))
                |> fmap (\(r, elements) -> (r, Vector.vector elements))
                |> Vector.vector
    }
    where
        dropRow :: ((r, c), a) -> (c, a)
        dropRow ((r, c), x)=
            (c, x)


-- | Construct a sparse matrix from a list of indexed vectors corresponding
-- to the rows of the matrix.
fromRows :: (DetectableZero a, KnownNat r, KnownNat c)
         => [(Finite r, SparseVector c a)]
         -> SparseMatrix r c a
fromRows rows =
    UnsafeMakeSparseMatrix {
        rows =
            Vector.vector rows
    }


-- | Matrix addition.
plus :: (DetectableZero a, KnownNat r, KnownNat c)
     => SparseMatrix r c a
     -> SparseMatrix r c a
     -> SparseMatrix r c a
plus m1 m2 =
    UnsafeMakeSparseMatrix {
        rows =
            rows m1 <+> rows m2
    }


-- | Matrix multiplication.
times :: (DetectableZero a, KnownNat r, KnownNat m, KnownNat c)
     => SparseMatrix r m a
     -> SparseMatrix m c a
     -> SparseMatrix r c a
times m1 m2 =
    UnsafeMakeSparseMatrix {
        rows =
            Vector.map (\r -> Vector.map (\c -> r `cross` c) (rows m2Tr)) (rows m1)
    }
    where
        m2Tr =
            transpose m2

        cross v1 v2 =
            Vector.sum (v1 <.> v2)


-- | Swap the rows of a matrix with its columns.
transpose :: (DetectableZero a, KnownNat r, KnownNat c)
          => SparseMatrix r c a
          -> SparseMatrix c r a
transpose m =
    UnsafeMakeSparseMatrix {
        rows =
            Vector.vector [(i, Vector.map (Vector.! i) (rows m)) | i <- finites]
    }


-- | Split a square matrix into four quadrants.
split :: forall s t a. (DetectableZero a, KnownNat s, KnownNat t)
      => SparseMatrix (s + t) (s + t) a
      -> ( SparseMatrix s s a
         , SparseMatrix s t a
         , SparseMatrix t s a
         , SparseMatrix t t a
         )
split m =
    withKnownNat ((sing :: SNat s) %+ (sing :: SNat t)) $
        let
            (top, bottom) =
                Vector.split (rows m)

            topSplit =
                Vector.map Vector.split top

            bottomSplit =
                Vector.map Vector.split bottom

            a = UnsafeMakeSparseMatrix { rows = Vector.map fst topSplit }
            b = UnsafeMakeSparseMatrix { rows = Vector.map snd topSplit }
            c = UnsafeMakeSparseMatrix { rows = Vector.map fst bottomSplit }
            d = UnsafeMakeSparseMatrix { rows = Vector.map snd bottomSplit }
        in
            (a, b, c, d)


-- | Combine four quadrants into a single square matrix.
combine :: forall s t a. (DetectableZero a, KnownNat s, KnownNat t)
        => ( SparseMatrix s s a
           , SparseMatrix s t a
           , SparseMatrix t s a
           , SparseMatrix t t a
           )
        -> SparseMatrix (s + t) (s + t) a
combine (a, b, c, d) =
    withKnownNat ((sing :: SNat s) %+ (sing :: SNat t)) $
        let
            top =
                Vector.zipWith (Vector.++) (rows a) (rows b)

            bottom =
                Vector.zipWith (Vector.++) (rows c) (rows d)
        in
            UnsafeMakeSparseMatrix {
                rows =
                    top Vector.++ bottom
            }


-- | We can map from matrices with one type for elements to another given
-- a semiring homomorphism. Note that this does not work for arbitrary
-- functions. Specifically, this function must map zeros to zeros.
map :: (DetectableZero a, DetectableZero b, KnownNat r, KnownNat c)
    => (a -> b)
    -> SparseMatrix r c a
    -> SparseMatrix r c b
map f m =
    UnsafeMakeSparseMatrix {
        rows =
            Vector.map (Vector.map f) (rows m)
    }


-- | Iterate over non-zero elements in a matrix.
nonZero :: (KnownNat r, KnownNat c)
        => SparseMatrix r c a
        -> [((Finite r, Finite c), a)]
nonZero m =
    concatMap
      (\(r, row) -> [((r, c), a) | (c, a) <- Vector.nonZero row])
      (Vector.nonZero $ rows m)


-- | Iterate over non-zero elements in a matrix grouped by rows.
nonZeroRows :: (KnownNat r, KnownNat c)
        => SparseMatrix r c a
        -> [(Finite r, [(Finite c, a)])]
nonZeroRows m =
    fmap
        (\(r, row) -> (r, Vector.nonZero row))
        (Vector.nonZero $ rows m)


-- | Convert a vector to a list.
toList :: (DetectableZero a, KnownNat r, KnownNat c) => SparseMatrix r c a -> [[a]]
toList m =
    fmap Vector.toList (Vector.toList $ rows m)



-- | Square matrices form a semiring.
instance (DetectableZero a, KnownNat n) => Semiring (SparseMatrix n n a) where
    -- | Matrix where all entries are zero.
    zero =
        matrix []

    -- | Matrix where the diagonal is one.
    one =
        matrix [((i, i), one) | i <- [0..]]

    -- | Matrix addition.
    (<+>) =
        plus

    -- | Matrix multiplication.
    (<.>) =
        times


-- | We can recognize zero matrices.
instance (DetectableZero a, KnownNat n) => DetectableZero (SparseMatrix n n a) where
    isZero m =
        isZero (rows m)


-- | Square matrices over Kleene algebra form a Kleene algebra.
instance (DetectableZero a, KleeneAlgebra a, KnownNat n) => KleeneAlgebra (SparseMatrix n n a) where
    star m | Proved Refl <- (sing :: SNat n) %~ (sing :: SNat 0) =
        m
    star m | Proved Refl <- (sing :: SNat n) %~ (sing :: SNat 1) =
        matrix [((0,0), star (m ! (0, 0)))]
    star m =
        -- TODO: get rid of 'unsafeCoerce' or limit it to proving @n = small + large@.
        withKnownNat ((sing :: SNat n) `sDiv` (sing :: SNat 2)) $
        withKnownNat (((sing :: SNat n) %+ (sing :: SNat 1)) `sDiv` (sing :: SNat 2)) $
        withKnownNat (((sing :: SNat n) `sDiv` (sing :: SNat 2))
                     %+
                     (((sing :: SNat n) %+ (sing :: SNat 1)) `sDiv` (sing :: SNat 2))
                     ) $
        case (sing :: SNat n) %~ (sing :: SNat ((n `Div` 2) + ((n + 1) `Div` 2))) of
            Proved Refl ->
                combine (a', b', c', d')
                where
                    a :: SparseMatrix (n `Div` 2) (n `Div` 2) a
                    (a, b, c, d) =
                        split m

                    -- a' :: SparseMatrix small small a
                    a' = star (a `plus` (b `times` star d `times` c))

                    -- b' :: SparseMatrix small large a
                    b' = star (a `plus` (b `times` star d `times` c)) `times` b `times` star d

                    -- c' :: SparseMatrix large small a
                    c' = star (d `plus` (c `times` star a `times` b)) `times` c `times` star a

                    -- d' :: SparseMatrix large large a
                    d' = star (d `plus` (c `times` star a `times` b))

            Disproved _->
                error "impossible"



-- | Equality of matrices is decidable.
deriving instance Eq a => Eq (SparseMatrix r c a)


-- | We can totally order matrices.
deriving instance Ord a => Ord (SparseMatrix r c a)


instance (DetectableZero a, Show a, KnownNat r, KnownNat c) => Show (SparseMatrix r c a) where
    show m =
        intercalate "\n"
            [ intercalate " " (fmap (padded widest) row) | row <- grid ]

        where
            -- | Matrix as a list of lists.
            grid :: [[a]]
            grid =
                fmap Vector.toList (Vector.toList $ rows m)

            -- | Show an element of the matrix.
            show :: a -> String
            show a =
                showsPrec 11 a ""

            -- | Width of the widest entry in the matrix.
            widest :: Int
            widest =
                foldr max 0 [ length (show a) | a <- concat grid ]

            -- | Show with a constant width.
            padded :: Int -> a -> String
            padded width a =
                let
                    s = show a
                in
                    s ++ take (width - length s) (repeat ' ')