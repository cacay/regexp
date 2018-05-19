{-# LANGUAGE TypeFamilies #-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}


-- | A generic interface for sets and an instance
-- supporting finite and cofinite subsets of a type.
module Data.GSet
    ( GSet (..)
    ) where

import Prelude hiding (and, or)
import Flow

import Data.String (IsString(..))
import GHC.Exts (IsList(..))
import qualified Text.ParserCombinators.ReadP as Parser

import Data.Function (on)
import Data.List (intercalate)
import qualified Data.Set

import Data.BooleanAlgebra (BooleanAlgebra(..))
import Data.Semiring (Semiring(..), DetectableZero(..))

import Test.QuickCheck as QuickCheck
import Test.SmallCheck.Series as SmallCheck


-- | A generic interface for sets over a type @a@.
class (BooleanAlgebra (Set a), DetectableZero (Set a), Ord (Set a)) => GSet a where
    -- | Sets of elements of @a@.
    type Set a :: *

    -- | The set containing a single element.
    singleton :: a -> Set a

    -- | Determine if an element is a member of a set.
    member :: a -> Set a -> Bool
    member a s =
        singleton a <.> s == singleton a

    -- | Return an arbitrary element from a non-empty set; and
    -- 'Nothing' if the set is empty. That is, the following properties
    -- should hold:
    --
    -- @'choose' 'zero' = 'Nothing'@
    --
    -- @s /= 'zero' ==> exists a. 'choose' s = 'Just' a && 'member' a s@
    choose :: Set a -> Maybe a



-- | Finite and cofinite subsets of a type form a 'Semiring'.
instance Ord a => Semiring (FiniteSet a) where
    zero =
        empty

    one =
        full

    (<+>) =
        union

    (<.>) =
        intersection


-- | We know when a finite or cofinite subset of a finite type is empty.
instance (Bounded a, Enum a, Ord a) => DetectableZero (FiniteSet a) where
    isZero p =
        size p == 0


-- | Finite and cofinite subsets of a type form a 'BooleanAlgebra'.
instance Ord a => BooleanAlgebra (FiniteSet a) where
    complement =
        setComplement


-- | Finite and cofinite sets over the elements of a finite type.
instance (Bounded a, Enum a, Ord a) => GSet a where
    type Set a = FiniteSet a

    singleton =
        These . Data.Set.singleton

    member a (These s) =
        Data.Set.member a s
    member a (ComplementOf s) =
        Data.Set.notMember a s

    choose (These s) =
        Data.Set.lookupMin s
    choose p@(ComplementOf _) =
        if size p == 0 then
            Nothing
        else
            Just $ head [a | a <- [minBound..maxBound], member a p]



-- * Implementation of sets with a more efficient complement operation.

-- | Finite and cofinite sets over the elements of a type.
data FiniteSet a
    -- | Set containing the given elements.
    = These (Data.Set.Set a)

    -- | Set containing the complement of the given elements.
    | ComplementOf (Data.Set.Set a)


-- | Equality of finite and cofinite subsets of a finite type is decidable.
instance (Bounded a, Enum a, Ord a) => Eq (FiniteSet a) where
    These s1 == These s2 =
        s1 == s2
    p1@(These s1) == p2@(ComplementOf s2) =
         size p1 == size p2 && Data.Set.null (s1 `Data.Set.intersection` s2)
    p1@(ComplementOf _) == p2@(These _) =
        p2 == p1
    ComplementOf s1 == ComplementOf s2 =
        s1 == s2


-- | We can totally order the finite and cofinite subsets of a finite type.
instance forall a.(Bounded a, Enum a, Ord a) => Ord (FiniteSet a) where
    -- | Order by size first; then use lexicographical order on the elements.
    compare p1 p2 =
        compare (size p1) (size p2) <> lex p1 p2
        where
            lex (ComplementOf s1) (ComplementOf s2) =
                -- This is a lot more efficient than turning complemented
                -- sets into lists. Note that the order of arguments to the
                -- comparison is reversed.
                (compare `on` Data.Set.toAscList) s2 s1
            lex _ _ =
                (compare `on` toList) p1 p2


-- | Nicer interface for inputting finite sets over 'Char'.
instance IsString (FiniteSet Char) where
    fromString =
        These . Data.Set.fromList


-- | Allows us to write finite sets as lists.
instance (Bounded a, Enum a, Ord a) => IsList (FiniteSet a) where
    type (Item (FiniteSet a)) = a

    fromList =
        These . Data.Set.fromList

    -- | We can list all elements in a finite or cofinite subset of
    -- a finite type. For infinite types, size of cofinite subsets
    -- is infinite, so this is not possible.
    toList (These s) =
        Data.Set.toAscList s
    toList (ComplementOf s) =
        [a | a <- [minBound..maxBound], Data.Set.notMember a s]


instance Show a => Show (FiniteSet a) where
    show (These s) =
        "{" ++ intercalate "," (map show $ Data.Set.toList s) ++ "}"
    show (ComplementOf s) | Data.Set.null s =
        "."
    show (ComplementOf s) =
        "~{" ++ intercalate "," (map show $ Data.Set.toList s) ++ "}"


instance (Read a, Ord a) => Read (FiniteSet a) where
    readsPrec _ =
        Parser.readP_to_S parser

        where
            parser :: Parser.ReadP (FiniteSet a)
            parser = do
                Parser.skipSpaces
                Parser.choice
                    [ do {Parser.char '.'; return one}
                    , do {Parser.char '~'; fmap ComplementOf elements}
                    , do {fmap These elements}
                    ]

            elements :: Parser.ReadP (Data.Set.Set a)
            elements =
                Parser.between openBrace closeBrace $ do
                    elements <- Parser.sepBy (Parser.readS_to_P reads) comma
                    return $ Data.Set.fromList elements

            openBrace = do
                Parser.char '{'
                Parser.skipSpaces

            closeBrace = do
                Parser.skipSpaces
                Parser.char '}'

            comma = do
                Parser.char ','
                Parser.skipSpaces


-- | Set containing no elements.
empty :: FiniteSet a
empty =
    These Data.Set.empty


-- | Set containing all elements.
full :: FiniteSet a
full =
    ComplementOf Data.Set.empty


-- | Complement of a set.
setComplement :: FiniteSet a -> FiniteSet a
setComplement (These s) =
    ComplementOf s
setComplement (ComplementOf s) =
    These s


-- | Intersection of two sets.
intersection :: Ord a => FiniteSet a -> FiniteSet a -> FiniteSet a
intersection (These s1) (These s2) =
    These (Data.Set.intersection s1 s2)
intersection (These s1) (ComplementOf s2) =
    These (Data.Set.difference s1 s2)
intersection p1@(ComplementOf _) p2@(These _) =
    intersection p2 p1
intersection(ComplementOf s1) (ComplementOf s2) =
    ComplementOf (Data.Set.union s1 s2)


-- | Intersection of two sets.
union :: Ord a => FiniteSet a -> FiniteSet a -> FiniteSet a
union p1 p2 =
    complement $ (complement p1) `intersection` (complement p2)



-- * Operations on finite types

-- | Number of elements in a finite type.
sizeOfType :: forall a. (Bounded a, Enum a) => a -> Int
sizeOfType _ =
    1 + fromEnum (maxBound :: a) - fromEnum (minBound :: a)


-- | We can compute the size of finite or cofinite subsets of
-- a finite type. For infinite types, size of cofinite subsets
-- is infinite.
size :: forall a. (Bounded a, Enum a) => FiniteSet a -> Int
size (These s) =
    Data.Set.size s
size (ComplementOf s) =
    sizeOfType (undefined :: a) - Data.Set.size s



-- * Testing

instance (Arbitrary a, Ord a) => Arbitrary (FiniteSet a) where
    arbitrary = do
        complemented <- arbitrary
        set <- arbitrary
        case complemented of
            False ->
                return (These set)

            True ->
                return (ComplementOf set)

    shrink (These s) =
        fmap These (shrink s)
    shrink (ComplementOf s) =
        fmap These (shrink s) ++ fmap ComplementOf (shrink s)


-- | We use a newtype to define a 'Serial' instance for 'Data.Set.Set'
-- so we don't pollute the global class space.
newtype Set' a =
    Set' {unSet' :: Data.Set.Set a}

instance (Serial m a, Enum a, Bounded a, Ord a) => Serial m (Set' a) where
    series = SmallCheck.generate $ \depth ->
        Data.Set.toList allSubsets
            |> filter ((<= depth) . Data.Set.size)
            |> fmap Set'
        where
            allSubsets =
                ([minBound .. maxBound] :: [a])
                    |> Data.Set.fromList
                    |> Data.Set.powerSet

instance (Serial m a, Enum a, Bounded a, Ord a) => Serial m (FiniteSet a) where
    series =
        cons1 (These . unSet') \/ cons1 (ComplementOf . unSet')
