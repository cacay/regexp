{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}


-- | Definition of regular expressions over /character classes/
-- (i.e. sets of characters from an arbitrary type). The definition
-- is left abstract, which frees us to simplify regular expressions
-- using (sound) rewriting rules. We normalize regular expressions
-- enough to guarantee that the set of Brzozowski derivatives are
-- finite.
module RegExp.RegExp
    ( CharacterClass
    , RegExp

    -- * Deconstructing regular expressions
    , RegExpView(..)
    , view
    , hide

    -- * Properties
    , nullable
    , empty

    -- * #combining# Combining regular expressions
    , rZero
    , rOne
    , rPlus
    , rTimes
    , rStar
    , rLiteral
    ) where

import Control.Exception.Base(assert)
import Unsafe.Coerce(unsafeCoerce)

import Data.Singletons
import Data.Singletons.Decide
import Prelude.Singletons

import Data.Set(Set)
import qualified Data.Set as Set

import Data.Either (isRight)
import qualified Data.List as List
import Data.String (IsString(..))
import qualified Text.ParserCombinators.ReadP as Parser

import Data.GSet (GSet)
import qualified Data.GSet as GSet
import Data.Semiring (Semiring(..))

import Test.QuickCheck as QuickCheck
import Test.SmallCheck.Series as SmallCheck


-- | Sets of characters from an alphabet 'c'.
type CharacterClass c =
    GSet.Set c


-- | Regular expressions that support character classes over an alphabet
-- @c@ (so we don't have to encode them using choice). The type
-- is left abstract so we can apply rewriting rules to simplify and
-- normalize expressions. Refer to 'view' and 'RegExpView' for
-- inspecting 'RegExp', and to 'hide' and [the relevant section](#combining)
-- for constructing them.
--
-- Normalizing expressions not only makes them smaller and more
-- readable, but also ensures termination for some algorithms, so
-- it is a good idea overall. We normalize with respect to the
-- following equations:
--
-- == Associativity, Commutativity, and Idempotence of @+@ (ACI)
--
-- prop> (r + s) + t = r + (s + t)
-- prop> r + s = s + t
-- prop> r + r = r
--
-- == Identity for @+@
--
-- prop> 0 + r = r
--
-- == Associativity of @.@
--
-- prop> (r . s) . t = r . (s . t)
--
-- == Identity and Annihilator for @.@
--
-- prop> 1 . r = r = r . 1
-- prop> 0 . r = 0 = r . 0
--
-- == Star
--
-- prop> (r*)* = r*
-- prop> 0* = 1
-- prop> 1* = 1
--
-- In addition, we keep regular expressions in strong star normal form
-- which is described in
-- [Simplifying Regular Expressions A Quantitative Perspective](https://pdfs.semanticscholar.org/1b6b/5843442a64523ccb7afd21eabec7881b4219.pdf).
-- In practice, this means @*@ is only applied to expression that
-- cannot match the empty word.
--
-- Brzozowski proved that normalizing with respect to ACI ensures
-- there are only finitely many derivatives of a regular expression.
-- So ACI is necessary for any algorithm that relies on taking repeated
-- derivatives of regular expressions.
data RegExp c where
    RZero :: RegExp c
    ROne  :: RegExp c
    RNormalized :: (NormalizedRegExp c isUnion isSeq isNullable) -> RegExp c

-- | Syntactic equality.
instance GSet c => Eq (RegExp c) where
    RZero == RZero =
        True
    ROne == ROne =
        True
    RNormalized r1 == RNormalized r2 =
        r1 `hEq` r2
    _ == _ =
        False

-- | An arbitrary syntactic ordering. Useful for defining sets and
-- maps over regular expressions.
instance (GSet c, Ord (CharacterClass c)) => Ord (RegExp c) where
    compare RZero RZero =
        EQ
    compare RZero _ =
        LT
    compare _ RZero =
        GT

    compare ROne ROne =
        EQ
    compare ROne _ =
        LT
    compare _ ROne =
        GT

    compare (RNormalized r1) (RNormalized r2) =
        r1 `hCompare` r2

-- | Nicer interface for inputting regular expression over 'Char'.
-- For example,
--
-- > "abc" :: 'RegExp' 'Char'
--
-- is the regular expression that matches single character strings
-- @"a"@, @"b"@, and @"c"@ (it doesn't match the string @"abc"@).
instance IsString (RegExp Char) where
    fromString =
        rLiteral . fromString



-- * Deconstructing regular expressions

-- | Standard syntax for regular expressions. We omit @Zero@ since
-- it can be encoded as @'Literal' 'zero'@.
data RegExpView c r where
    -- | Match the empty string and nothing else.
    One :: RegExpView c r

    -- | Match the left or the right expression.
    Plus :: r -> r -> RegExpView c r

    -- | Match the left then the right expression.
    Times :: r -> r -> RegExpView c r

    -- | Match zero or more copies of the given expression.
    Star :: r -> RegExpView c r

    -- | Match any character in the character class. The character
    -- class might be empty, in which case this matches no strings.
    Literal :: CharacterClass c -> RegExpView c r

deriving instance Functor (RegExpView c)



-- | Expose the abstract type 'RegExp' as a 'RegExpView'.
view :: forall c. GSet c => RegExp c -> RegExpView c (RegExp c)
view RZero =
    Literal zero
view ROne =
    One
view (RNormalized r) =
    view' r
    where
        view' :: NormalizedRegExp c isUnion isSeq isNullable
              -> RegExpView c (RegExp c)
        view' (NUnion p n s) | p /= zero, Set.null n, Set.null s =
            Literal p
        view' (NUnion p n s) | p /= zero =
            nUnion p Set.empty Set.empty `Plus` nUnion zero n s
        view' (NUnion _ n s) | otherwise =
            case (Set.minView n, Set.minView s) of
                (Nothing, Nothing) ->
                    error "impossible"

                (Just (SubUnion r, n), _) ->
                    RNormalized r `Plus` nUnion zero n s

                (Nothing, Just (SubUnion r, s)) ->
                    RNormalized r `Plus` nUnion zero Set.empty s

        view' (NUnionWithOne p s) =
            ROne `Plus` nUnion p Set.empty s

        view' (NSeq l) | Some1 (SubSeq r1) ::: (Some1 l')  <- nSeqView l
                       , Some1 (SubSeq r2) ::: (Some1 l'') <- nSeqView l'
                       , Nil <- nSeqView l'' =
            RNormalized r1 `Times` RNormalized r2
        view' (NSeq l) | Some1 (SubSeq r1) ::: Some1 l' <- nSeqView l =
            RNormalized r1 `Times` RNormalized (NSeq l')
        view' (NSeq l) | otherwise =
            error "impossible"

        view' (NStar r) =
            Star (RNormalized r)


-- | Pack the public view 'RegExpView' back into the abstract view 'RegExp'.
hide :: GSet c => RegExpView c (RegExp c) -> RegExp c
hide One =
    rOne
hide (Plus r1 r2) =
    rPlus r1 r2
hide (Times r1 r2) =
    rTimes r1 r2
hide (Star r) =
    rStar r
hide (Literal p) =
    rLiteral p



-- * Properties

-- | 'True' if and only if the regular expression can match the
-- empty word.
nullable :: GSet c => RegExp c -> Bool
nullable RZero =
    False
nullable ROne =
    True
nullable (RNormalized r) =
    isRight (nullableNormalized r)


-- | 'True' if and only if the regular expression matches no words.
empty :: RegExp c -> Bool
empty RZero =
    True
empty _ =
    False



-- * Normalized regular expressions

-- | We define a type of /normalized regular expressions/ to help us
-- statically ensure the properties described in 'RexExp'. Terms of this
-- type denote expressions that
-- 1. are fully normalized with respect to the rewriting rules in 'RegExp',
-- 2. are in strong star normal form,
-- 3. know whether they are nullable (i.e. we can determine in constant time
--    whether they can match the empty word or not).
--
-- (1) and (2) are direct requirements. (3) helps us specify when a regular
-- expression is in star normal form. Additionally, being able to compute
-- nullability in constant time speeds up derivative based algorithms.
--
-- To enforce these requirements, we use data structures that intrinsically
-- capture the required properties. For example, instead of using binary
-- unions, we define unions over /sets/ of subexpressions since sets capture
-- associativity, commutativity, and idempotence. Similarly, we use lists
-- for sequencing so we get associativity automatically.
--
-- Normalized expressions are indexed based on whether the root constructor
-- is a union or a sequence so we can statically disallow nesting unions
-- under unions (since they can be combined into one) and similarly for
-- sequencing. There is an additional index to track whether the expression
-- is nullable.
--
-- Normalized expressions cannot encode the regular expressions that matches
-- no words (i.e. @Zero@) or the regular expression that only matches the
-- empty words (i.e. @One@). These are added by 'RegExp'. This is in line
-- with the development in
-- /Simplifying Regular Expressions A Quantitative Perspective/.
data NormalizedRegExp c (isUnion :: Bool) (isSeq :: Bool) (isNullable :: Bool) where
    -- | Union of a literal (a character set) and a set of subexpressions.
    -- Note that we disallow standalone literal nodes under unions and
    -- instead bundle them with the union nodes themselves to ensure we
    -- combine literals using set union instead of syntactic regular expression
    -- union. This gives an additional level of normalization.
    --
    -- We do not have a separate case for literals since they can be
    -- represented as a union node with an empty set of subexpressions.
    --
    -- We keep nullable and strict (non-nullable) subexpressions separate to
    -- satisfy requirement (3): a union node is nullable if the set of
    -- nullable subexpressions is not empty. This is checked dynamically.
    --
    -- To satisfy (1) and (2), we require that for every @NUnion p n s@, the
    -- following should hold:

    -- @p /= zero || 'length' n + 'length' s >= 2@.
    --
    -- Additionally, 'NUnion' and 'NUnionWithOne' should not occur as
    -- subexpressions since these can be hoisted up.
    NUnion :: CharacterClass c
           -> Set (SubUnion c True)
           -> Set (SubUnion c False)
           -> NormalizedRegExp c True False isNullable

    -- | The empty word or a union. This corresponds to the @?@ constructor
    -- from the paper, but generalized over a union of subexpressions
    -- (as opposed to a single expression) so that expressions like @a? + b?@
    -- get simplified to @(a + b)?@.
    --
    -- For every, @NUnionWithOne p s@ we require that
    -- @p /= zero || 'length' s >= 1@ and @s@ does not contain 'NUnion' or
    -- 'NUnionWithOne'.
    NUnionWithOne :: CharacterClass c
                  -> Set (SubUnion c False)
                  -> NormalizedRegExp c True False True


    -- | Sequential composition of a list of subexpressions. Each cons node
    -- in the list needs to store whether the sequential composition of that
    -- and the following nodes are nullable or not in order to satisfy (3).
    --
    -- The list must contain at least two elements and 'NSeq' nodes cannot
    -- appear as subexpression.
    NSeq :: NSeq c isNullable
         -> NormalizedRegExp c False True isNullable

    -- | Iteration. The iterated expression cannot be nullable, but the
    -- overall expression always is.
    NStar :: NormalizedRegExp c isUnion isSeq False
          -> NormalizedRegExp c False False True


-- | Normalized regular expressions that can appear under a union node.
data SubUnion c (isNullable :: Bool) where
    SubUnion :: !(NormalizedRegExp c False isSeq isNullable)
             -> SubUnion c isNullable


-- | Normalized regular expressions that can appear under a seq node.
data SubSeq c (isNullable :: Bool) where
    SubSeq :: !(NormalizedRegExp c isUnion False isNullable)
           -> SubSeq c isNullable


-- | Sequential composition of a list of subexpressions. Each node
-- in the sequence keeps track of whether the subsequence starting
-- with that element is nullable.
data NSeq c (isNullable :: Bool) where
    -- | Empty list. Nullable since it corresponds to @One@.
    NSeqNil :: NSeq c True

    -- | Tack on a nullable subexpression. The result is nullable if
    -- and only if the rest of the list is.
    NSeqConsNullable :: Sing (isNullable :: Bool)
                     -> SubSeq c True
                     -> NSeq c isNullable
                     -> NSeq c isNullable

    -- | Tack on a strict (non-nullable) subexpression. The result
    -- is always strict.
    NSeqConsStrict :: SubSeq c False
                   -> NSeq c isNullable
                   -> NSeq c False



-- * Smart constructors to check invariants we cannot encode statically.


-- | Compute the union of the given sets of subexpressions.
-- This constructor is always safe: it will always construct
-- a valid expression, and it will always "do the right thing".
nUnion :: GSet c
       => CharacterClass c
       -> Set (SubUnion c True)
       -> Set (SubUnion c False)
       -> RegExp c
nUnion p n s | p /= zero || Set.size n + Set.size s >= 2 =
    if Set.null n then
        RNormalized (nUnionStrict p s)
    else
        RNormalized (nUnionNullable p n s)
nUnion _ n s | otherwise =
    case (Set.lookupMin n, Set.lookupMin s) of
        (Nothing, Nothing) ->
            RZero

        (Just (SubUnion r), Nothing) ->
            RNormalized r

        (Nothing, Just (SubUnion r)) ->
            RNormalized r

        (Just _, Just _) ->
            error "impossible"


-- | Safe and smart constructor for 'NUnion' that always returns a
-- nullable expression.
nUnionNullable :: GSet c
               => CharacterClass c
               -> Set (SubUnion c True)
               -> Set (SubUnion c False)
               -> NormalizedRegExp c True False True
nUnionNullable p n s =
    assert (not $ Set.null n) $
    assert (p /= zero || Set.size n + Set.size s >= 2) $
    NUnion p n s


-- | Safe and smart constructor for 'NUnion' that always returns a
-- non-nullable expression.
nUnionStrict :: GSet c
             => CharacterClass c
             -> Set (SubUnion c False)
             -> NormalizedRegExp c True False False
nUnionStrict p s =
    assert (p /= zero || Set.size s >= 2) $
    NUnion p Set.empty s


-- | Safe and smart constructor for 'NUnionWithOne'.
nUnionWithOne :: GSet c
              => CharacterClass c
              -> Set (SubUnion c False)
              -> NormalizedRegExp c True False True
nUnionWithOne p s =
    assert (p /= zero || Set.size s >= 1) $
    NUnionWithOne p s


-- | Safe and smart constructor for 'NSeq'.
nSeq :: GSet c
     => NSeq c isNullable
     -> NormalizedRegExp c False True isNullable
nSeq l =
    assert (isValid l) $
    NSeq l
    where
        -- | Check that the list has at least two subexpressions.
        isValid NSeqNil =
            False
        isValid (NSeqConsNullable _ _ NSeqNil) =
            False
        isValid (NSeqConsStrict _ NSeqNil) =
            False
        isValid _ =
            True


-- | Alias for 'NStar' for uniformity.
nStar :: GSet c
      => NormalizedRegExp c isUnion isSeq False
      -> NormalizedRegExp c False False True
nStar =
    NStar



-- * Working with normalized expressions

nullableNormalized :: GSet c
                   => NormalizedRegExp c isUnion isSeq isNullable
                   -> Either (isNullable :~: False) (isNullable :~: True)
nullableNormalized (NUnion _ n _)=
    if Set.null n then
        Left (unsafeCoerce Refl)
    else
        Right (unsafeCoerce Refl)
nullableNormalized (NUnionWithOne _ _) =
    Right Refl
nullableNormalized (NSeq l) =
    nullableNSeq l
nullableNormalized (NStar _) =
    Right Refl


nullableNSeq :: NSeq c isNullable
             -> Either (isNullable :~: False) (isNullable :~: True)
nullableNSeq NSeqNil =
    Right Refl
nullableNSeq (NSeqConsNullable SFalse _ _) =
    Left Refl
nullableNSeq (NSeqConsNullable STrue _ _) =
    Right Refl
nullableNSeq (NSeqConsStrict _ _) =
    Left Refl



-- | View 'NSeq' as a list.
nSeqView :: NSeq c isNullable
         -> ListView (Some1 (NSeq c)) (Some1 (SubSeq c))
nSeqView NSeqNil =
    Nil
nSeqView (NSeqConsNullable _ h t) =
    Some1 h ::: (Some1 t)
nSeqView (NSeqConsStrict h t) =
    Some1 h ::: (Some1 t)


-- | Construct an 'NSeq' that contains a single subexpression.
nSeqSingleton :: GSet c => SubSeq c isNullable -> Some1 (NSeq c)
nSeqSingleton r@(SubSeq n) =
    case nullableNormalized n of
        Left Refl  ->
            Some1 $ NSeqConsStrict r NSeqNil

        Right Refl ->
            Some1 $ NSeqConsNullable STrue r NSeqNil


-- | Append two 'NSeq's.
nSeqAppend :: NSeq c isNullable1
           -> NSeq c isNullable2
           -> NSeq c (isNullable1 && isNullable2)
nSeqAppend NSeqNil l2 =
    l2
nSeqAppend (NSeqConsNullable SFalse h1 t1) l2 =
    NSeqConsNullable SFalse h1 (nSeqAppend t1 l2)
nSeqAppend (NSeqConsNullable STrue h1 t1) l2 =
    case nullableNSeq l2 of
        Left Refl ->
            NSeqConsNullable SFalse h1 (nSeqAppend t1 l2)
        Right Refl ->
            NSeqConsNullable STrue h1 (nSeqAppend t1 l2)
nSeqAppend (NSeqConsStrict h1 t1) l2 =
    NSeqConsStrict h1 (nSeqAppend t1 l2)



-- * Comparing normalized expressions

-- GHC cannot derive 'Eq' and 'Ord' instances for normalized regular
-- expressions because of all the existential quantification going
-- on. Since we only care about ordering so we can put expression
-- in sets, we define ordering on the underlying untyped terms. We
-- do this efficiently by defining heterogeneous equality and comparison.

-- | Heterogeneous equality.
class HEq a b where
    hEq :: a -> b -> Bool


-- | Heterogeneous ordering.
class HOrd a b where
    hCompare :: a -> b -> Ordering


instance GSet c => HEq (NormalizedRegExp c u1 s1 n1) (NormalizedRegExp c u2 s2 n2) where
    hEq (NUnion p1 n1 s1) (NUnion p2 n2 s2) =
        p1 == p2 && n1 == n2 && s1 == s2
    hEq (NUnionWithOne p1 s1) (NUnionWithOne p2 s2) =
        p1 == p2 && s1 == s2
    hEq (NSeq l1) (NSeq l2) =
        l1 `hEq` l2
    hEq (NStar r1) (NStar r2) =
        r1 `hEq` r2
    hEq _ _ =
        False

instance GSet c => HEq (SubUnion c n1) (SubUnion c n2) where
    hEq (SubUnion r1) (SubUnion r2) =
        r1 `hEq` r2

instance GSet c => HEq (SubSeq c n1) (SubSeq c n2) where
    hEq (SubSeq r1) (SubSeq r2) =
        r1 `hEq` r2

instance GSet c => HEq (NSeq c n1) (NSeq c n2) where
    hEq NSeqNil NSeqNil =
        True
    hEq (NSeqConsNullable n1 h1 t1) (NSeqConsNullable n2 h2 t2) =
        fromSing n1 == fromSing n2 && h1 `hEq` h2 && t1 `hEq` t2
    hEq (NSeqConsStrict h1 t1) (NSeqConsStrict h2 t2) =
        h1 `hEq` h2 && t1 `hEq` t2
    hEq _ _ =
        False


instance GSet c => Eq (NormalizedRegExp c isUnion isSeq isNullable) where
    (==) = hEq

instance GSet c => Eq (SubUnion c isNullable) where
    (==) = hEq

instance GSet c => Eq (SubSeq c isNullable) where
    (==) = hEq

instance GSet c => Eq (NSeq c isNullable) where
    (==) = hEq



instance (GSet c, Ord (CharacterClass c)) => HOrd (NormalizedRegExp c u1 s1 n1) (NormalizedRegExp c u2 s2 n2) where
    hCompare (NUnion p1 n1 s1) (NUnion p2 n2 s2) =
        p1 `compare` p2 <> n1 `compare` n2 <> s1 `compare` s2
    hCompare (NUnion _ _ _) _ =
        LT
    hCompare _ (NUnion _ _ _) =
        GT

    hCompare (NUnionWithOne p1 s1) (NUnionWithOne p2 s2) =
        p1 `compare` p2 <> s1 `compare` s2
    hCompare (NUnionWithOne _ _) _ =
        LT
    hCompare _ (NUnionWithOne _ _) =
        GT

    hCompare (NSeq l1) (NSeq l2) =
        l1 `hCompare` l2
    hCompare (NSeq _) _ =
        LT
    hCompare _ (NSeq _) =
        GT

    hCompare (NStar r1) (NStar r2) =
        r1 `hCompare` r2

instance (GSet c, Ord (CharacterClass c)) => HOrd (SubUnion c n1) (SubUnion c n2) where
    hCompare (SubUnion r1) (SubUnion r2) =
        r1 `hCompare` r2

instance (GSet c, Ord (CharacterClass c)) => HOrd (SubSeq c n1) (SubSeq c n2) where
    hCompare (SubSeq r1) (SubSeq r2) =
        r1 `hCompare` r2

instance (GSet c, Ord (CharacterClass c)) => HOrd (NSeq c n1) (NSeq c n2) where
    hCompare NSeqNil NSeqNil =
        EQ
    hCompare NSeqNil _ =
        LT
    hCompare _ NSeqNil =
        GT

    hCompare (NSeqConsNullable n1 h1 t1) (NSeqConsNullable n2 h2 t2) =
        fromSing n1 `compare` fromSing n2 <> h1 `hCompare` h2 <> t1 `hCompare` t2
    hCompare (NSeqConsNullable _ _ _) _ =
        LT
    hCompare _ (NSeqConsNullable _ _ _) =
        GT

    hCompare (NSeqConsStrict h1 t1) (NSeqConsStrict h2 t2) =
        h1 `hCompare` h2 <> t1 `hCompare` t2


instance (GSet c, Ord (CharacterClass c)) => Ord (NormalizedRegExp c isUnion isSeq isNullable) where
    compare = hCompare

instance (GSet c, Ord (CharacterClass c)) => Ord (SubUnion c isNullable) where
    compare = hCompare

instance (GSet c, Ord (CharacterClass c)) => Ord (SubSeq c isNullable) where
    compare = hCompare

instance (GSet c, Ord (CharacterClass c)) => Ord (NSeq c isNullable) where
    compare = hCompare



-- * Constructing and combining regular expressions

-- | Regular expression that matches no strings.
rZero :: RegExp c
rZero =
    RZero


-- | Regular expression that matches the empty string and nothing else.
rOne :: RegExp c
rOne =
    ROne


-- | Regular expression that matches strings that either regular expression
-- matches.
rPlus :: forall c. GSet c => RegExp c -> RegExp c -> RegExp c
rPlus RZero r2 =
    r2
rPlus r1 RZero =
    r1

rPlus ROne ROne =
    ROne
rPlus ROne result@(RNormalized r2) =
    case nullableNormalized r2 of
        Left Refl ->
            case r2 of
                NUnion p2 n2 s2 ->
                    assert (Set.null n2) $
                    RNormalized $ nUnionWithOne p2 s2

                NSeq _ ->
                    RNormalized $ nUnionWithOne zero (Set.singleton $ SubUnion r2)

        Right Refl ->
            result
rPlus r1 ROne =
    rPlus ROne r1

rPlus (RNormalized r1) (RNormalized r2) =
    rPlus' r1 r2
    where
        rPlus' :: NormalizedRegExp c isUnion1 isSeq1 isNullable1
               -> NormalizedRegExp c isUnion2 isSeq2 isNullable2
               -> RegExp c
        rPlus' (NUnion p1 n1 s1) (NUnion p2 n2 s2) =
            nUnion (p1 <+> p2) (Set.union n1 n2) (Set.union s1 s2)
        rPlus' (NUnion p1 n1 s1) (NUnionWithOne p2 s2) | Set.null n1 =
            RNormalized $
                nUnionWithOne (p1 <+> p2) (Set.union s1 s2)
        rPlus' (NUnion p1 n1 s1) (NUnionWithOne p2 s2) | otherwise =
            RNormalized $
                nUnionNullable (p1 <+> p2) n1 (Set.union s1 s2)
        rPlus' (NUnion p1 n1 s1) r2@(NSeq _) =
            case nullableNormalized r2 of
                Left Refl ->
                    nUnion p1 n1 (Set.insert (SubUnion r2) s1)

                Right Refl ->
                    nUnion p1 (Set.insert (SubUnion r2) n1) s1
        rPlus' (NUnion p1 n1 s1) r2@(NStar _) =
            nUnion p1 (Set.insert (SubUnion r2) n1) s1
        rPlus' r1 r2@(NUnion _ _ _) =
            rPlus' r2 r1

        rPlus' (NUnionWithOne p1 s1) (NUnionWithOne p2 s2) =
            RNormalized $
                nUnionWithOne (p1 <+> p2) (Set.union s1 s2)
        rPlus' (NUnionWithOne p1 s1) r2@(NSeq _) =
            case nullableNormalized r2 of
                Left Refl ->
                    RNormalized $
                        nUnionWithOne p1 (Set.insert (SubUnion r2) s1)

                Right Refl ->
                    nUnion p1 (Set.singleton $ SubUnion r2) s1
        rPlus' (NUnionWithOne p1 s1) r2@(NStar _) =
            nUnion p1 (Set.singleton $ SubUnion r2) s1
        rPlus' r1 r2@(NUnionWithOne _ _) =
            rPlus' r2 r1

        rPlus' r1@(NSeq _) r2@(NSeq _) =
            rPlusNotUnion r1 r2
        rPlus' r1@(NSeq _) r2@(NStar _) =
            rPlusNotUnion r1 r2
        rPlus' r1@(NStar _) r2@(NSeq _) =
            rPlusNotUnion r1 r2
        rPlus' r1@(NStar _) r2@(NStar _) =
            rPlusNotUnion r1 r2


        rPlusNotUnion :: NormalizedRegExp c False isSeq1 isNullable1
                      -> NormalizedRegExp c False isSeq2 isNullable2
                      -> RegExp c
        rPlusNotUnion r1 r2 | r1 `hEq` r2 =
            RNormalized r1
        rPlusNotUnion r1 r2 | otherwise  =
            case (nullableNormalized r1, nullableNormalized r2) of
                (Right Refl, Right Refl) ->
                    RNormalized $
                        nUnionNullable zero (Set.fromList [SubUnion r1, SubUnion r2]) Set.empty

                (Right Refl, Left Refl) ->
                    RNormalized $
                        nUnionNullable zero (Set.singleton $ SubUnion r1) (Set.singleton $ SubUnion r2)

                (Left Refl, Right Refl) ->
                    RNormalized $
                        nUnionNullable zero (Set.singleton $ SubUnion r2) (Set.singleton $ SubUnion r1)

                (Left Refl, Left Refl) ->
                    RNormalized $
                        nUnionStrict zero (Set.fromList [SubUnion r1, SubUnion r2])


-- | Regular expression that matches the first expression followed
-- by the second.
rTimes :: forall c. GSet c => RegExp c -> RegExp c -> RegExp c
rTimes RZero _ =
    RZero
rTimes _ RZero =
    RZero

rTimes ROne r2 =
    r2
rTimes r1 ROne =
    r1

rTimes (RNormalized r1) (RNormalized r2) =
    case (isSeq r1, isSeq r2) of
        (Left Refl, Left Refl) ->
            case (nSeqSingleton $ SubSeq r1, nSeqSingleton $ SubSeq r2) of
                (Some1 l1, Some1 l2) ->
                    RNormalized $ NSeq (l1 `nSeqAppend` l2)

        (Right Refl, Left Refl) | NSeq l1 <- r1 ->
            case nSeqSingleton (SubSeq r2) of
                Some1 l2 ->
                    RNormalized $ NSeq (l1 `nSeqAppend` l2)

        (Left Refl, Right Refl) | NSeq l2 <- r2 ->
            case nSeqSingleton (SubSeq r1) of
                Some1 l1 ->
                    RNormalized $ NSeq (l1 `nSeqAppend` l2)

        (Right Refl, Right Refl) | NSeq l1 <- r1
                                 , NSeq l2 <- r2 ->
            RNormalized $ NSeq (l1 `nSeqAppend` l2)
    where
        isSeq :: NormalizedRegExp c isUnion isSeq isNullable
                 -> Either (isSeq :~: False) (isSeq :~: True)
        isSeq (NUnion _ _ _) =
            Left Refl
        isSeq (NUnionWithOne _ _) =
            Left Refl
        isSeq (NSeq _) =
            Right Refl
        isSeq (NStar _) =
            Left Refl


-- | Regular expression that matches zero or more copies of the given
-- expression.
rStar :: forall c. GSet c => RegExp c -> RegExp c
rStar RZero =
    ROne
rStar ROne =
    ROne
rStar r@(RNormalized (NStar _)) = -- Optimize a common case
    r
rStar (RNormalized r) =
    case nullableNormalized r of
        Left Refl ->
            RNormalized $ nStar r

        Right Refl | (p, s) <- removeOne r ->
            if p /= zero || Set.size s >= 2 then
                RNormalized $ nStar (nUnionStrict p s)
            else
                assert (p == zero && Set.size s == 1) $
                case Set.findMin s of
                    SubUnion r ->
                        RNormalized $ nStar r
    where
        -- | If @removeOne r = r'@, then @r* = (uncurry nUnionStrict r')*@.
        removeOne :: NormalizedRegExp c isUnion isSeq True
                  -> (CharacterClass c, Set (SubUnion c False))
        removeOne (NUnion p n s) =
            List.foldl' merge (p, s) n'
            where
                n' = fmap (\(SubUnion r) -> removeOne r) (Set.toList n)
        removeOne (NUnionWithOne p s) =
            (p, s)
        removeOne (NSeq NSeqNil) =
            (zero, Set.empty)
        removeOne (NSeq (NSeqConsNullable STrue (SubSeq r) t)) =
            removeOne r `merge` removeOne (NSeq t)
        removeOne (NStar (NUnion p n s)) =
            assert (Set.null n) $
            (p, s)
        removeOne (NStar r@(NSeq l)) =
            (zero, Set.singleton (SubUnion  r))

        -- | Combine two strict union components.
        merge :: (CharacterClass c, Set (SubUnion c False))
              -> (CharacterClass c, Set (SubUnion c False))
              -> (CharacterClass c, Set (SubUnion c False))
        merge (p1, s1) (p2, s2) =
            (p1 <+> p2, s1 `Set.union` s2)


-- | Regular expression that matches single character strings picked
-- from the given character class.
rLiteral :: forall c. GSet c => CharacterClass c -> RegExp c
rLiteral p | p == zero =
    RZero
rLiteral p | otherwise =
    nUnion p Set.empty Set.empty


-- * Printing

instance (GSet c, Show (CharacterClass c)) => Show (RegExp c) where
    showsPrec d RZero =
        showString "{}"

    showsPrec d ROne =
        showString "<>"

    showsPrec d (RNormalized r) =
        showsPrec d r


instance (GSet c, Show (CharacterClass c), Show r) => Show (RegExpView c r) where
    showsPrec _ One =
        showString "<>"
    showsPrec d (Plus r1 r2) =
        showParen (d > plusPrec) $
        showsPrec plusPrec r1 . showString " ++ " . showsPrec plusPrec r2
        where
            plusPrec = 9
    showsPrec d (Times r1 r2) =
        showParen (d > timesPrec) $
        showsPrec timesPrec r1 . showString "##" . showsPrec timesPrec r2
        where
            timesPrec = 10
    showsPrec d (Star r) =
        showParen (d > starPrec) $
        showsPrec starPrec r . showString "**"
        where
            starPrec = 11
    showsPrec d (Literal p) =
        showsPrec d p


instance (GSet c, Show (CharacterClass c)) => Show (NormalizedRegExp c isUnion isSeq isNullable) where
    showsPrec d (NUnion p n s) =
        showUnion d p (n' ++ s')
        where
            n' = fmap Some1 (Set.toList n)
            s' = fmap Some1 (Set.toList s)

    showsPrec d (NUnionWithOne p s) =
        showParen (d > unionWithOnePrec) $
            showUnion unionWithOnePrec p s' . showString "?"
        where
            unionWithOnePrec = 8
            s' = fmap Some1 (Set.toList s)

    showsPrec d (NSeq l) =
        showParen (d > seqPrec) $
            intercalate (showString "#") (toList l)
        where
            seqPrec = 7

            toList :: NSeq c n -> [ShowS]
            toList NSeqNil =
                []
            toList (NSeqConsNullable _ h t) =
                showsPrec seqPrec h : toList t
            toList (NSeqConsStrict h t) =
                showsPrec seqPrec h : toList t

    showsPrec d (NStar r) =
        showParen (d > starPrec) $
            showsPrec starPrec r . showString "*"
        where
            starPrec = 8


instance (GSet c, Show (CharacterClass c)) => Show (SubUnion c isNullable) where
    showsPrec d (SubUnion r) =
        showsPrec d r


instance (GSet c, Show (CharacterClass c)) => Show (SubSeq c isNullable) where
    showsPrec d (SubSeq r) =
        showsPrec d r


-- | Behavior common to showing 'NUnion' and 'NUnionWithOne'.
showUnion :: (GSet c, Show (CharacterClass c))
          => Int
          -> CharacterClass c
          -> [Some1 (SubUnion c)]
          -> ShowS
showUnion d p l =
    showParen (d > unionPrec && numElements > 1) $
        intercalate (showString " + ") (literal ++ map showSub l)
    where
        unionPrec = 6

        prec =
            if numElements > 1 then unionPrec else d

        showSub (Some1 r) =
            showsPrec prec r

        literal =
            if p == zero then
                []
            else
                [showsPrec prec p]

        numElements = length literal + length l



-- | Combine a list of string builders using another as a separator.
intercalate :: ShowS -> [ShowS] -> ShowS
intercalate sep l =
    foldr (.) id (List.intersperse sep l)



-- * Parsing

instance (GSet c, Read (CharacterClass c)) => Read (RegExp c) where
    readsPrec _ =
        Parser.readP_to_S parser

        where
            parser :: Parser.ReadP (RegExp c)
            parser = do
                Parser.skipSpaces
                pPlus

            pPlus :: Parser.ReadP (RegExp c)
            pPlus =
                Parser.choice
                    [ do
                        left <- pTimes
                        Parser.char '+'
                        Parser.skipSpaces
                        right <- pPlus
                        return $ left `rPlus` right

                    , pTimes
                    ]

            pTimes :: Parser.ReadP (RegExp c)
            pTimes =
                Parser.choice
                    [ do
                        left <- pStar
                        Parser.char '#'
                        Parser.skipSpaces
                        right <- pTimes
                        return $ left `rTimes` right

                    , pStar
                    ]

            pStar :: Parser.ReadP (RegExp c)
            pStar = do
                atom <- pAtom
                ops <- Parser.many postfix
                return $ foldr ($) atom ops

            pAtom :: Parser.ReadP (RegExp c)
            pAtom =
                Parser.choice
                    [ do
                        p <- Parser.readS_to_P reads
                        Parser.skipSpaces
                        return $ rLiteral p

                    , do
                        Parser.string "<>"
                        Parser.skipSpaces
                        return rOne

                    , do
                        Parser.char '('
                        Parser.skipSpaces
                        r <- pPlus
                        Parser.char ')'
                        Parser.skipSpaces
                        return r
                    ]

            postfix :: Parser.ReadP (RegExp c -> RegExp c)
            postfix =
                Parser.choice
                    [ do
                        Parser.char '?'
                        Parser.skipSpaces
                        return $ \r -> rOne `rPlus` r

                    , do
                        Parser.char '*'
                        Parser.skipSpaces
                        return rStar
                    ]



-- * Helpers

-- | Existentially quantify a single boolean argument.
data Some1 (f :: Bool -> *) where
    Some1 :: !(f b) -> Some1 f


-- | Useful for defining views that look like lists.
data ListView c e
    = Nil
    | e ::: c



-- * Testing

-- | For testing with QuickCheck.
instance (GSet c, Arbitrary (CharacterClass c)) => Arbitrary (RegExp c) where
    arbitrary = do
        size <- getSize
        if size <= 1 then
            oneof [zero, one, literal]
        else
            oneof [plus, times, star]

        where
            zero :: Gen (RegExp c)
            zero =
                return rZero

            one :: Gen (RegExp c)
            one =
                return rOne

            plus :: Gen (RegExp c)
            plus = do
                l <- subtree
                r <- subtree
                return (l `rPlus` r)

            times :: Gen (RegExp c)
            times = do
                l <- subtree
                r <- subtree
                return (l `rTimes` r)

            star :: Gen (RegExp c)
            star = do
                r <- subtree
                return (rStar r)

            literal :: Gen (RegExp c)
            literal = do
                p <- resize 5 arbitrary
                return (rLiteral p)

            -- | Decrement the size parameter before generating
            -- a regular expression
            subtree :: Gen (RegExp c)
            subtree = do
                size <- getSize
                newSize <- choose (0, size - 1)
                resize newSize arbitrary

    shrink r =
        case view r of
            One ->
                []
            Plus r1 r2 ->
                concat [
                    [r1, r2],
                    [s1 `rPlus` r2 | s1 <- shrink r1],
                    [r1 `rPlus` s2 | s2 <- shrink r2]
                ]
            Times r1 r2 ->
                concat [
                    [r1, r2],
                    [s1 `rTimes` r2 | s1 <- shrink r1],
                    [r1 `rTimes` s2 | s2 <- shrink r2]
                ]
            Star r ->
                r : [rStar s | s <- shrink r]
            Literal p ->
                [rLiteral s | s <- shrink p]


-- | For testing with SmallCheck.
instance (GSet c, Monad m, Serial m (CharacterClass c)) => Serial m (RegExp c) where
    series =
        cons0 rZero \/
        cons0 rOne \/
        cons2 rPlus \/
        cons2 rTimes \/
        cons1 rStar \/
        cons1 rLiteral