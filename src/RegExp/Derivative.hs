{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}

-- | Derivatives of regular expressions that support character classes.
-- The development follows
-- [Symbolic Solving of Extended Regular Expression Inequalities](https://arxiv.org/abs/1410.3227).
module RegExp.Derivative
    ( Word

    -- * Derivatives
    , derivative
    , partialDerivative

    -- * Application of derivatives
    , matches
    , equivalent

    -- * Automata construction
    , allDerivatives
    , next
    , join
    ) where

import Prelude hiding (Word)

import Control.Exception.Base(assert)
import Control.Monad(unless, when)
import Control.Monad.Except(MonadError(..), runExceptT)
import qualified Data.Equivalence.Monad as Equiv
import qualified Data.Equivalence.STT as EquivSTT

import Data.Set(Set)
import qualified Data.Set as Set

import RegExp.RegExp

import Data.BooleanAlgebra
import Data.Semiring (Semiring(..))
import Data.GSet hiding (Set)



-- | String of characters from an alphabet @c@.
type Word c =
    [c]



-- * Derivatives

-- | Brzozowski derivative of a regular expression with respect to a character.
-- @derivative c r@ matches a word @w@ if and only if @r@ matches @cw@.
derivative :: GSet c => c -> RegExp c -> RegExp c
derivative c r =
    case view r of
        One ->
            rZero

        Plus r1 r2 ->
            rPlus (derivative c r1) (derivative c r2)

        Times r1 r2 | nullable r1 ->
            rPlus (derivative c r1 `rTimes` r2) (derivative c r2)

        Times r1 r2 | otherwise ->
            derivative c r1 `rTimes` r2

        Star r' ->
            derivative c r' `rTimes` r

        Literal p ->
            if c `member` p then rOne else rZero


-- | Antimirov derivative of a regular expression with respect to a character.
-- This is similar to 'derivative', but returns a set of regular expressions
-- whose union is equivalent to the Brzozowski derivative.
partialDerivative :: forall c. GSet c
                  => c
                  -> RegExp c
                  -> Set (RegExp c)
partialDerivative c r =
    case view r of
        One ->
            Set.empty

        Plus r1 r2 ->
            partialDerivative c r1 `Set.union` partialDerivative c r2

        Times r1 r2 | nullable r1 ->
            Set.union
                (partialDerivative c r1 `setTimes` r2)
                (partialDerivative c r2)

        Times r1 r2 | otherwise ->
            partialDerivative c r1 `setTimes` r2

        Star r' ->
            partialDerivative c r' `setTimes` r

        Literal p ->
            if c `member` p then Set.singleton rOne else Set.empty

    where
        setTimes :: Set (RegExp c) -> RegExp c -> Set (RegExp c)
        setTimes s r =
            Set.map (`rTimes` r) s



-- * Applications

-- | @r `matches` w@ if the regular expression @r@ accepts word @w@.
matches :: GSet c => RegExp c -> Word c -> Bool
matches r [] =
    nullable r
matches r (c : w) =
    matches (derivative c r) w


-- | Two regular expressions are equivalent if and only if they match
-- the same set of strings. This function will check for equivalence,
-- and return a witness in the case the expressions are different.
-- One of the expressions will match the witness and the other won't.
equivalent :: forall c. GSet c => RegExp c -> RegExp c -> Either (Word c) ()
equivalent r1 r2 =
    case Equiv.runEquivM' (runExceptT (check r1 r2)) of
        Left w ->
            assert (r1 `matches` w /= r2 `matches` w) $
            Left w

        Right () ->
            Right ()
    where
        -- | Hopcroft and Karp's bisimulation algorithm.
        check :: (MonadError (Word c) m, Equiv.MonadEquiv (EquivSTT.Class s () (RegExp c)) (RegExp c) () m)
              => RegExp c
              -> RegExp c
              -> m ()
        check r1 r2 = do
            weAlreadyChecked <- Equiv.equivalent r1 r2
            unless weAlreadyChecked $ do
                when (nullable r1 /= nullable r2) $
                    -- These expressions differ since one can match the empty
                    -- word and the other cannot. The empty word is our witness.
                    throwError []

                -- Assume these "states" are equivalent, check following states.
                Equiv.equate r1 r2

                let derivatives =
                        [ (c, derivative c r1, derivative c r2)
                        | p <- Set.toList (next r1 `join` next r2)
                        , Just c <- [choose p]
                        ]

                mapM_ checkNext derivatives


        -- | Check states reached by a character.
        checkNext :: (MonadError (Word c) m, Equiv.MonadEquiv (EquivSTT.Class s () (RegExp c)) (RegExp c) () m)
              => (c, RegExp c, RegExp c)
              -> m ()
        checkNext (c, r1, r2) =
            check r1 r2 `catchError` \w ->
                throwError (c : w)



-- * Automata construction

-- | Set of derivatives of a regular expression under all words.
allDerivatives :: forall c. GSet c => RegExp c -> Set (RegExp c)
allDerivatives r =
    Set.insert rZero (helper Set.empty [r])
    where
        helper :: Set (RegExp c) -> [RegExp c] -> Set (RegExp c)
        helper context [] =
            context

        helper context (r : rest) | r `Set.member` context =
            helper context rest

        helper context (r : rest) =
            let
                derivatives =
                    [ derivative c r | p <- Set.toList (next r)
                                     , Just c <- [choose p]]
            in
                helper (Set.insert r context) (derivatives ++ rest)



-- * Helpers

-- | Given a regular expression @r@, compute equivalence classes of
-- character classes such that:
--
-- * @p `member` next r@ and @c1 `member` p && c2 `member` p@ implies
--   @derivative c1 r = derivative c2 r@,
-- * @not $ c `member` ors (next r)@ implies @derivative c r ~ rZero@.
next :: GSet c => RegExp c -> Set (CharacterClass c)
next r =
    case view r of
        One ->
            Set.singleton zero

        Plus r1 r2 ->
            join (next r1) (next r2)

        Times r1 r2 | nullable r1 ->
            join (next r1) (next r2)

        Times r1 _ | otherwise ->
            next r1

        Star r ->
            next r

        Literal p  ->
            Set.singleton p


-- | Given two sets of mutually disjoint character classes, compute
-- a set of mutually disjoint character classes that cover both input
-- sets. More concretely, given @s1@ and @s2@ such that
--
-- @'disjoint' s1 && 'disjoint' s2@
--
-- we have:
--
-- * @'ors' ('join' s1 s2) = 'ors' s1 <+> 'ors' s2@
-- * @'disjoint' ('join' s1 s2)@
-- * @'all' (\p -> 'all' (\p1 -> p '<.>' p1 == 'zero' || p `subset` p1) s1) ('join' s1 s2)@
-- * @'all' (\p -> 'all' (\p2 -> p '<.>' p2 == 'zero' || p `subset` p2) s2) ('join' s1 s2)@
join :: GSet c
     => Set (CharacterClass c)
     -> Set (CharacterClass c)
     -> Set (CharacterClass c)
join s1 s2 = Set.fromList $ concat $ do
    p1 <- Set.toList s1
    p2 <- Set.toList s2
    return
        [ p1 <.> p2
        , p1 `butNot` ors s2
        , p2 `butNot` ors s1
        ]


-- | Test if a set of character classes are pairwise disjoint.
disjoint :: GSet c => Set (CharacterClass c) -> Bool
disjoint s =
    let s' = Set.toList s in
        and [ p1 <.> p2 == zero | p1 <- s', p2 <- s', p1 /= p2 ]