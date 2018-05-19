{-# LANGUAGE GADTs #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Finite state automaton represented as matrices.
module RegExp.Internal.DFA
    ( Dfa

    -- * Combining DFAs
    , product

    -- * Convert from/to regular expressions
    , regexp
    , fromRegExp
    ) where

import Prelude hiding (product)
import Flow

import Control.Exception.Base(assert)

import Data.Finite
import Data.Singletons
import Data.Singletons.Prelude
import Data.Singletons.TypeLits

import Data.List (intercalate)
import qualified Data.Set

import Data.BooleanAlgebra
import Data.Semiring(Semiring(..))
import Data.KleeneAlgebra
import Data.GSet

import RegExp.RegExp
import RegExp.Derivative
import RegExp.Language (Language)
import qualified RegExp.Language as Language


import SparseVector (SparseVector)
import qualified SparseVector as Vector

import SparseMatrix (SparseMatrix)
import qualified SparseMatrix as Matrix


-- | Deterministic finite state automata that accept words over alphabet @c@.
data Dfa c where
    Dfa :: KnownNat n => DfaSize n c -> Dfa c


-- | Deterministic finite state automata with @n@ states that accept words
-- over alphabet @c@.
data DfaSize (n :: Nat) c =
    DfaSize {
        -- | The start state.
        start :: Finite n,

        -- | The transition matrix. In order to represent a deterministic
        -- machine, the following must hold:
        -- * Each row covers the entire alphabet. That is, the union of all
        --   entries on a given row must be the entire set of characters.
        -- * All entries in a row are pairwise disjoint.
        --
        -- The first requirement says that there is at least one transition
        -- from every state given a character. This requirement is easy to
        -- satisfy by adding an explicit "error" state.
        --
        -- The second requirement states that there is at most one transition
        -- given a state and a character.
        transition :: SparseMatrix n n (CharacterClass c),

        -- | Accepting states.
        accept :: SparseVector n Bool
    }


-- | Verify that the given DFA satisfies the conditions outlined in 'DfaSize',
-- and return the DFA unchanged if so. Raises an exception otherwise.
assertValid :: forall c. GSet c => Dfa c -> Dfa c
assertValid r@(Dfa (d :: DfaSize n c)) =
    assert transitionValid $
    r
    where
        transitionValid =
            all
                (== one)
                [Vector.sum $ Matrix.nthRow r (transition d) | r <- finites]


-- | Generic product construction over two DFAs. Intersection
-- and union of DFAs can be recovered as special cases by passing
-- in '(<.>)' and '(<+>)', respectively.
product :: forall c. GSet c
        => (forall a. BooleanAlgebra a => a -> a -> a)
        -> Dfa c
        -> Dfa c
        -> Dfa c
product f (Dfa (d1 :: DfaSize n c)) (Dfa (d2 :: DfaSize m c)) =
    withKnownNat ((sing :: SNat n) %* (sing :: SNat m)) $
    assertValid $
    Dfa $ DfaSize {
        start =
            state (start d1) (start d2),

        transition =
            Matrix.matrix
                [ ((state n m, state n' m'), f s1 s2)
                | n <- finites
                , n' <- finites
                , m <- finites
                , m' <- finites
                , let s1 = transition d1 Matrix.! (n, n')
                , let s2 = transition d2 Matrix.! (m, m')
                ],

        accept =
            Vector.vector
                [ (state n m, f a1 a2)
                | n <- finites
                , m <- finites
                , let a1 = accept d1 Vector.! n
                , let a2 = accept d2 Vector.! m
                ]
        }
    where
        -- | State in the product automata that corresponds to the given
        -- pair of states.
        state :: Finite n -> Finite m -> Finite (n * m)
        state i j =
           combineProduct (i, j)



-- | DFA that accepts words accepted by both input DFAs.
intersection :: forall c. GSet c => Dfa c -> Dfa c -> Dfa c
intersection (Dfa (d1 :: DfaSize n c)) (Dfa (d2 :: DfaSize m c)) =
    withKnownNat ((sing :: SNat n) %* (sing :: SNat m)) $
    assertValid $
    Dfa $ DfaSize {
        start =
            state (start d1) (start d2),

        transition =
            Matrix.matrix
                [ ((state n m, state n' m'), s1 <.> s2)
                | ((n, n'), s1) <- Matrix.nonZero (transition d1)
                , ((m, m'), s2) <- Matrix.nonZero (transition d2)
                ],

        accept =
            Vector.vector
                [ (state n m, a1 <.> a2)
                | (n, a1) <- Vector.nonZero (accept d1)
                , (m, a2) <- Vector.nonZero (accept d2)
                ]
        }
    where
        -- | State in the product automata that corresponds to the given
        -- pair of states.
        state :: Finite n -> Finite m -> Finite (n * m)
        state i j =
           combineProduct (i, j)


-- | We can form a semiring over DFAs by interpreting them as sets
-- of words.
instance GSet c => Semiring (Dfa c) where
    -- | DFA that accepts no words.
    zero =
        assertValid $
        Dfa $ DfaSize {
            start =
                finite 0 :: Finite 1,

            transition =
                Matrix.matrix [((0, 0), one)],

            accept =
                Vector.vector [(0, False)]
        }

    -- | DFA that accepts all words.
    one =
        assertValid $
        Dfa $ DfaSize {
            start =
                finite 0 :: Finite 1,

            transition =
                Matrix.matrix [((0, 0), one)],

            accept =
                Vector.vector [(0, True)]
        }

    -- | DFA that accepts words accepted by either DFA.
    (<+>) =
        product (<+>)

    -- | DFA that accepts words accepted by both DFAs.
    (<.>) =
        intersection


-- | We can form a boolean algebra over DFAs by interpreting them as
-- sets of words.
instance GSet c => BooleanAlgebra (Dfa c) where
    -- | @complement d@ accepts precisely the words that @d@ doesn't.
    complement (Dfa d) =
        assertValid $
        Dfa $
            d {
                accept =
                    accept d
                        |> Vector.toList
                        |> fmap not
                        |> zip finites
                        |> Vector.vector
            }



-- * Converting to and from regular expressions

-- | Convert a DFA to a regular expression.
regexp :: forall c. GSet c => Dfa c -> RegExp c
regexp (Dfa (d :: DfaSize n c)) =
    Language.regexp $
        (s `Matrix.times` star m `Matrix.times` t) Matrix.! (0, 0)
    where
        s :: SparseMatrix 1 n (Language c)
        s =
            Matrix.fromRows [(0, Vector.vector [(start d, injectBool True)])]

        m :: SparseMatrix n n (Language c)
        m =
            Matrix.map (Language.language . rLiteral) (transition d)

        t :: SparseMatrix n 1 (Language c)
        t =
            Matrix.transpose $
                Matrix.fromRows [(0, Vector.map injectBool (accept d))]

        injectBool :: Semiring a => Bool -> a
        injectBool True =
            one
        injectBool False =
            zero


-- | Convert a regular expression to a DFA.
fromRegExp :: forall c. GSet c => RegExp c -> Dfa c
fromRegExp r =
    case toSing (fromIntegral $ Data.Set.size derivatives) of
        SomeSing (s :: SNat n) ->
            withKnownNat s $
            let
                -- | States of the constructed DFA will be the derivatives of
                -- the input regular expression. We assign each an index.
                state :: RegExp c -> Finite n
                state r =
                    finite $ fromIntegral (Data.Set.findIndex r derivatives)


                -- | Transitions /from/ the given state.
                row :: RegExp c -> SparseVector n (CharacterClass c)
                row r =
                    Vector.vector $
                        (state rZero, complement $ ors $ next r) :
                        [ (state (derivative c r), p)
                        | p <- Data.Set.toList (next r)
                        , Just c <- [choose p]
                        ]
            in
                assertValid $
                Dfa $ DfaSize {
                    start =
                        state r,

                    transition =
                        Matrix.fromRows
                            [(state d, row d) | d <- Data.Set.toList derivatives],

                    accept =
                        Vector.vector [(state d, True) | d <- Data.Set.toList derivatives, nullable d]
                }
    where
        derivatives =
            allDerivatives r



-- * Showing DFAs

instance (GSet c, Show (Set c)) => Show (Dfa c) where
    show (Dfa d) =
        show d


instance (GSet c, KnownNat n, Show (Set c)) => Show (DfaSize n c) where
    show d =
        intercalate "\n"
            [ "Start state:\n    " ++ show (start d)
            ,   "Transition matrix:\n" ++ show (transition d)
            ,   "Accepting states:\n    " ++ show (accept d)
            ]