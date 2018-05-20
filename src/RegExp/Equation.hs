{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | Solving systems of linear equations with regular expression coefficients.
module RegExp.Equation
    ( RightHand
    , solve
    , scale
    , combine
    ) where

import Control.Exception.Base(assert)
import Control.Monad.State

import Data.Map.Strict(Map)
import qualified Data.Map.Strict as Map

import RegExp.RegExp
import Data.GSet(GSet)


-- | Right-hand side of an equation. A sum of terms where a term is
-- either a constant, or a constant times a variable. These look
-- like @r0 + r1 X1 + r2 X2 ...@ where @ri@ are regular expressions
-- and @Xi@ are variables.
type RightHand c v =
    (RegExp c, Map v (RegExp c))


-- | Solve a system of linear equations with regular expression coefficients.
-- Equations are generated on demand using the given function.
-- Coefficients in front of variables must be non-nullable to ensure the
-- system has a unique solution.
solve :: forall v c. (GSet c, Ord v) => (v -> RightHand c v) -> v -> RegExp c
solve f v =
    evalState (go v) (Context Map.empty Map.empty)
    where
        go :: (MonadState (Context c v) m) => v -> m (RegExp c)
        go v = do
            context <- get
            case Map.lookup v (solved context) of
                Just r ->
                    -- We are done if the result was computed beforehand.
                    return r

                Nothing ->
                    assert (not $ Map.member v (partial context)) $ do
                    resolved@(c, l) <- resolve (f v)

                    -- Eliminate @v@ in @resolved@.
                    let resolved'@(c', l') =
                            case Map.lookup v l of
                                -- Nothing to do if @v@ doesn't occur.
                                Nothing ->
                                    resolved

                                -- Otherwise, use Arden's lemma to to rewrite @resolved@.
                                Just cv ->
                                    assert (not $ nullable cv)
                                    scale (rStar cv) (c, Map.delete v l)

                    -- Add a partial solution for @v@ in the context. This is
                    -- essentially substituting the solution for @v@ in all
                    -- "following" equations.
                    put (context {partial = Map.insert v resolved' (partial context)})

                    -- Recursively solve all variables appearing in the
                    -- equation for @v@.
                    terms <-
                        mapM
                            (\(v, c) -> do {r <- go v; return (c `rTimes` r)})
                            (Map.toList l')

                    let result = foldr rPlus c' terms

                    put (context {solved = Map.insert v result (solved context)})
                    return result


        -- | Resolve variables in a 'RightHand' using the context.
        -- Variables not in the context are kept as is.
        resolve :: (MonadState (Context c v) m)
                => RightHand c v
                -> m (RightHand c v)
        resolve (c, l) = do
            resolved <- mapM resolveTerm (Map.toList l)
            return $ foldr combine (c, Map.empty) resolved


        -- | Resolve the variable in a single term using the context.
        -- If the variable is not in the context, it is returned as is.
        resolveTerm :: (MonadState (Context c v) m)
                => (v, RegExp c)
                -> m (RightHand c v)
        resolveTerm (v, r) = do
            context <- get
            case Map.lookup v (partial context) of
                Nothing ->
                    return (rZero, Map.singleton v r)

                Just right -> do
                    resolved <- resolve right
                    return (scale r resolved)


-- | Multiply a 'RightHand' on the left with the given coefficient.
scale :: (GSet c, Ord v) => RegExp c -> RightHand c v -> RightHand c v
scale r (c, l) =
    (r `rTimes` c, Map.map (r `rTimes`) l)


-- | Merge two 'RightHand's using `rPlus`.
combine :: (GSet c, Ord v) => RightHand c v -> RightHand c v -> RightHand c v
combine (c1, l1) (c2, l2) =
    (c1 `rPlus` c2, Map.unionWith rPlus l1 l2)


-- * Internals

-- | Context used in the implementation of 'solve'.
data Context c v =
    Context {
        -- | Variables that have a partial solution in terms of
        -- other variables.
        partial :: Map v (RightHand c v),

        -- | Variables that are fully solved.
        solved :: Map v (RegExp c)
    }


