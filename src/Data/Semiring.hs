-- | Copied from @semiring-num-1.6.0.1@ because that doesn't work
-- with Stack nightly build. TODO: delete when that works.
module Data.Semiring
    ( Semiring(..)
    , DetectableZero(..)
    ) where

-- $setup
-- >>> import Data.Function

-- | A <https://en.wikipedia.org/wiki/Semiring Semiring> is like the
-- the combination of two 'Data.Monoid.Monoid's. The first
-- is called '<+>'; it has the identity element 'zero', and it is
-- commutative. The second is called '<.>'; it has identity element 'one',
-- and it must distribute over '<+>'.
--
-- = Laws
-- == Normal 'Monoid' laws
--
-- @(a '<+>' b) '<+>' c = a '<+>' (b '<+>' c)
--'zero' '<+>' a = a '<+>' 'zero' = a
--(a '<.>' b) '<.>' c = a '<.>' (b '<.>' c)
--'one' '<.>' a = a '<.>' 'one' = a@
--
-- == Commutativity of '<+>'
-- @a '<+>' b = b '<+>' a@
--
-- == Distribution of '<.>' over '<+>'
-- @a '<.>' (b '<+>' c) = (a '<.>' b) '<+>' (a '<.>' c)
--(a '<+>' b) '<.>' c = (a '<.>' c) '<+>' (b '<.>' c)@
--
-- == Annihilation
-- @'zero' '<.>' a = a '<.>' 'zero' = 'zero'@
--
-- An ordered semiring follows the laws:
--
-- @x '<=' y => x '<+>' z '<=' y '<+>' z
--x '<=' y => x '<+>' z '<=' y '<+>' z
--'zero' '<=' z '&&' x '<=' y => x '<.>' z '<=' y '<.>' z '&&' z '<.>' x '<=' z '<.>' y@
class Semiring a  where
    {-# MINIMAL zero , one , (<.>) , (<+>) #-}
    -- | The identity of '<+>'.
    zero
        :: a
    -- | The identity of '<.>'.
    one
        :: a
    -- | An associative binary operation, which distributes over '<+>'.
    infixl 7 <.>
    (<.>) :: a -> a -> a
    -- | An associative, commutative binary operation.
    infixl 6 <+>
    (<+>) :: a -> a -> a


-- | Useful for operations where zeroes may need to be discarded: for instance
-- in sparse matrix calculations.
class Semiring a =>
      DetectableZero a  where
    -- | 'True' if x is 'zero'.
    isZero
        :: a -> Bool


instance Semiring Bool where
    one = True
    zero = False
    (<+>) = (||)
    (<.>) = (&&)
    {-# INLINE zero #-}
    {-# INLINE one #-}
    {-# INLINE (<+>) #-}
    {-# INLINE (<.>) #-}


instance DetectableZero Bool where
    isZero = not
    {-# INLINE isZero #-}


instance Semiring () where
    one = ()
    zero = ()
    _ <+> _ = ()
    _ <.> _ = ()
    {-# INLINE zero #-}
    {-# INLINE one #-}
    {-# INLINE (<+>) #-}
    {-# INLINE (<.>) #-}

instance DetectableZero () where
    isZero _ = True
    {-# INLINE isZero #-}


instance (Semiring a, Semiring b) => Semiring (a, b) where
    one =
        (one, one)

    zero =
        (zero, zero)

    (a1, b1) <+> (a2, b2) =
        (a1 <+> a2, b1 <+> b2)

    (a1, b1) <.> (a2, b2) =
        (a1 <.> a2, b1 <.> b2)

instance (DetectableZero a, DetectableZero b) => DetectableZero (a, b) where
    isZero (a, b) =
        isZero a && isZero b