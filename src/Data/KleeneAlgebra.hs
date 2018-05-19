-- | Definition of Kleene algebras.
module Data.KleeneAlgebra
    ( KleeneAlgebra(..)
    ) where

import Data.Semiring (Semiring (..))


-- | A Kleene algebra is an /idempotent/ semiring with an additional operation
-- called the Kleene star. In addition to the semiring axioms, a Kleene algebra
-- needs to satisfy the following properties:
--
-- == Idempotence of '<+>'
-- @a '<+>' a = a@
--
-- == Properties of 'star'
-- @'one' '<+>' (a '<.>' 'star' a) <= 'star' a@
--
-- @'one' '<+>' ('star' a '<.>' a) <= 'star' a@
--
-- @b '<+>' (a '<.>' x) <= x ==> ('star' a) '<.>' b <= x@
--
-- @b '<+>' (x '<.>' a) <= x ==> b '<.>' ('star' a) <= x@
--
-- Here, @a <= b@ is defined as @a '<+>' b = b@.
class Semiring a => KleeneAlgebra a where
    -- | Kleene star. Captures the notion of /iteration/.
    star :: a -> a


-- | Booleans form a (trivial) Kleene algebra.
instance KleeneAlgebra Bool where
    star _ =
        True
