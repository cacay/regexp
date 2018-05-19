{-# LANGUAGE GADTs #-}

-- | Operations over regular expressions.
module RegExp.Operations
    ( intersection
    , complement
    , difference
    , intersectionEquation
    , complementEquation
    ) where


import qualified Data.Map as Map
import qualified Data.Set as Set

import qualified RegExp.Internal.DFA as DFA
import RegExp.RegExp
import RegExp.Derivative
import RegExp.Equation

import qualified Data.BooleanAlgebra as BooleanAlgebra
import Data.Semiring(Semiring(..))
import Data.GSet hiding (Set)


-- | Regular expression that accepts words both expressions accept.
intersection :: forall c. GSet c => RegExp c -> RegExp c -> RegExp c
intersection r1 r2 =
    DFA.regexp $
        DFA.fromRegExp r1 <.> DFA.fromRegExp r2


-- | Regular expression that accepts words given expression doesn't.
complement :: GSet c => RegExp c -> RegExp c
complement r =
    DFA.regexp $
        BooleanAlgebra.complement $ DFA.fromRegExp r


-- | Regular expression that accepts words the first expression does but
-- the second doesn't.
difference :: GSet c => RegExp c -> RegExp c -> RegExp c
difference r1 r2 =
    DFA.regexp $
        DFA.fromRegExp r1 <.> BooleanAlgebra.complement (DFA.fromRegExp r2)



-- | Intersection of two regular expressions computed directly by solving
-- linear equations instead of going through DFAs.
intersectionEquation :: forall c. GSet c => RegExp c -> RegExp c -> RegExp c
intersectionEquation r1 r2 =
    solve step (r1, r2)
    where
        step :: (RegExp c, RegExp c) -> RightHand c (RegExp c, RegExp c)
        step (r1, r2) =
            (hasEmpty, Map.fromListWith rPlus subTerms)
            where
                hasEmpty =
                    if nullable r1 && nullable r2 then
                        rOne
                    else
                        rZero

                subTerms =
                    [ ((derivative c r1, derivative c r2), rLiteral p)
                    | p <- Set.toList $ join (next r1) (next r2)
                    , Just c <- [choose p]
                    ]


-- | Complement of a regular expression computed directly by solving
-- linear equations instead of going through DFAs.
complementEquation :: forall c. GSet c => RegExp c -> RegExp c
complementEquation r =
    solve step r
    where
        step :: RegExp c -> RightHand c (RegExp c)
        step r =
            (hasEmpty `rPlus` (notNext `rTimes` any), Map.fromListWith rPlus subTerms)
            where
                hasEmpty =
                    if nullable r then rZero else rOne

                notNext =
                    rLiteral $ BooleanAlgebra.complement $ BooleanAlgebra.ors $ next r

                any :: RegExp c
                any =
                    rStar $ rLiteral $ one

                subTerms =
                    [ (derivative c r, rLiteral p)
                    | p <- Set.toList $ next r
                    , Just c <- [choose p]
                    ]
