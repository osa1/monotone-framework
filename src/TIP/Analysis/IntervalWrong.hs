-- | Interval analysis, done wrong.
--
-- This version uses an interval lattice with infinite height, so the fixpoint
-- algorithm won't work.
--
-- (e.g. (0, 0) <= (0, 1) <= (0, 2) <= ... (0, inf) is an infinite chain in this
-- lattice)
--
-- Note that in this implementation it's not possible to express "inifinity",
-- e.g. no (0, inf). So in theory this lattice does not have infinite chain of
-- (<=), but it's still bad enough in practice as it has a chain
--
--   (0, 0) <= (0, 1) <= ... <= (0, maxBound :: Int)
--
-- which is big enough that some programs will take forever to analyze (see
-- example below).
module TIP.Analysis.IntervalWrong where

--------------------------------------------------------------------------------

import Data.Array ((!))
import qualified Data.Map as M
import Data.Maybe (fromJust)

import Analysis
import CFG
import SemiLattice
import TIP.Analysis.Utils
import TIP.Syntax

--------------------------------------------------------------------------------

data Interv = Bot | Interv Int Int
  deriving (Show, Eq)

topInt :: Interv
topInt = Interv minBound maxBound

intLatJoin :: Interv -> Interv -> Interv
intLatJoin Bot            x              = x
intLatJoin x              Bot            = x
intLatJoin (Interv l1 h1) (Interv l2 h2) = Interv (min l1 l2) (max h1 h2)

intLat :: SemiLattice Interv
intLat = SemiLattice
  { join   = intLatJoin
  , bottom = Bot
  }

--------------------------------------------------------------------------------
-- * Abstract evaluation of expressions

eval :: M.Map Id Interv -> Exp -> Interv
eval _ (Int i) = Interv i i
eval m (Var v) = fromJust (M.lookup v m)
eval _ FunCall{} = topInt
eval m (Binop e1 op e2) = apply op (eval m e1) (eval m e2)
eval _ Input = topInt
eval _ AddrOf{} = topInt
eval _ Malloc{} = topInt
eval _ Deref{} = topInt
eval _ Null = topInt

apply :: Binop -> Interv -> Interv -> Interv

apply Gt _ _ = topInt
apply Eq _ _ = topInt

apply _ Bot x   = x
apply _ x   Bot = x

-- FIXME: overflows!!
apply op (Interv l1 h1) (Interv l2 h2) =
  let
    op' = case op of
            Plus -> (+)
            Minus -> (-)
            Mult -> (*)
            Div -> div
            _ -> error "unreachable"

    all_bounds = [ op' l h | l <- [ l1, h1 ], h <- [ l2, h2 ] ]
    lower = minimum all_bounds
    higher = maximum all_bounds
  in
    Interv lower higher

--------------------------------------------------------------------------------

intAnal :: Fun -> FlowAnalysis (M.Map Id Interv)
intAnal fun = mkFwdAnal lat cfg trans
  where
    lat = varMapLattice_union intLat
    cfg = funCFG fun

    trans join_ cur
      | cur == entryNode = bottom lat
      | otherwise =
        case cfgNodeStmts cfg ! cur of
          var := rhs -> M.insert var (eval join_ rhs) join_
          Seq{}      -> error "Seq in CFG."
          _          -> join_
