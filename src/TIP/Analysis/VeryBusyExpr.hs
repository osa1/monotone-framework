module TIP.Analysis.VeryBusyExpr where

--------------------------------------------------------------------------------

import qualified Data.Graph.Inductive as G
import qualified Data.Set as S

import Analysis
import CFG
import SemiLattice
import TIP.Analysis.AvailableExpr (availExprLat)
import TIP.Analysis.Utils
import TIP.Syntax

--------------------------------------------------------------------------------

-- | The lattice is the same as "available expressions" lattice.
veryBusyExprLat :: Fun -> SemiLattice (S.Set Exp)
veryBusyExprLat = availExprLat

veryBusyExprAnal :: Fun -> FlowAnalysis (S.Set Exp)
veryBusyExprAnal fun = mkBkwAnal lat cfg trans
  where
    lat = veryBusyExprLat fun
    cfg = funCFG fun

    trans join_ cur
      | cur == exitNode = S.empty
      | otherwise =
        case G.lab' (G.context cfg cur) of
          Skip      -> join_
          x := e    -> removeReferencing join_ x `S.union` subExps e
          x :*= e   -> removeReferencing join_ x `S.union` subExps e
          Output e  -> join_ `S.union` subExps e
          Seq{}     -> error "Seq in CFG."
          If e _ _  -> join_ `S.union` subExps e
          While e _ -> join_ `S.union` subExps e
