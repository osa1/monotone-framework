module TIP.Analysis.AvailableExpr where

--------------------------------------------------------------------------------

import qualified Data.Graph.Inductive as G
import qualified Data.Set as S

import Analysis
import CFG
import SemiLattice
import TIP.Analysis.Utils
import TIP.Syntax

--------------------------------------------------------------------------------

-- | The lattice elements are all supersets of all expression in the program.
availExprLat :: Fun -> SemiLattice (S.Set Exp)
availExprLat fun = SemiLattice
  { join   = S.intersection
  , bottom = funExps fun
  }

availExprAnal :: Fun -> FlowAnalysis (S.Set Exp)
availExprAnal fun = mkFwdAnal lat cfg trans
  where
    lat = availExprLat fun
    cfg = funCFG fun

    trans join_ cur
      | cur == entryNode = S.empty
      | otherwise =
        case G.lab' (G.context cfg cur) of
          Skip      -> join_
          x := e    -> removeReferencing (join_ `S.union` subExps e) x
          x :*= e   -> removeReferencing (join_ `S.union` subExps e) x
          Output e  -> join_ `S.union` subExps e
          Seq{}     -> error "Seq in CFG."
          If e _ _  -> join_ `S.union` subExps e
          While e _ -> join_ `S.union` subExps e
