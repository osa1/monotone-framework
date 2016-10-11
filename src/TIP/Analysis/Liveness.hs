module TIP.Analysis.Liveness (livenessAnal) where

--------------------------------------------------------------------------------

import qualified Data.Set as S
import Data.Array ((!))

import Analysis
import CFG
import SemiLattice
import TIP.Syntax

--------------------------------------------------------------------------------

livenessAnalLat :: SemiLattice (S.Set Id)
livenessAnalLat = SemiLattice
  { join   = S.union
  , bottom = S.empty
  }

livenessAnal :: Fun -> FlowAnalysis (S.Set Id)
livenessAnal fun = mkBkwAnal lat cfg trans
  where
    lat = livenessAnalLat
    cfg = funCFG fun

    trans join_ cur
      | cur == exitNode = expVars (funRet fun)
      | otherwise =
        case cfgNodeStmts cfg ! cur of
          Skip      -> join_
          var := e   -> S.delete var join_ `S.union` expVars e
          var :*= e  -> S.delete var join_ `S.union` expVars e
          Output e  -> join_ `S.union` expVars e
          Seq{}     -> error "Seq in CFG."
          If e _ _  -> join_ `S.union` expVars e
          While e _ -> join_ `S.union` expVars e