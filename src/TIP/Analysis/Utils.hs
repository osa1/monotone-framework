module TIP.Analysis.Utils where

--------------------------------------------------------------------------------

import qualified Data.Map as M
import qualified Data.Set as S

import SemiLattice
import TIP.Syntax

--------------------------------------------------------------------------------

-- | Remove expressions from the set that reference to the given id.
removeReferencing :: S.Set Exp -> Id -> S.Set Exp
removeReferencing s x = S.filter (\e -> not (S.member (Var x) (subExps e))) s

-- | Generate a map lattice with variables as keys. Join = union. Use for "may"
-- analyses.
varMapLattice_union :: SemiLattice a -> SemiLattice (M.Map Id a)
varMapLattice_union l = SemiLattice
  { join   = M.unionWith (join l)
  , bottom = M.empty
               -- Alternatively this could be
               --   M.fromList (zip vars (repeat (bottom l)))
  }
