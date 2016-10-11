-- | Interval analysis, done right.
--
-- This version uses widening to make fixpoint algorithm work.
module TIP.Analysis.IntervalCorrect where

--------------------------------------------------------------------------------

import qualified Data.IntSet as S
import qualified Data.Map as M

import Analysis
import qualified TIP.Analysis.IntervalWrong as IW
import TIP.Syntax

--------------------------------------------------------------------------------

intAnal :: Fun -> FlowAnalysis (M.Map Id IW.Interv)
intAnal fun = (IW.intAnal fun){ widen = Just (widenIntervLat fun) }

widenIntervLat :: Fun -> [M.Map Id IW.Interv] -> [M.Map Id IW.Interv]
widenIntervLat fun = map (M.map widen_interv)
  where
    fun_ints :: [IW.InfInt]
    fun_ints = IW.NegInf : IW.PosInf :
               map (IW.Integer . fromIntegral) (S.toList (funInts fun))

    widen_interv :: IW.Interv -> IW.Interv
    widen_interv i | IW.isBotInt i = i
    widen_interv (IW.Interv l h) = IW.Interv (maximum (filter (\i -> i <= l) fun_ints))
                                             (minimum (filter (\i -> i >= h) fun_ints))

-- | Collect all integers used in a program. Used as seed to widening function.
funInts :: Fun -> S.IntSet
funInts = go_s . funBody
  where
    go_s Skip         = S.empty
    go_s (_ := e)     = go_e e
    go_s (_ :*= e)    = go_e e
    go_s (Output e)   = go_e e
    go_s (Seq s1 s2)  = go_s s1 `S.union` go_s s2
    go_s (If e s1 s2) = go_e e `S.union` go_s s1 `S.union` go_s s2
    go_s (While e s)  = go_e e `S.union` go_s s

    go_e (Int i)         = S.singleton i
    go_e Var{}           = S.empty
    go_e (FunCall e1 e2) = S.unions (go_e e1 : map go_e e2)
    go_e (Binop e1 _ e2) = go_e e1 `S.union` go_e e2
    go_e Input           = S.empty
    go_e AddrOf{}        = S.empty
    go_e Malloc          = S.empty
    go_e (Deref e)       = go_e e
    go_e Null            = S.empty
