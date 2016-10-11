module TIP.Analysis.Sign (signAnal) where

--------------------------------------------------------------------------------

import Data.Array
import qualified Data.Map as M
import Data.Maybe (fromJust)

import Analysis
import CFG
import SemiLattice
import TIP.Analysis.Utils
import TIP.Syntax

import Prelude hiding (exp)

--------------------------------------------------------------------------------
-- * The sign lattice

data Sign
  = Pos | Neg | Zero
  | Top    -- ^ set of all integers
  | Bottom -- ^ empty set
  deriving (Show, Eq)

signJoin :: Sign -> Sign -> Sign
signJoin Top    _      = Top
signJoin _      Top    = Top
signJoin Bottom x      = x
signJoin x      Bottom = x
signJoin Pos    Pos    = Pos
signJoin Neg    Neg    = Neg
signJoin Zero   Zero   = Zero
signJoin _      _      = Top

signLattice :: SemiLattice Sign
signLattice = SemiLattice
  { join   = signJoin
  , bottom = Bottom
  }

--------------------------------------------------------------------------------

-- | Abstract evaluation of expressions for their signs.
eval :: M.Map Id Sign -> Exp -> Sign
eval env exp =
  case exp of
    Int i
      | i > 0     -> Pos
      | i < 0     -> Neg
      | otherwise -> Zero
    Var v -> fromJust (M.lookup v env)
    Binop e1 op e2 -> applyOp op (eval env e1) (eval env e2)
    _ -> Top

applyOp :: Binop -> Sign -> Sign -> Sign

-- addition
applyOp Plus Bottom  _       = Bottom
applyOp Plus _       Bottom  = Bottom
applyOp Plus Top     _       = Top
applyOp Plus _       Top     = Top
applyOp Plus Pos     Pos     = Pos
applyOp Plus Pos     Neg     = Top
applyOp Plus Pos     Zero    = Pos
applyOp Plus Neg     Pos     = Top
applyOp Plus Neg     Neg     = Neg
applyOp Plus Neg     Zero    = Neg
applyOp Plus Zero    Pos     = Pos
applyOp Plus Zero    Neg     = Neg
applyOp Plus Zero    Zero    = Zero

-- negation
applyOp Minus Bottom  _      = Bottom
applyOp Minus _       Bottom = Bottom
applyOp Minus Top     _      = Top
applyOp Minus _       Top    = Top
applyOp Minus Pos     Pos    = Top
applyOp Minus Pos     Neg    = Pos
applyOp Minus Pos     Zero   = Pos
applyOp Minus Neg     Pos    = Neg
applyOp Minus Neg     Neg    = Top
applyOp Minus Neg     Zero   = Neg
applyOp Minus Zero    Pos    = Neg
applyOp Minus Zero    Neg    = Pos
applyOp Minus Zero    Zero   = Zero

-- multiplication
applyOp Mult Bottom  _       = Bottom
applyOp Mult _       Bottom  = Bottom
applyOp Mult Top     Zero    = Zero
applyOp Mult Top     _       = Top
applyOp Mult Pos     Pos     = Pos
applyOp Mult Pos     Neg     = Neg
applyOp Mult Pos     Zero    = Zero
applyOp Mult Pos     Top     = Top
applyOp Mult Neg     Pos     = Neg
applyOp Mult Neg     Neg     = Pos
applyOp Mult Neg     Zero    = Zero
applyOp Mult Neg     Top     = Top
applyOp Mult Zero    _       = Zero

-- division
applyOp Div Bottom  _        = Bottom
applyOp Div _       Bottom   = Bottom
applyOp Div Top     _        = Top
applyOp Div _       Top      = Top
applyOp Div Pos     Pos      = Pos
applyOp Div Pos     Neg      = Neg
applyOp Div Pos     Zero     = Bottom -- IMPORTANT! optimization opportunity
applyOp Div Neg     Pos      = Neg
applyOp Div Neg     Neg      = Pos
applyOp Div Neg     Zero     = Bottom
applyOp Div Zero    Pos      = Zero
applyOp Div Zero    Neg      = Zero
applyOp Div Zero    Zero     = Bottom

-- other operators don't return integers
applyOp Gt _ _               = Bottom -- Not Top!
applyOp Eq _ _               = Bottom -- Not Top!

--------------------------------------------------------------------------------

signAnal :: Fun -> FlowAnalysis (M.Map Id Sign)
signAnal fun = mkFwdAnal lat cfg trans
  where
    lat = varMapLattice_union signLattice
    cfg = funCFG fun
    trans join_ cur =
      case cfgNodeStmts cfg ! cur of
        var := rhs -> M.insert var (eval join_ rhs) join_
        Seq{}      -> error "Seq in CFG."
        _          -> join_
