module TIP.Analysis.ConstProp where

--------------------------------------------------------------------------------

import qualified Data.Graph.Inductive as G
import qualified Data.Map as M

import Analysis
import CFG
import SemiLattice
import TIP.Analysis.Utils
import TIP.Syntax

--------------------------------------------------------------------------------

-- | Out lattice elements for constant propagation.
data Const
  = TopConst      -- ^ not a constant
  | IntConst Int  -- ^ constant
  | BottomConst   -- ^ unknown
  deriving (Show, Eq)

constJoin :: Const -> Const -> Const
constJoin TopConst    _           = TopConst
constJoin _           TopConst    = TopConst
constJoin BottomConst c           = c
constJoin c           BottomConst = c
constJoin c1          c2
  | c1 == c2  = c1
  | otherwise = TopConst

-- | Constant propagation lattice.
constPropLat :: SemiLattice Const
constPropLat = SemiLattice
  { join   = constJoin
  , bottom = BottomConst
  }

--------------------------------------------------------------------------------
-- * Abstract evaluation of expressions

applyBinop :: Binop -> Int -> Int -> Const
applyBinop Plus  x y = IntConst (x + y)
applyBinop Minus x y = IntConst (x - y)
applyBinop Mult  x y = IntConst (x * y)
applyBinop Div   x y = IntConst (x `div` y)
applyBinop Gt    _ _ = TopConst
applyBinop Eq    _ _ = TopConst

applyConstPropOp :: Binop -> Const -> Const -> Const
applyConstPropOp op (IntConst i1) (IntConst i2) = applyBinop op i1 i2

-- TODO: ??? Confused here ???
applyConstPropOp _  BottomConst   _             = BottomConst
applyConstPropOp _  _             BottomConst   = BottomConst

-- TODO: Can't we make this better by returning const for `T * 0`?
applyConstPropOp _  TopConst      _             = TopConst
applyConstPropOp _  _             TopConst      = TopConst

evalConstProp :: M.Map Id Const -> Exp -> Const
evalConstProp _ (Int i) = IntConst i
evalConstProp m (Var i) =
  M.findWithDefault BottomConst i m
  -- or alternatively
  -- fromMaybe TopConst (M.lookup i m)
evalConstProp _ FunCall{} = TopConst
evalConstProp m (Binop e1 op e2) = applyConstPropOp op (evalConstProp m e1) (evalConstProp m e2)
evalConstProp _ Input = TopConst
evalConstProp _ (AddrOf _) = TopConst
evalConstProp _ Malloc = TopConst
evalConstProp _ Deref{} = TopConst
evalConstProp _ Null = TopConst

--------------------------------------------------------------------------------

constPropAnal :: Fun -> FlowAnalysis (M.Map Id Const)
constPropAnal fun = mkFwdAnal lat cfg trans
  where
    lat = varMapLattice_union constPropLat
    cfg = funCFG fun

    trans join_ cur =
      case G.lab' (G.context cfg cur) of
        var := rhs -> M.insert var (evalConstProp join_ rhs) join_
        Seq{}      -> error "Seq in CFG."
        _          -> join_
