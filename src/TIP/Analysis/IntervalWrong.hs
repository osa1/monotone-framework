-- | Interval analysis, done wrong.
--
-- This version uses an interval lattice with infinite height, so the fixpoint
-- algorithm won't work.
--
-- (e.g. (0, 0) <= (0, 1) <= (0, 2) <= ... (0, inf) is an infinite chain in this
-- lattice)
module TIP.Analysis.IntervalWrong where

--------------------------------------------------------------------------------

import qualified Data.Graph.Inductive as G
import qualified Data.Map as M

import Analysis
import CFG
import SemiLattice
import TIP.Analysis.Utils
import TIP.Syntax

--------------------------------------------------------------------------------
-- * Integer intervals

data Interv = Interv
  { _low  :: InfInt
  , _high :: InfInt
  } deriving (Eq)

instance Show Interv where
  show (Interv low high) = "[" ++ show low ++ ", " ++ show high ++ "]"

-- | Integer with plus and minus ∞ values.
data InfInt
  = NegInf  -- ^ -∞
  | Integer Integer
  | PosInf  -- ^ +∞
  deriving (Eq, Ord)

instance Show InfInt where
  show NegInf      = "-∞"
  show (Integer i) = show i
  show PosInf      = "+∞"

-- | Is the interval empty?
isEmptyInterv :: Interv -> Bool
isEmptyInterv (Interv low high) = low > high

--------------------------------------------------------------------------------
-- * Integer interval lattice

-- | Top is (-∞, +∞).
topInt :: Interv
topInt = Interv NegInf PosInf

isTopInt :: Interv -> Bool
isTopInt = (==) topInt

-- | Bottom of the lattice is any empty interval.
isBotInt :: Interv -> Bool
isBotInt = isEmptyInterv

-- | Any interval with low > high will do.
botInt :: Interv
botInt = Interv PosInf NegInf

intLatJoin :: Interv -> Interv -> Interv
intLatJoin i1 i2
  | isBotInt i1 = i2
  | isBotInt i2 = i1
  | isTopInt i1 || isTopInt i2 = topInt
intLatJoin (Interv l1 h1) (Interv l2 h2) = Interv (min l1 l2) (max h1 h2)

intLat :: SemiLattice Interv
intLat = SemiLattice
  { join   = intLatJoin
  , bottom = botInt
  }

--------------------------------------------------------------------------------
-- * Arithmetic on intervals

-- | Addition is partial since -∞ + +∞ is undefined.
addInfInt :: InfInt -> InfInt -> Maybe InfInt

addInfInt NegInf       PosInf       = Nothing
addInfInt NegInf       _            = Just NegInf

addInfInt PosInf       NegInf       = Nothing
addInfInt PosInf       _            = Just PosInf

addInfInt (Integer i1) (Integer i2) = Just (Integer (i1 + i2))
addInfInt Integer{}    NegInf       = Just NegInf
addInfInt Integer{}    PosInf       = Just PosInf

-- | Negation
negInfInt :: InfInt -> InfInt
negInfInt NegInf      = PosInf
negInfInt (Integer i) = Integer (- i)
negInfInt PosInf      = NegInf

-- | x + (- y)
subInfInt :: InfInt -> InfInt -> Maybe InfInt
subInfInt x y = addInfInt x (negInfInt y)

mulInfInt :: InfInt -> InfInt -> InfInt

mulInfInt NegInf NegInf = PosInf
mulInfInt NegInf (Integer i)
  | i < 0     = PosInf
  | i == 0    = Integer 0
  | otherwise = NegInf
mulInfInt NegInf PosInf = NegInf

mulInfInt (Integer i) NegInf
  | i < 0     = PosInf
  | i == 0    = Integer 0
  | otherwise = NegInf
mulInfInt (Integer i1) (Integer i2) = Integer (i1 * i2)
mulInfInt (Integer i) PosInf
  | i < 0     = NegInf
  | i == 0    = Integer 0
  | otherwise = PosInf

mulInfInt PosInf NegInf = NegInf
mulInfInt PosInf (Integer i)
  | i < 0     = NegInf
  | i == 0    = Integer 0
  | otherwise = PosInf
mulInfInt PosInf PosInf = PosInf

--------------------------------------------------------------------------------
-- * Abstract evaluation of expressions

eval :: M.Map Id Interv -> Exp -> Interv
eval _ (Int i) = Interv (Integer (fromIntegral i)) (Integer (fromIntegral i))
eval m (Var v) = M.findWithDefault botInt v m
eval _ FunCall{} = topInt
eval m (Binop e1 op e2) = apply op (eval m e1) (eval m e2)
eval _ Input = topInt
eval _ AddrOf{} = topInt
eval _ Malloc{} = topInt
eval _ Deref{} = topInt
eval _ Null = topInt

apply :: Binop -> Interv -> Interv -> Interv

-- TODO: Why not botInt?
apply Gt _ _ = topInt
apply Eq _ _ = topInt

-- We don't interpret division
apply Div _ _ = topInt

apply Plus (Interv l1 h1) (Interv l2 h2) =
  let
    add NegInf _                  = NegInf
    add _ NegInf                  = NegInf
    add PosInf _                  = PosInf
    add _ PosInf                  = PosInf
    add (Integer i1) (Integer i2) = Integer (i1 + i2)
  in
    Interv (add l1 l2) (add h1 h2)

apply Minus i1_ i2_ = apply Plus i1_ (inv i2_)
  where
    inv (Interv NegInf PosInf) = Interv NegInf PosInf
    inv (Interv PosInf NegInf) = Interv PosInf NegInf
    inv (Interv (Integer i) PosInf) = Interv NegInf (Integer (- i))
    inv (Interv NegInf (Integer i)) = Interv (Integer (- i)) PosInf
    inv (Interv (Integer i1) (Integer i2)) =
      Interv (Integer (min (- i1) (- i2))) (Integer (max (- i1) (- i2)))
    -- all others are bottom
    inv _ = error "bottom in apply Minus"

apply Mult _ _ = error "Interval analysis: Multiplication not implemented"

--------------------------------------------------------------------------------

intAnal :: Fun -> FlowAnalysis (M.Map Id Interv)
intAnal fun = mkFwdAnal lat cfg trans
  where
    lat = varMapLattice_union intLat
    cfg = funCFG fun

    trans join_ cur =
      case G.lab' (G.context cfg cur) of
        var := rhs -> M.insert var (eval join_ rhs) join_
        Seq{}      -> error "Seq in CFG."
        _          -> join_
