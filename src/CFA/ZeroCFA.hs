-- | 0-CFA as desribed in "Principles of Program Analysis" chapter 3.
module CFA.ZeroCFA where

--------------------------------------------------------------------------------

import qualified Data.Map as M
import qualified Data.Set as S

import Prelude hiding (lookup)

--------------------------------------------------------------------------------

newtype Label = Label { labelInt :: Int }
  deriving (Show, Eq, Ord)

data Exp = Exp
  { expTerm :: Term
  , expLbl  :: Label
  } deriving (Show, Eq, Ord)

newtype Var = Var { varInt :: Int }
  deriving (Show, Eq, Ord)

data Term
  = C Const
  | X Var
  | Fn Var Exp
  | Fix Var Var Exp
  | App Exp Exp
  | If Exp Exp Exp
  | Let Var Exp Exp
  | Binop Exp Op Exp
  deriving (Show, Eq, Ord)

data Const = Const
  deriving (Show, Eq, Ord)

data Op = Op
  deriving (Show, Eq, Ord)

fvExp :: Exp -> S.Set Var
fvExp = fvTerm . expTerm

fvTerm :: Term -> S.Set Var
fvTerm C{}             = S.empty
fvTerm (X v)           = S.singleton v
fvTerm (Fn x e)        = S.delete x (fvExp e)
fvTerm (Fix f x e)     = S.delete f (S.delete x (fvExp e))
fvTerm (App e1 e2)     = fvExp e1 `S.union` fvExp e2
fvTerm (If e1 e2 e3)   = fvExp e1 `S.union` fvExp e2 `S.union` fvExp e3
fvTerm (Let x e1 e2)   = fvExp e1 `S.union` S.delete x (fvExp e2)
fvTerm (Binop e1 _ e2) = fvExp e1 `S.union` fvExp e2

-- Result of a 0-CFA analysis is a pair
--
--   - abstract cache (C):
--     associates abstract values with each labelled program point.
--
--   - abstract environment (rho):
--     associates abstract values with each variable.

-- Terms are only lambdas (`Fn` or `Fix`).
type AbsVal = S.Set Term

data CFA = CFA
  { _cache :: M.Map Label AbsVal
  , _env   :: M.Map Var   AbsVal
  }

-- | Decision procedure for "acceptability relation" described in Table 3.1.
--
-- The goal is to come up with a minimal CFA that satisfies this relation.
acceptable :: CFA -> Exp -> Bool

CFA _     _   `acceptable` Exp C{}     _ = True
CFA cache env `acceptable` Exp (X var) l = lookup var env `S.isSubsetOf` lookup l cache

-- Note that we don't want bodies of functions to be acceptable here. The idea
-- is to avoid analyzing unreachable program parts e.g. functions that are not
-- applied. Function bodies are analyzed in application case instead.
CFA cache _   `acceptable` Exp t@Fn{}  l = t `S.member` lookup l cache
CFA cache _   `acceptable` Exp t@Fix{} l = t `S.member` lookup l cache

-- We analyze the operand here even if the operator cannot evaluate to a
-- function. TODO: Why? Sounds easy to fix.
cfa@(CFA cache env) `acceptable` Exp (App e1 e2) l =
    acceptable cfa e1 &&
    acceptable cfa e2 &&
    all fun_acceptable (lookup (expLbl e1) cache)
  where
    fun_acceptable (Fn x e) =
      cfa `acceptable` e &&
      lookup (expLbl e2) cache `S.isSubsetOf` lookup x env &&
      lookup (expLbl e) cache `S.isSubsetOf` lookup l cache

    fun_acceptable fun@(Fix f x e) =
      cfa `acceptable` e &&
      lookup (expLbl e2) cache `S.isSubsetOf` lookup x env &&
      lookup (expLbl e) cache `S.isSubsetOf` lookup l cache &&
      fun `S.member` lookup f env

    fun_acceptable e =
      error ("Non-functional abstract value: " ++ show e)

cfa@(CFA cache _) `acceptable` Exp (If e0 e1 e2) l =
    acceptable cfa e0 &&
    acceptable cfa e1 &&
    acceptable cfa e2 &&
    lookup (expLbl e1) cache `S.isSubsetOf` lookup l cache &&
    lookup (expLbl e2) cache `S.isSubsetOf` lookup l cache

cfa@(CFA cache env) `acceptable` Exp (Let x e1 e2) l =
    acceptable cfa e1 &&
    acceptable cfa e2 && -- TODO: Why? shouldn't we check this with updated env?
    lookup (expLbl e1) cache `S.isSubsetOf` lookup x env &&
    lookup (expLbl e2) cache `S.isSubsetOf` lookup l cache

cfa `acceptable` Exp (Binop e1 _ e2) _ =
    acceptable cfa e1 &&
    acceptable cfa e2

--------------------------------------------------------------------------------
-- * Utils

lookup :: Ord k => k -> M.Map k (S.Set a) -> S.Set a
lookup = M.findWithDefault S.empty
