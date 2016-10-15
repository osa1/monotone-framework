-- | 0-CFA as desribed in "Principles of Program Analysis" chapter 3.
module CFA.ZeroCFA where

--------------------------------------------------------------------------------

import Data.List (foldl')
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
type AbsVal = S.Set AbsTerm

data AbsTerm
  = AbsFn Var Exp
  | AbsFix Var Var Exp
  deriving (Show, Eq, Ord)

type Cache = M.Map Label AbsVal
type Env   = M.Map Var   AbsVal

data CFA = CFA
  { _cache :: Cache
  , _env   :: Env
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
CFA cache _   `acceptable` Exp (Fn x e)    l = AbsFn x e `S.member` lookup l cache
CFA cache _   `acceptable` Exp (Fix f x e) l = AbsFix f x e `S.member` lookup l cache

-- We analyze the operand here even if the operator cannot evaluate to a
-- function. TODO: Why? Sounds easy to fix.
cfa@(CFA cache env) `acceptable` Exp (App e1 e2) l =
    acceptable cfa e1 &&
    acceptable cfa e2 &&
    all fun_acceptable (lookup (expLbl e1) cache)
  where
    fun_acceptable (AbsFn x e) =
      cfa `acceptable` e &&
      lookup (expLbl e2) cache `S.isSubsetOf` lookup x env &&
      lookup (expLbl e) cache `S.isSubsetOf` lookup l cache

    fun_acceptable fun@(AbsFix f x e) =
      cfa `acceptable` e &&
      lookup (expLbl e2) cache `S.isSubsetOf` lookup x env &&
      lookup (expLbl e) cache `S.isSubsetOf` lookup l cache &&
      fun `S.member` lookup f env

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

-- | "Less than" relation for the CFA lattice.
--
-- TODO: Maybe implement another one that takes "set of all locs" and "set of
-- all vars" as arguments?
lt :: CFA -> CFA -> Bool
CFA c1 e1 `lt` CFA c2 e2 =
    and (zipWith S.isSubsetOf c1_values c2_values) &&
    and (zipWith S.isSubsetOf e1_values e2_values)
  where
    c1_values = M.elems (filterEmptySets c1)
    e1_values = M.elems (filterEmptySets e1)
    c2_values = M.elems (filterEmptySets c2)
    e2_values = M.elems (filterEmptySets e2)

--------------------------------------------------------------------------------
-- * Constraint-Based 0-CFA Analysis (Chapter 3.4)

-- | Constraints
data Constr
  = Subset LHS RHS
      -- ^ lhs <= rhs
  | Cond AbsTerm RHS LHS RHS
      -- ^ ({t} <= rhs0) => (lhs <= rhs1)
  deriving (Show, Eq, Ord)

data LHS
  = CacheOfL Label
  | EnvOfL Var
  | SingletonL AbsTerm
  deriving (Show, Eq, Ord)

data RHS
  = CacheOfR Label
  | EnvOfR Var
  deriving (Show, Eq, Ord)

absTerms :: Term -> S.Set AbsTerm
absTerms C{} = S.empty
absTerms X{} = S.empty
absTerms (Fn x e) = S.singleton (AbsFn x e)
absTerms (Fix f x e) = S.singleton (AbsFix f x e)
absTerms (App e1 e2) = absTerms (expTerm e1) `S.union` absTerms (expTerm e2)
absTerms (If e1 e2 e3) = absTerms (expTerm e1) `S.union` absTerms (expTerm e2) `S.union` absTerms (expTerm e3)
absTerms (Let _ e1 e2) = absTerms (expTerm e1) `S.union` absTerms (expTerm e2)
absTerms (Binop e1 _ e2) = absTerms (expTerm e1) `S.union` absTerms (expTerm e2)

-- | Table 3.6
constrGen :: Exp -> S.Set AbsTerm -> S.Set Constr

constrGen (Exp C{} _) _ =
    S.empty

constrGen (Exp (X x) l) _ =
    S.singleton (EnvOfL x `Subset` CacheOfR l)

constrGen (Exp (Fn x e) l) ts =
    S.insert (SingletonL (AbsFn x e) `Subset` CacheOfR l) $
    constrGen e ts

constrGen (Exp (Fix f x e) l) ts =
    S.insert (SingletonL (AbsFix f x e) `Subset` CacheOfR l) $
    S.insert (SingletonL (AbsFix f x e) `Subset` EnvOfR f) $
    constrGen e ts

constrGen (Exp (App e1 e2) l) ts = S.unions
  [ constrGen e1 ts
  , constrGen e2 ts
  , S.fromList [ Cond t (CacheOfR (expLbl e1)) (CacheOfL (expLbl e2)) (EnvOfR x)
               | t@(AbsFn x _) <- S.toList ts ]
  , S.fromList [ Cond t (CacheOfR (expLbl e1)) (CacheOfL (expLbl e0)) (CacheOfR l)
               | t@(AbsFn _ e0) <- S.toList ts ]
  , S.fromList [ Cond t (CacheOfR (expLbl e1)) (CacheOfL (expLbl e2)) (EnvOfR x)
               | t@(AbsFix _ x _) <- S.toList ts ]
  , S.fromList [ Cond t (CacheOfR (expLbl e1)) (CacheOfL (expLbl e0)) (CacheOfR l)
               | t@(AbsFix _ _ e0) <- S.toList ts ]
  ]

constrGen (Exp (If e0 e1 e2) l) ts =
    S.insert (CacheOfL (expLbl e1) `Subset` CacheOfR l) $
    S.insert (CacheOfL (expLbl e2) `Subset` CacheOfR l) $
    S.union (constrGen e0 ts) $
    S.union (constrGen e1 ts) $
    constrGen e2 ts

constrGen (Exp (Let x e1 e2) l) ts =
    S.insert (CacheOfL (expLbl e1) `Subset` EnvOfR x) $
    S.insert (CacheOfL (expLbl e2) `Subset` CacheOfR l) $
    S.union (constrGen e1 ts) $
    constrGen e2 ts

constrGen (Exp (Binop e1 _ e2) _) ts =
    S.union (constrGen e1 ts) $
    constrGen e2 ts

-- Using tuples to look the same as the implementation in the book

fixpoint :: Exp -> (Cache, Env)
fixpoint e = loop cfa0
  where
    cfa0 = (M.empty, M.empty)
    loop cfa
      | next == cfa = cfa
      | otherwise   = loop next
      where
        next = f_star cfa

    constrs :: [(Ls, RHS)]
    constrs = map toLs (S.toList (constrGen e (absTerms (expTerm e))))

    f_star :: (Cache, Env) -> (Cache, Env)
    f_star cfa = (f1 cfa, f2 cfa)

    f1 :: (Cache, Env) -> Cache
    f1 (cache0, env) = foldl' f1' cache0 constrs
      where
        f1' :: Cache -> (Ls, RHS) -> Cache
        f1' cache (ls, CacheOfR l) = alterSet (eval (cache, env) ls) l cache
        f1' cache (_,  EnvOfR{})   = cache

    f2 :: (Cache, Env) -> Env
    f2 (cache, env0) = foldl' f2' env0 constrs
      where
        f2' :: Env -> (Ls, RHS) -> Env
        f2' env (_,  CacheOfR{}) = env
        f2' env (ls, EnvOfR x)   = alterSet (eval (cache, env) ls) x env

data Ls
  = LhsLs LHS
  | CondLs AbsTerm RHS LHS
      -- ^ ({t} <= rhs) => lhs

toLs :: Constr -> (Ls, RHS)
toLs (Subset lhs rhs)       = (LhsLs lhs, rhs)
toLs (Cond t rhs0 lhs rhs1) = (CondLs t rhs0 lhs, rhs1)

-- Defined in 3.4.1
eval :: (Cache, Env) -> Ls -> AbsVal
eval (cache, _  ) (LhsLs (CacheOfL l))   = lookup l cache
eval (_,     env) (LhsLs (EnvOfL x))     = lookup x env
eval (_,     _  ) (LhsLs (SingletonL t)) = S.singleton t
eval (cache, env) (CondLs t rhs lhs)
  | t `S.member` eval (cache, env) (rhsToLs rhs)
  = eval (cache, env) (LhsLs lhs)
  | otherwise
  = S.empty

rhsToLs :: RHS -> Ls
rhsToLs (CacheOfR l) = LhsLs (CacheOfL l)
rhsToLs (EnvOfR x)   = LhsLs (EnvOfL x)

--------------------------------------------------------------------------------
-- * Utils

lookup :: Ord k => k -> M.Map k (S.Set a) -> S.Set a
lookup = M.findWithDefault S.empty

alterSet :: (Ord k, Ord a) => S.Set a -> k -> M.Map k (S.Set a) -> M.Map k (S.Set a)
alterSet s = M.alter (maybe (Just s) (Just . S.union s))

-- | In our lattice a map entry
--
--      k :-> {}
--
-- is the same as not having it at all. So we need this function when comparing
-- lattice elements.
filterEmptySets :: M.Map k (S.Set v) -> M.Map k (S.Set v)
filterEmptySets = M.filter (not . S.null)
