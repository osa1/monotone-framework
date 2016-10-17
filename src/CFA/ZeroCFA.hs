{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE TupleSections #-}

-- | 0-CFA as desribed in "Principles of Program Analysis" chapter 3.
module CFA.ZeroCFA where

--------------------------------------------------------------------------------

import Data.Bifunctor (first)
import Data.Bits (shiftL, (.|.))
import qualified Data.Graph.Inductive.Graph as G
import qualified Data.Graph.Inductive.PatriciaTree as G
import Data.List (foldl')
import qualified Data.Map as M
import Data.Maybe (fromJust)
import qualified Data.Set as S

import Prelude hiding (lookup)

import Utils (span_right)

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
  = Con Const
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

-- | Free variables of an expression
fvExp :: Exp -> S.Set Var
fvExp = fvTerm . expTerm

-- | Free variables of a term
fvTerm :: Term -> S.Set Var
fvTerm Con{}           = S.empty
fvTerm (X v)           = S.singleton v
fvTerm (Fn x e)        = S.delete x (fvExp e)
fvTerm (Fix f x e)     = S.delete f (S.delete x (fvExp e))
fvTerm (App e1 e2)     = fvExp e1 `S.union` fvExp e2
fvTerm (If e1 e2 e3)   = fvExp e1 `S.union` fvExp e2 `S.union` fvExp e3
fvTerm (Let x e1 e2)   = fvExp e1 `S.union` S.delete x (fvExp e2)
fvTerm (Binop e1 _ e2) = fvExp e1 `S.union` fvExp e2

-- | Labels occuring in an expression
labelsExp :: Exp -> S.Set Label
labelsExp e = S.insert (expLbl e) (labelsTerm (expTerm e))

-- | Labels occuring in a term
labelsTerm :: Term -> S.Set Label
labelsTerm Con{} = S.empty
labelsTerm X{} = S.empty
labelsTerm (Fn _ e) = labelsExp e
labelsTerm (Fix _ _ e) = labelsExp e
labelsTerm (App e1 e2) = labelsExp e1 `S.union` labelsExp e2
labelsTerm (If e1 e2 e3) = labelsExp e1 `S.union` labelsExp e2 `S.union` labelsExp e3
labelsTerm (Let _ e1 e2) = labelsExp e1 `S.union` labelsExp e2
labelsTerm (Binop e1 _ e2) = labelsExp e1 `S.union` labelsExp e2

-- | Variables used in an expression (free or bound)
varsExp :: Exp -> S.Set Var
varsExp = varsTerm . expTerm

-- | Terms used in an expression (free or bound)
varsTerm :: Term -> S.Set Var
varsTerm Con{} = S.empty
varsTerm (X v) = S.singleton v
varsTerm (Fn v e) = S.insert v (varsExp e)
varsTerm (Fix v1 v2 e) = S.insert v1 (S.insert v2 (varsExp e))
varsTerm (App e1 e2) = varsExp e1 `S.union` varsExp e2
varsTerm (If e1 e2 e3) = varsExp e1 `S.union` varsExp e2 `S.union` varsExp e3
varsTerm (Let v e1 e2) = S.insert v (varsExp e1 `S.union` varsExp e2)
varsTerm (Binop e1 _ e2) = varsExp e1 `S.union` varsExp e2

-- Result of a 0-CFA analysis is a pair
--
--   - abstract cache (C):
--     associates abstract values with each program point (label).
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

-- Ignores empty sets. For testing purposes.
cfaEq :: CFA -> CFA -> Bool
cfaEq (CFA cache1 env1) (CFA cache2 env2) =
    filterEmpties (M.toList cache1) == filterEmpties (M.toList cache2) &&
    filterEmpties (M.toList env1) == filterEmpties (M.toList env2)
  where
    filterEmpties = filter (not . S.null . snd)

-- | Decision procedure for "acceptability relation" described in Table 3.1.
--
-- The goal is to come up with a minimal CFA that satisfies this relation.
acceptable :: CFA -> Exp -> Bool

CFA _     _   `acceptable` Exp Con{}   _ = True
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

data P
  = C Label
      -- ^ Cache value of label
  | R Var
      -- ^ Env value of var
  deriving (Show, Eq, Ord)

-- | Constraints
data Constr
  = Subset (Either AbsTerm P) P
      -- ^ lhs <= rhs
  | Cond AbsTerm P P P
      -- ^ ({t} <= rhs0) => (lhs <= rhs1)
  deriving (Show, Eq, Ord)

absTerms :: Term -> S.Set AbsTerm
absTerms Con{} = S.empty
absTerms X{} = S.empty
absTerms (Fn x e) = S.singleton (AbsFn x e)
absTerms (Fix f x e) = S.singleton (AbsFix f x e)
absTerms (App e1 e2) = absTerms (expTerm e1) `S.union` absTerms (expTerm e2)
absTerms (If e1 e2 e3) = absTerms (expTerm e1) `S.union` absTerms (expTerm e2) `S.union` absTerms (expTerm e3)
absTerms (Let _ e1 e2) = absTerms (expTerm e1) `S.union` absTerms (expTerm e2)
absTerms (Binop e1 _ e2) = absTerms (expTerm e1) `S.union` absTerms (expTerm e2)

-- | 0-CFA constraint generator. Specified in Table 3.6.
constrGen :: Exp -> S.Set AbsTerm -> S.Set Constr

constrGen (Exp Con{} _) _ =
    S.empty

constrGen (Exp (X x) l) _ =
    S.singleton (Right (R x) `Subset` C l)

constrGen (Exp (Fn x e) l) ts =
    S.insert (Left (AbsFn x e) `Subset` C l) $
    constrGen e ts

constrGen (Exp (Fix f x e) l) ts =
    S.insert (Left (AbsFix f x e) `Subset` C l) $
    S.insert (Left (AbsFix f x e) `Subset` R f) $
    constrGen e ts

constrGen (Exp (App e1 e2) l) ts = S.unions
  [ constrGen e1 ts
  , constrGen e2 ts
  , S.fromList [ Cond t (C (expLbl e1)) (C (expLbl e2)) (R x)
               | t@(AbsFn x _) <- S.toList ts ]
  , S.fromList [ Cond t (C (expLbl e1)) (C (expLbl e0)) (C l)
               | t@(AbsFn _ e0) <- S.toList ts ]
  , S.fromList [ Cond t (C (expLbl e1)) (C (expLbl e2)) (R x)
               | t@(AbsFix _ x _) <- S.toList ts ]
  , S.fromList [ Cond t (C (expLbl e1)) (C (expLbl e0)) (C l)
               | t@(AbsFix _ _ e0) <- S.toList ts ]
  ]

constrGen (Exp (If e0 e1 e2) l) ts =
    S.insert (Right (C (expLbl e1)) `Subset` C l) $
    S.insert (Right (C (expLbl e2)) `Subset` C l) $
    S.union (constrGen e0 ts) $
    S.union (constrGen e1 ts) $
    constrGen e2 ts

constrGen (Exp (Let x e1 e2) l) ts =
    S.insert (Right (C (expLbl e1)) `Subset` R x) $
    S.insert (Right (C (expLbl e2)) `Subset` C l) $
    S.union (constrGen e1 ts) $
    constrGen e2 ts

constrGen (Exp (Binop e1 _ e2) _) ts =
    S.union (constrGen e1 ts) $
    constrGen e2 ts

-- | A 0-CFA constraint solver. Chapter 3.4.2.
cfa1 :: Exp -> CFA
cfa1 e = uncurry CFA (loop cfa0)
  where
    cfa0 = (M.empty, M.empty)
    loop cfa
      | next == cfa = cfa
      | otherwise   = loop next
      where
        next = f_star cfa

    constrs :: [(Ls, P)]
    constrs = map toLs (S.toList (constrGen e (absTerms (expTerm e))))

    f_star :: (Cache, Env) -> (Cache, Env)
    f_star cfa = (f1 cfa, f2 cfa)

    f1 :: (Cache, Env) -> Cache
    f1 (cache0, env) = foldl' f1' cache0 constrs
      where
        f1' :: Cache -> (Ls, P) -> Cache
        f1' cache (ls, C l) = alterSet (eval (cache, env) ls) l cache
        f1' cache (_,  R{}) = cache

    f2 :: (Cache, Env) -> Env
    f2 (cache, env0) = foldl' f2' env0 constrs
      where
        f2' :: Env -> (Ls, P) -> Env
        f2' env (_,  C{}) = env
        f2' env (ls, R x) = alterSet (eval (cache, env) ls) x env

-- | Left-hand side of a subset constraint.
data Ls
  = LhsLs (Either AbsTerm P)
      -- ^ {t} or p
  | CondLs AbsTerm P P
      -- ^ ({t} <= p1) => p2

toLs :: Constr -> (Ls, P)
toLs (Subset lhs rhs)       = (LhsLs lhs, rhs)
toLs (Cond t rhs0 lhs rhs1) = (CondLs t rhs0 lhs, rhs1)

-- Defined in 3.4.1
eval :: (Cache, Env) -> Ls -> AbsVal
eval (cache, _  ) (LhsLs (Right (C l))) = lookup l cache
eval (_,     env) (LhsLs (Right (R x))) = lookup x env
eval (_,     _  ) (LhsLs (Left t))      = S.singleton t
eval (cache, env) (CondLs t rhs lhs)
  | t `S.member` eval (cache, env) (rhsToLs rhs)
  = eval (cache, env) (LhsLs (Right lhs))
  | otherwise
  = S.empty

rhsToLs :: P -> Ls
rhsToLs (C l) = LhsLs (Right (C l))
rhsToLs (R x) = LhsLs (Right (R x))

-- | Table 3.7, graph-based O(n^3) constraint solver.
--
-- (even though we work on constraints, `n` here is the number of terms.
-- TODO: write about why this is so)
--
-- Here's how this works, in my own words (make sure to look at Table 3.7
-- too):
--
-- * The graph has a node for every C(l) and r(x). More precisely, for every
--   location 'l' in program we add a node C(l) and for every variable 'x' in the
--   program we add a node r(x).
--
-- * Each node is annotated with a set of abstract values. These are the values
--   that "flow into" the location (if node is C(l) for a location l) or
--   variable (if node is r(x) for a variable x).
--
--   In my implementation I use a mapping from nodes (typed 'P') to these sets.
--   Initially these sets are empty.
--
-- * Edges are annotated with constraints that gave rise to them.
--
-- * We maintain a workset ('W') of Ps. Initially empty.
--
-- * Adding edges: We consider constraints.
--
--     - {t} <= p: We do nothing if `t` is already in the abstract value set of
--       `p` (remember that `p` is either C(l) for some l or r(x) for some x).
--       Otherwise we add `t` to `p`s abstract value set, and we add `p` to the
--       workset.
--
--     - p1 <= p2: We add an edge from `p1` to `p2`, we annotate the edge with
--       the constraint itself.
--
--     - {t} <= p => p1 <= p2: We add an edge from `p1` to `p2` and `p` to `p2`.
--       both edges are annotated with this constraint.
--
-- * Main loop: Until the workset is empty, fetch a node from the workset.
--
--     - The node has constraint `p1 <= p2`. Add abstract values of p1 to p2. If
--       any new values were added, add p2 to the workset.
--
--     - The node has constraint `{t} <= p => p1 <= p2`. If `t` is in the
--       abstract value set of p, add abstract values of p1 to p2. If any new
--       values were added, add p2 to the workset.
--
-- Initially in the workset we only have location nodes (C(l)) with abstract
-- values. These are basically nodes for lambdas (if we had non-functions
-- abstract values, e.g. integers, we'd add nodes with integer constants to the
-- set too).
--
-- We start popping nodes from the workset, and consider outgoing edges of the
-- node. If an outgoing edge has annotation of form `p1 <= p2`, we "propagate"
-- abstract values from current node to p2, and if any new nodes are added to p2
-- we add `p2` to the workset. If an edge has annotation of form `{t} <= p => p1
-- <= p2`, we do the same only if the condition holds, i.e. if `t` is in the set
-- of `p`.
--
cfa2 :: [Label] -> [Var] -> [Constr] -> CFA
cfa2 lbls vs constrs = CFA cache env
  where
    d_sol = iter grdw0
    cache = M.fromList (map (\l -> (l, fromJust (M.lookup (C l) d_sol))) lbls)
    env   = M.fromList (map (\v -> (v, fromJust (M.lookup (R v) d_sol))) vs)

    iter (gr0, d0, w0)
      | Just (work, w1) <- S.minView w0
      = let
          work_node  = p_node work
          work_edges = G.out gr0 work_node
        in
          iter $
          foldl' (\(gr, d, w) -> \case
                                    Subset (Right p1) p2 ->
                                        add (fromJust (M.lookup p1 d)) p2 (gr, d, w)
                                    Cond t p p1 p2
                                      | t `S.member` fromJust (M.lookup p d) ->
                                        add (fromJust (M.lookup p1 d)) p2 (gr, d, w)
                                      | otherwise -> (gr, d, w)
                                    Subset Left{} _ ->
                                        error "cfa2: Found a term relation edge.")
                 (gr0, d0, w1)
                 (map G.edgeLabel work_edges)

      | otherwise
      = d0

    -- | Nodes of the graph.
    ps :: [P]
    ps = map C lbls ++ map R vs

    -- | Initial (graph, data array, workset).
    grdw0 :: (G.Gr P Constr, M.Map P (S.Set AbsTerm), S.Set P)
    grdw0 = build_graph constrs (g0, d0, w0)
      where
        g0 = G.mkGraph (map (\p -> (p_node p, p)) ps) []
        d0 = M.fromList (zip ps (repeat S.empty))
        w0 = S.empty

    -- | We need a fast mapping from `P` to graph nodes to be able to query edges
    -- quickly.
    --
    -- Alternatively we could use `P` as graph keys but that's not something
    -- that fgl allows to do.
    p_node :: P -> G.Node
    p_node (C l) = labelInt l
    p_node (R v) = (1 `shiftL` 63) .|. varInt v

    -- | Generate edges for a constraint.
    constr_edges :: Constr -> [(G.Node, G.Node)]
    constr_edges (Subset (Right p1) p2) = [(p_node p1, p_node p2)]
    constr_edges (Cond _ p p1 p2)       = [(p_node p1, p_node p2), (p_node p, p_node p2)]
    constr_edges (Subset Left{} _)      = error "constr_edges: Can't generate edge for a term relation."

    -- | Add edges to the graph.
    build_graph :: [Constr]
                -> (G.Gr P Constr, M.Map P (S.Set AbsTerm), S.Set P)
                -> (G.Gr P Constr, M.Map P (S.Set AbsTerm), S.Set P)

    build_graph [] grdw =
      grdw

    build_graph (Subset (Left t) p : rest) grdw =
      build_graph rest $
      add (S.singleton t) p grdw

    build_graph (constr : rest) (gr, d, w) =
      build_graph rest $
      ( foldl' (\g (from, to) -> G.insEdge (from, to, constr) g)
               gr
               (constr_edges constr)
      , d
      , w
      )

    -- | Try to add terms to the given node. Add the node to the worklist if any
    -- terms were added.
    add ts p (gr, d, w)
      | ts `S.isSubsetOf` fromJust (M.lookup p d)
      = (gr, d, w)
      | otherwise
      = (gr, alterSet ts p d, S.insert p w)

-- | Entry point for `cfa2`.
cfa2' :: Exp -> CFA
cfa2' e = cfa2 (S.toList (labelsExp e)) (S.toList (varsExp e)) (S.toList (constrGen e (absTerms (expTerm e))))

--------------------------------------------------------------------------------
-- * Examples

-- | (fn x => x) (fn y => y)
ex_3_1 :: Exp
ex_3_1 = Exp (Exp (Fn (Var 0) (Exp (X (Var 0)) (Label 1))) (Label 2)
              `App` Exp (Fn (Var 1) (Exp (X (Var 1)) (Label 3))) (Label 4))
             (Label 5)

-- | let g = (fun f x => f (fn y => y))
--    in g (fn z => z)
ex_3_2 :: Exp
ex_3_2 = Exp (Let g (Exp (Fix f x (Exp (App (Exp (X f) l1) (Exp (Fn y (Exp (X y) l2)) l3)) l4)) l5)
               (Exp (App (Exp (X g) l6) (Exp (Fn z (Exp (X z) l7)) l8)) l9))
             l10
  where
    (l1 : l2 : l3 : l4 : l5 : l6 : l7 : l8 : l9 : l10 : _) = map Label [ 1 .. ]
    (g : x : y : f : z : _) = map Var [ 1 .. ]

-- | let f = (fn x => x) in ((f f) (fn y => y))
ex_3_32 :: Exp
ex_3_32 = Exp (Let f (Exp (Fn x (Exp (X x) l1)) l2)
                (Exp (App (Exp (App (Exp (X f) l3) (Exp (X f) l4)) l5)
                          (Exp (Fn y (Exp (X y) l6)) l7))
                          l8))
              l9
  where
    (l1 : l2 : l3 : l4 : l5 : l6 : l7 : l8 : l9 : _) = map Label [ 1 .. ]
    (f : x : y : _) = map Var [ 1 .. ]

-- | An example with a captured variable.
--
--   (let g = (\a => a) in (\t => g t)) (fn z => z)
--
ex_capture :: Exp
ex_capture = Exp (App (Exp (Let g (Exp (Fn a (Exp (X a) l1)) l2)
                              (Exp (Fn t (Exp (App (Exp (X g) l3) (Exp (X t) l4)) l5)) l6)) l7)
                      (Exp (Fn z (Exp (X z) l8)) l9))
                 l10
  where
    (g : a : t : z : _) = map Var [ 1 .. ]
    (l1 : l2 : l3 : l4 : l5 : l6 : l7 : l8 : l9 : l10 : _) = map Label [ 1 .. ]

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

showCFA :: CFA -> String
showCFA (CFA cache env) =
    unlines ("Cache:" : map (ln . first labelInt) (M.toList cache) ++
             "Env:" : map (ln . first varInt) (M.toList env))
  where
    ln (lbl, vals) = span_right 3 (show lbl) ++ ": " ++ show (S.toList vals)

instance Show CFA where
  show = showCFA
