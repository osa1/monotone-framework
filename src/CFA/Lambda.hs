-- | This is a solution for exercise 8.1. We don't actually provide any examples
-- or run the solution, because it's impossible to write anything in this
-- language (untyped lambda calculus).
module CFA.Lambda where

--------------------------------------------------------------------------------

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.List (foldl')

import Prelude hiding (lookup)

--------------------------------------------------------------------------------

-- | Variables are represented as integers.
newtype Id = Id { idInt :: Int }
  deriving (Show, Eq, Ord)

-- | Program point
newtype PP = PP { ppInt :: Int }
  deriving (Show, Eq, Ord)

-- | Annotated expressions
data Exp
  = Var PP Id
      -- ^ Variable
  | Lam PP Id Exp
      -- ^ Lambda. Binder is unique in the entire program.
  | App PP Exp Exp
      -- ^ Application
  deriving (Show, Eq, Ord)

getPP :: Exp -> PP
getPP (Var pp _)   = pp
getPP (Lam pp _ _) = pp
getPP (App pp _ _) = pp

mkPPMap :: Exp -> M.Map PP Exp
mkPPMap e@(Var pp _)      = M.singleton pp e
mkPPMap e@(Lam pp _ body) = M.insert pp e (mkPPMap body)
mkPPMap e@(App pp e1 e2)  = M.insert pp e (mkPPMap e1 `M.union` mkPPMap e2)

data CFA = CFA
  { _lblVals :: M.Map PP (S.Set Exp)
      -- ^ 'C' in the book.
      -- "C(l) is supposed to contain the values that the subexpression labelled
      -- 'l' may evaluate to."
  , _env     :: M.Map Id (S.Set Exp)
      -- ^ rho in the book.
      -- "pho(x) contains the values that the variable x can be bound to."
  } deriving (Eq, Show)

bot :: CFA
bot = CFA M.empty M.empty

-- | An example: ((fun x -> x) (fn y -> y))
example :: Exp
example = App (PP 5) (Lam (PP 2) (Id 0) (Var (PP 1) (Id 0))) (Lam (PP 4) (Id 1) (Var (PP 3) (Id 1)))

-- | A (the?) solution to the example.
solution :: CFA
solution = CFA
  { _lblVals = M.fromList [ (PP 1, S.singleton (Lam (PP 4) (Id 1) (Var (PP 3) (Id 1))))
                          , (PP 2, S.singleton (Lam (PP 2) (Id 0) (Var (PP 1) (Id 0))))
                          , (PP 3, S.empty)
                          , (PP 4, S.singleton (Lam (PP 4) (Id 1) (Var (PP 3) (Id 1))))
                          , (PP 5, S.singleton (Lam (PP 4) (Id 1) (Var (PP 3) (Id 1))))
                          ]
  , _env = M.fromList [ (Id 0, S.singleton (Lam (PP 4) (Id 1) (Var (PP 3) (Id 1))))
                      ]
  }

-- We need to find a minimal solution to these constraints:
--
-- (<= is subset relation)
--
--   * For a program point 'pp' with variable 'v',
--
--       env v <= lblVals pp
--
--     This can be solved by adding (set union) `env v` to `lblVals pp`.
--
--   * For a program point 'pp' with lambda '\x -> e'
--
--       { \x -> e } <= lblVals pp
--
--     This can be solved by adding the lambda to lblVals.
--
--   * For a program point 'pp' with application 'e1^pp1 e2^pp2'
--
--       if { \x -> e }     <= lblVals pp1 then lblVals pp2 <= env x
--       if { \x -> e^pp3 } <= lblVals pp1 then lblVals pp3 <= lblVals pp
--
--     This can be solved by, for every lambda in `lblVals pp1`,
--
--       1. updating env by adding `lblVals pp2` to the env entry for argument
--          of the function.
--
--       2. updating lblVals by adding `lblVals pp3` to the entry for the
--          application.
--
-- Note that one requirement here is that every lambda argument has unique name.
--
-- Questions:
--
--   - Does this give a minimal solution? Why?
--
--   - How do I know that this reaches to a fixpoint? (programs have finite
--     number of lambdas)

solve :: Exp -> CFA
solve = solve' bot

solve' :: CFA -> Exp -> CFA
solve' cfa0 e0 = if next == cfa0 then cfa0 else solve' next e0
  where
    next = iter e0 cfa0

    iter (Var pp v) (CFA lblVals env) =
      let
        v_vals   = lookup v env
        lblVals' = alterSet v_vals pp lblVals
      in
        CFA lblVals' env

    iter e@(Lam pp _ body) (CFA lblVals env) =
      iter body $
      CFA (alterSet (S.singleton e) pp lblVals) env

    iter (App pp0 e1 e2) (CFA lblVals env) =
      let
        e1_lams = [ (pp, v, b) | Lam pp v b <- S.toList (lookup (getPP e1) lblVals) ]
        e2_vals = lookup (getPP e2) lblVals

        constr1 :: M.Map Id (S.Set Exp) -> (PP, Id, Exp) -> M.Map Id (S.Set Exp)
        constr1 env' (_, v, _) = alterSet e2_vals v env'

        constr2 :: M.Map PP (S.Set Exp) -> (PP, Id, Exp) -> M.Map PP (S.Set Exp)
        constr2 libVals' (_, _, b) =
          let
            p3_vals = lookup (getPP b) libVals'
          in
            alterSet p3_vals pp0 libVals'
      in
        iter e1 $
        iter e2 $
        CFA (foldl' constr2 lblVals e1_lams) (foldl' constr1 env e1_lams)

alterSet :: (Ord k, Ord a) => S.Set a -> k -> M.Map k (S.Set a) -> M.Map k (S.Set a)
alterSet s = M.alter (maybe (Just s) (Just . S.union s))

lookup :: Ord k => k -> M.Map k (S.Set Exp) -> S.Set Exp
lookup = M.findWithDefault S.empty

test :: Bool
test = solve example == solution
