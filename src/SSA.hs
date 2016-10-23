{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiWayIf                 #-}

-- | Here we experiment with "static single assignment" form.
--
-- The main algorithm is described in "Simple and Efficient Construction of
-- Static Single Assignment Form". It's extended to handle labels.
-- (TODO: not yet)
module SSA where

--------------------------------------------------------------------------------

import Control.Monad (forM_)
import Data.Foldable (toList)
import qualified Data.Graph.Inductive.Graph as G
import qualified Data.Graph.Inductive.PatriciaTree as G
import qualified Data.Map as M
import Data.Sequence ((|>))
import qualified Data.Sequence as Seq
import qualified Data.Set as S

import Control.Monad.State

import Debug.Trace (trace)
import Prelude hiding (mod, pred)

--------------------------------------------------------------------------------
-- * AST definition

type Var = Int

data Stmt
  = Asgn Var Exp
  | If Exp Stmt Stmt
  | While Exp Stmt
  | Return Exp
  | Seq Stmt Stmt
      -- ^ Sequencing
  | Skip
      -- ^ Do nothing (empty block)
  deriving (Show)

data Exp
  = Con Const
  | Var Var
  | FunCall Exp [Exp]
  | Binop Exp Binop Exp
  | Unop Unop Exp
  deriving (Show)

data Binop = BOp   deriving (Show)
data Unop  = UOp   deriving (Show)
data Const = Const deriving (Show)

data Fun = Fun
  { funArgs :: [Var]
  , funBody :: Stmt
  } deriving (Show)

--------------------------------------------------------------------------------
-- * SSA definition

type BBIdx = Int

data BasicBlock = BasicBlock
  { bbId         :: !Int
  , bbStmts      :: ![Stmt']
  , bbTerminator :: !Terminator
  }

type CFG = G.Gr BasicBlock ()

data Stmt' = Asgn' Var Exp'

data Terminator
  = Jmp BBIdx
  | CondJmp
      !Var    -- condition
      !BBIdx  -- if true jump here
      !BBIdx  -- if false jump here
  | ReturnVar Var
  | ReturnT

data Exp'
  = Con' Const
  | Var' Var
  | FunCall' Var [Var]
  | Binop' Var Binop Var
  | Unop' Unop Var

--------------------------------------------------------------------------------
-- * SSA construction

-- BEWARE: State-monad-heavy code ahead. This needs a lot of refactoring.

type Phi = Int

newtype SsaM a = SsaM { runSsaM :: State SsaS a }
  deriving (Functor, Applicative, Monad, MonadState SsaS)

data SsaS = SsaS
  { varDefs         :: !(M.Map Var (M.Map BBIdx Var))
  , sealedBlocks    :: !(S.Set BBIdx)
  , incompletePhis  :: !(M.Map BBIdx (M.Map Var Phi))
  , freshVarCount   :: !Int
  , freshBlockCount :: !Int
  , graph           :: !CFG
  , currentBB       :: !BBIdx
  , currentStmts    :: !(Seq.Seq Stmt')
  }

initSsaS :: SsaS
initSsaS = SsaS
  { varDefs         = M.empty
  , sealedBlocks    = S.empty
  , incompletePhis  = M.empty
  , freshVarCount   = 0
  , freshBlockCount = 1
  , graph           = G.mkGraph [(0, BasicBlock 0 [] ReturnT)] []
  , currentBB       = 0
  , currentStmts    = Seq.empty
  }

writeVariable :: Var -> BBIdx -> Var -> SsaM ()
writeVariable var block val = modify' f
  where
    f st = st{ varDefs = modifyMap'' M.singleton M.insert block val var (varDefs st) }

readVariable :: Var -> BBIdx -> SsaM Var
readVariable var block = do
    defs <- gets varDefs
    maybe (readVariableRecursive var block) return $
      M.lookup block defs >>= M.lookup var

readVariableRecursive :: Var -> BBIdx -> SsaM Var
readVariableRecursive var block = do
    gr <- gets graph
    sealeds <- gets sealedBlocks
    let preds = G.pre gr block

    val <-
      if | S.member block sealeds
          -> do val <- freshPhi
                modify' $ \st ->
                  st{ incompletePhis =
                        modifyMap'' M.singleton M.insert var val block (incompletePhis st) }
                return val

         | [pred] <- preds
          -> -- optimize the common case of one predecessor: No phi needed
             readVariable var pred

         | otherwise
          -> -- break potential cycles with operandless phi
             do val <- freshPhi
                writeVariable var block val
                addPhiOperands var val block
                return val

    writeVariable var block val
    return val

freshPhi, freshVar :: SsaM Var
freshPhi = freshVar
freshVar = state (\st -> (freshVarCount st, st{ freshVarCount = freshVarCount st + 1 }))

freshBlock :: SsaM BBIdx
freshBlock =
    state $ \st ->
      let bb = freshBlockCount st in
      ( bb
      , st{ freshBlockCount = bb + 1
          , graph = G.insNode (bb, BasicBlock bb [] ReturnT) (graph st)
          } )

-- | Determine operands from predecessors
addPhiOperands :: Var -> Var -> BBIdx -> SsaM ()
addPhiOperands var phi block = do
    st <- get
    let preds = G.pre (graph st) block
    pred_vars <- mapM (readVariable var) preds
    -- TODO: try to remove trivial phis
    -- TODO: we don't keep phi operands yet
    trace ("phi operands: " ++ show pred_vars) (return ())

sealBlock :: BBIdx -> SsaM ()
sealBlock block = do
    incomplete_phis <- gets incompletePhis
    forM_ (M.toList (M.findWithDefault M.empty block incomplete_phis)) $
      \(var, var_phi) -> addPhiOperands var var_phi block
    modify' $ \s -> s{ sealedBlocks = S.insert block (sealedBlocks s) }

addStmt :: Stmt' -> SsaM ()
addStmt stmt = modify' $ \s -> s{ currentStmts = currentStmts s |> stmt }

setCurBB :: BBIdx -> SsaM ()
setCurBB bb = modify' $ \s -> s{ currentBB = bb, currentStmts = Seq.empty }

setGraph :: CFG -> SsaM ()
setGraph gr = modify' $ \s -> s{ graph = gr }

terminate :: BBIdx -> SsaM ()
terminate dest = do
    SsaS{ graph = gr, currentBB = cur_bb } <- get
    let (preds, _, bb, succs) = G.context gr cur_bb
    let gr' = (preds, cur_bb, bb{ bbTerminator = Jmp dest }, ((), dest) : succs) G.& gr
    modify' $ \s -> s{ graph = gr' }

buildSSA :: Stmt -> SsaM ()

buildSSA (Seq s1 s2) = buildSSA s1 >> buildSSA s2

buildSSA Skip        = return ()

buildSSA (Return e)  = do
    e' <- bind_exp e

    -- terminate current basic block
    SsaS{ graph = gr, currentStmts = stmts, currentBB = cur_bb } <- get
    let (preds, _, _, succs) = G.context gr cur_bb
    let bb = BasicBlock cur_bb (toList stmts) (ReturnVar e')
    let gr' = (preds, cur_bb, bb, succs) G.& gr

    setGraph gr'
    setCurBB (-1)

buildSSA (Asgn var rhs) = do
    rhs' <- flatten_exp rhs
    var' <- freshVar
    cur_bb <- gets currentBB
    writeVariable var cur_bb var'
    modify' $ \s -> s{ currentStmts = currentStmts s |> Asgn' var' rhs' }

buildSSA (If cond then_s else_s) = do
    cond'  <- bind_exp cond
    then_b <- freshBlock
    else_b <- freshBlock
    cont_b <- freshBlock

    SsaS{ graph = gr, currentStmts = stmts, currentBB = cur_bb } <- get
    let bb = BasicBlock cur_bb (toList stmts) (CondJmp cond' then_b else_b)
    let (preds, _, _, _) = G.context gr cur_bb
    let gr' = (preds, cur_bb, bb, [((), then_b), ((), else_b)]) G.& gr

    -- then branch
    setGraph gr'
    setCurBB then_b
    buildSSA then_s
    terminate cont_b

    -- else branch
    setCurBB else_b
    buildSSA else_s
    terminate cont_b

    setCurBB cont_b

buildSSA (While cond body) = do
    cond'  <- bind_exp cond
    body_b <- freshBlock
    cont_b <- freshBlock

    SsaS{ graph = gr, currentStmts = stmts, currentBB = cur_bb } <- get
    let bb = BasicBlock cur_bb (toList stmts) (CondJmp cond' body_b cont_b)
    let (preds, _, _, _) = G.context gr cur_bb
    let gr' = (preds, cur_bb, bb, [((), body_b), ((), cont_b)]) G.& gr

    -- body
    setGraph gr'
    setCurBB body_b
    buildSSA body
    terminate cont_b

    -- continuation
    setCurBB cont_b

flatten_exp :: Exp -> SsaM Exp'
flatten_exp (Con c) = return (Con' c)
flatten_exp (Var v) = gets currentBB >>= fmap Var' . readVariable v
flatten_exp (FunCall f as) = FunCall' <$> bind_exp f <*> mapM bind_exp as
flatten_exp (Binop e1 op e2) = do
    e1' <- bind_exp e1
    e2' <- bind_exp e2
    return (Binop' e1' op e2')
flatten_exp (Unop op e) = Unop' op <$> bind_exp e

bind_exp :: Exp -> SsaM Var

bind_exp (Con c) = do
    v <- freshVar
    addStmt (Asgn' v (Con' c))
    return v

bind_exp (Var v) = gets currentBB >>= readVariable v

bind_exp e = do
    e' <- flatten_exp e
    v  <- freshVar
    addStmt (Asgn' v e')
    return v

--------------------------------------------------------------------------------
-- * Utils

modifyMap''
  :: Ord k0
  => (k -> v -> m)
        -- ^ Singleton function
  -> (k -> v -> m -> m)
        -- ^ Update function
  -> k -> v
  -> k0 -- ^ Key
  -> M.Map k0 m
  -> M.Map k0 m
modifyMap'' singl mod k v key m =
  modifyMap' (singl k v) (mod k v) key m

modifyMap' :: Ord k => a -> (a -> a) -> k -> M.Map k a -> M.Map k a
modifyMap' ins mod = modifyMap (maybe ins mod)

modifyMap :: Ord k => (Maybe a -> a) -> k -> M.Map k a -> M.Map k a
modifyMap a k m = M.alter (Just . a) k m
