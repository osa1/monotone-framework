{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiWayIf                 #-}
{-# LANGUAGE TupleSections              #-}

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
import Data.Sequence ((><), (|>))
import qualified Data.Sequence as Seq
import qualified Data.Set as S

import Control.Monad.State

import Debug.Trace (trace)
import Prelude hiding (mod, pred)

import Data.Graph.Inductive.Dot (fglToDotString)
import Text.Dot (showDot)

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
  { bbIdx        :: !BBIdx
      -- ^ Basic block index in the control flow graph.
  , bbStmts      :: !(Seq.Seq Stmt')
      -- ^ Statements of the basic block.
  , bbTerminator :: !Terminator
      -- ^ What to do after the block.
  , bbPhis       :: !(M.Map Var [Var])
      -- ^ Phi nodes
  } deriving (Show)

emptyBasicBlock :: BBIdx -> BasicBlock
emptyBasicBlock bb_idx = BasicBlock bb_idx Seq.empty ReturnT M.empty

type CFG = G.Gr BasicBlock ()

type CFGNode = G.Context BasicBlock ()

data Stmt' = Asgn' Var Exp'
  deriving (Show)

data Terminator
  = Jmp BBIdx
  | CondJmp
      !Var    -- condition
      !BBIdx  -- if true jump here
      !BBIdx  -- if false jump here
  | ReturnVar Var
  | ReturnT
  deriving (Show)

data Exp'
  = Con' Const
  | Var' Var
  | FunCall' Var [Var]
  | Binop' Var Binop Var
  | Unop' Unop Var
  deriving (Show)

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
  }

initSsaS :: SsaS
initSsaS = SsaS
  { varDefs         = M.empty
  , sealedBlocks    = S.empty
  , incompletePhis  = M.empty
  , freshVarCount   = 0
  , freshBlockCount = 1
  , graph           = G.empty
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
                phi_ops <- readPhiOperands var val block
                gr <- gets graph
                let (preds, _, bb, succs) = G.context gr block
                merge (preds, block, bb{ bbPhis = M.insert val phi_ops (bbPhis bb) }, succs)
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
          , graph = G.insNode (bb, emptyBasicBlock bb) (graph st)
          } )

merge :: G.Context BasicBlock () -> SsaM ()
merge ctx = modify' $ \s -> s{ graph = ctx G.& graph s }

-- | Determine operands from predecessors.
readPhiOperands :: Var -> Var -> BBIdx -> SsaM [Var]
readPhiOperands var phi block = do
    st <- get
    let preds = G.pre (graph st) block
    mapM (readVariable var) preds

sealBlock :: BBIdx -> SsaM ()
sealBlock block = do
    SsaS{ incompletePhis = incomplete_phis, graph = gr } <- get

    -- ask predecessors for the values of this variable
    bb_phis <-
      M.fromList <$>
        forM (M.toList (M.findWithDefault M.empty block incomplete_phis))
          (\(var, var_phi) -> (var,) <$> readPhiOperands var var_phi block)

    -- add phi to the graph
    let (preds, _, bb, succs) = G.context gr block
    let gr' = (preds, block, bb{ bbPhis = bb_phis `M.union` bbPhis bb }, succs) G.& gr

    modify' $ \s -> s{ sealedBlocks = S.insert block (sealedBlocks s)
                     , graph = gr'
                     }


buildSSA :: Stmt -> CFG
buildSSA stmt = graph (execState (runSsaM (buildSSA' stmt ([], 0, emptyBasicBlock 0, []))) initSsaS)

buildSSA' :: Stmt -> CFGNode -> SsaM CFGNode

buildSSA' (Seq s1 s2) node = buildSSA' s1 node >>= buildSSA' s2

buildSSA' Skip node = return node

buildSSA' (Return e) (preds, cur_bb, bb, succs)  = do
    (e_var, e_stmts) <- bind_exp e cur_bb
    -- terminate the basic block
    let bb' = bb{ bbStmts = bbStmts bb >< e_stmts
                , bbTerminator = ReturnVar e_var }

    -- TODO: Not sure about that part. We need to make sure that after a return
    -- we don't extend current basic block anymore.
    -- merge (preds, cur_bb, bb', succs)
    return (preds, cur_bb, bb', succs)

buildSSA' (Asgn var rhs) (preds, cur_bb, bb, succs) = do
    (rhs', rhs_stmts) <- flatten_exp rhs cur_bb
    var' <- freshVar
    writeVariable var cur_bb var'
    return (preds, cur_bb, bb{ bbStmts = (bbStmts bb >< rhs_stmts) |> Asgn' var' rhs' }, succs)

buildSSA' (If cond then_s else_s) (preds, cur_bb, bb, _) = do
    then_b <- freshBlock
    else_b <- freshBlock
    cont_b <- freshBlock -- continuation

    (cond_var, cond_stmts) <- bind_exp cond cur_bb
    sealBlock cur_bb
    merge (preds, cur_bb, bb{ bbStmts = bbStmts bb >< cond_stmts
                            , bbTerminator = CondJmp cond_var then_b else_b }, [((), then_b), ((), else_b)])

    let branch_preds = [((), cur_bb)]
    let branch_succs = [((), cont_b)]
    merge =<< buildSSA' then_s (branch_preds, then_b, emptyBasicBlock then_b, branch_succs)
    sealBlock then_b
    merge =<< buildSSA' else_s (branch_preds, else_b, emptyBasicBlock else_b, branch_succs)
    sealBlock else_b

    let cont_preds = [((), then_b), ((), else_b)]
    let cont_ctx = (cont_preds, cont_b, emptyBasicBlock cont_b, [])
    merge cont_ctx
    sealBlock cont_b
    return cont_ctx

buildSSA' (While cond body) (preds, cur_bb, bb, succs) = do
    cond_b <- freshBlock
    body_b <- freshBlock
    cont_b <- freshBlock -- continuation

    -- terminate current bb, jump to the condition
    merge (preds, cur_bb, bb{ bbTerminator = Jmp cond_b }, ((), cond_b) : succs)

    -- condition
    (cond_var, cond_stmts) <- bind_exp cond cond_b
    merge ( [((), cur_bb)]
          , cond_b
          , BasicBlock cond_b cond_stmts (CondJmp cond_var body_b cont_b) M.empty
          , [((), cond_b)] )
    sealBlock cond_b

    -- body
    merge =<< buildSSA' body ([((), cond_b)], body_b, emptyBasicBlock body_b, [((), cond_b)])
    sealBlock body_b

    sealBlock cond_b

    -- continuation
    return ([((), cond_b)], cont_b, emptyBasicBlock cont_b, [])

bind_exp :: Exp -> BBIdx -> SsaM (Var, Seq.Seq Stmt')
bind_exp (Con c) _ = do
    v <- freshVar
    return (v, Seq.singleton (Asgn' v (Con' c)))
bind_exp (Var v) cur_bb = (, Seq.empty) <$> readVariable v cur_bb
bind_exp e cur_bb = do
    (e', e_stmts) <- flatten_exp e cur_bb
    v <- freshVar
    return (v, e_stmts |> Asgn' v e')

flatten_exp :: Exp -> BBIdx -> SsaM (Exp', Seq.Seq Stmt')
flatten_exp (Con c) _ = return (Con' c, Seq.empty)
flatten_exp (Var v) cur_bb = (, Seq.empty) . Var' <$> readVariable v cur_bb
flatten_exp (FunCall f as) cur_bb = do
    (f', f_stmts) <- bind_exp f cur_bb
    as' <- mapM (\a -> bind_exp a cur_bb) as
    return (FunCall' f' (map fst as'), f_stmts >< foldr (><) Seq.empty (map snd as'))
flatten_exp (Binop e1 op e2) cur_bb = do
    (e1', e1_stmts) <- bind_exp e1 cur_bb
    (e2', e2_stmts) <- bind_exp e2 cur_bb
    return (Binop' e1' op e2', e1_stmts >< e2_stmts)
flatten_exp (Unop op e) cur_bb = do
    (e', e_stmts) <- bind_exp e cur_bb
    return (Unop' op e', e_stmts)

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

--------------------------------------------------------------------------------
-- * Examples

fig2 :: Stmt
fig2 =
    Asgn 1 (Con Const) `Seq`
    While (Con Const) (If (Con Const) (Asgn 1 (Con Const)) Skip) `Seq`
    Asgn 3 (FunCall (Var 2) [Var 1])
