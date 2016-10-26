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

import Data.Coerce (coerce)
import qualified Data.Graph.Inductive.Graph as G
import qualified Data.Graph.Inductive.PatriciaTree as G
import qualified Data.Map.Strict as M
import Data.Sequence ((><), (|>))
import qualified Data.Sequence as Seq
import qualified Data.Set as S

import Control.Monad.State.Strict

import Debug.Trace (trace)
import Prelude hiding (mod, pred)

import Data.Graph.Inductive.Dot (fglToDotString)
import Text.Dot (showDot)

--------------------------------------------------------------------------------
-- * AST definition

newtype Var = Var { varInt :: Int }
  deriving (Show, Eq, Ord)

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
  | X Var
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

newtype BBIdx = BBIdx { bbInt :: Int }
  deriving (Show, Eq, Ord)

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

type Adj     = [BBIdx]
type CFGNode = (Adj, BBIdx, BasicBlock, Adj)

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
  | X' Var
  | FunCall' Var [Var]
  | Binop' Var Binop Var
  | Unop' Unop Var
  deriving (Show)

--------------------------------------------------------------------------------
-- * SSA construction

-- BEWARE: State-monad-heavy code ahead. This needs a lot of refactoring.

type Phi = Var

newtype SsaM a = SsaM { runSsaM :: State SsaS a }
  deriving (Functor, Applicative, Monad, MonadState SsaS)

data SsaS = SsaS
  { varDefs         :: !(M.Map Var (M.Map BBIdx Var))
      -- ^ Exported variables.
  , sealedBlocks    :: !(S.Set BBIdx)
      -- ^ Blocks with known predecessors (i.e. no new predecessors will be
      -- added).
  , incompletePhis  :: !(M.Map BBIdx (M.Map Var Phi))
      -- ^ Argumnet-less phi nodes added for breaking loops.
  , freshVarCount   :: !Int
      -- ^ Counter for fresh variable generation.
  , freshBlockCount :: !Int
      -- ^ Variable for fresh basic block generation.
  , graph           :: !CFG
      -- ^ The control flow graph.
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

--------------------------------------------------------------------------------
-- * Helpers, SsaM operations

-- | Set exported value in a basic block for a source variable.
writeVariable :: Var -> BBIdx -> Var -> SsaM ()
writeVariable var block val = modify' f
  where
    f st = st{ varDefs = modifyMap'' M.singleton M.insert block val var (varDefs st) }

-- | Read exported value of a variable in a basic block. Recursively query
-- predecessors if the variable is not defined in the block.
readVariable :: Var -> BBIdx -> SsaM Var
readVariable var block = do
    defs <- gets varDefs
    maybe (readVariableRecursive var block) return $
      M.lookup var defs >>= M.lookup block

-- | Recursively query exported values of predecessors for a given variable.
-- May introduce a phi node.
readVariableRecursive :: Var -> BBIdx -> SsaM Var
readVariableRecursive var block = do
    gr <- gets graph
    sealeds <- gets sealedBlocks
    let preds = coerce (G.pre gr (bbInt block))

    val <-
      if | not (S.member block sealeds)
          -> -- new predecessors may be added to the block, introduce a phi and
             -- record it as "incomplete"
             do val <- freshPhi
                -- trace ("inserting incomplete phi for node " ++ show block) (return ())
                modify' $ \st ->
                  st{ incompletePhis =
                        modifyMap'' M.singleton M.insert var val block (incompletePhis st) }
                return val

         -- other cases are for sealed blocks

         | [pred] <- preds
          -> -- optimize the common case of one predecessor: No phi needed
             readVariable var pred

         | otherwise
          -> -- break potential cycles with operandless phi
             do val <- freshPhi
                writeVariable var block val
                phi_ops <- mapM (readVariable var) preds
                (_, _, bb, _) <- context block
                merge ([], block, bb{ bbPhis = M.insert val phi_ops (bbPhis bb) }, [])
                return val

    writeVariable var block val
    return val

freshPhi, freshVar :: SsaM Var
freshPhi = freshVar
freshVar = state (\st -> (Var (freshVarCount st), st{ freshVarCount = freshVarCount st + 1 }))

freshBlock :: SsaM BBIdx
freshBlock =
    state $ \st ->
      let bb = freshBlockCount st in
      ( BBIdx bb
      , st{ freshBlockCount = bb + 1
          , graph = G.insNode (bb, emptyBasicBlock (BBIdx bb)) (graph st)
          } )

edgeToFglEdge :: BBIdx -> ((), G.Node)
edgeToFglEdge bb_idx = ((), bbInt bb_idx)

edgesToFglEdges :: [BBIdx] -> G.Adj ()
edgesToFglEdges = map edgeToFglEdge

merge :: CFGNode -> SsaM ()
merge (preds, bb_idx, bb, succs) =
    modify' $ \s -> s{ graph = (edgesToFglEdges preds, bbInt bb_idx, bb, edgesToFglEdges succs) G.& graph s }

mergeCFG :: CFGNode -> CFG -> CFG
mergeCFG (preds, bb_idx, bb, succs) cfg =
    (edgesToFglEdges preds, bbInt bb_idx, bb, edgesToFglEdges succs) G.& cfg

context :: BBIdx -> SsaM CFGNode
context b = do
    gr <- gets graph
    let (preds, bb_idx, bb, succs) = G.context gr (bbInt b)
    return (map (BBIdx . snd) preds, BBIdx bb_idx, bb, map (BBIdx . snd) succs)

-- | Mark a block as "sealed". A block is sealed when all of its predecessors
-- are known. We complete incomplete phis in the basic block when it's sealed.
--
-- We never ask predecessors of non-sealed blocks, so no need for actually
-- adding edges to the graph until a block is sealed.
sealBlock :: CFGNode -> SsaM ()
sealBlock (preds, block, bb, succs) = do
    -- trace ("sealBlock: " ++ show bb) (return ())
    incomplete_phis <- gets incompletePhis
    -- trace ("incompletePhis: " ++ show incomplete_phis) (return ())
    let bb_incomplete_phis = M.findWithDefault M.empty block incomplete_phis

    -- ask predecessors for the values of this variable
    bb_phis <-
      M.fromList <$>
        forM (M.toList bb_incomplete_phis)
          (\(var, var_phi) -> (var_phi,) <$> mapM (readVariable var) preds)

    -- trace ("bb_phis: " ++ show bb_phis) (return ())

    -- add the node to the graph
    merge (preds, block, bb{ bbPhis = bb_phis `M.union` bbPhis bb }, succs)
    modify' $ \s -> s{ sealedBlocks   = S.insert block (sealedBlocks s)
                     , incompletePhis = M.delete block (incompletePhis s) }

--------------------------------------------------------------------------------

buildSSA :: Stmt -> CFG
buildSSA stmt =
    let
      (SsaS{ graph = gr, sealedBlocks = sealeds }) =
        execState (runSsaM (sealBlock =<< buildSSA' stmt ([], BBIdx 0, emptyBasicBlock (BBIdx 0), []))) initSsaS
    in
      -- trace ("sealed blocks: " ++ show sealeds) $
      gr

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
    sealBlock (preds, cur_bb, bb', succs)
    return ([], BBIdx (-1), emptyBasicBlock (BBIdx (-1)), [])

buildSSA' (Asgn var rhs) (preds, cur_bb, bb, succs) = do
    (rhs', rhs_stmts) <- flatten_exp rhs cur_bb
    var' <- freshVar
    writeVariable var cur_bb var'
    return (preds, cur_bb, bb{ bbStmts = (bbStmts bb >< rhs_stmts) |> Asgn' var' rhs' }, succs)

buildSSA' (If cond then_s else_s) (preds, cur_bb, bb, succs) = do
    then_b <- freshBlock
    else_b <- freshBlock
    cont_b <- freshBlock -- continuation

    (cond_var, cond_stmts) <- bind_exp cond cur_bb
    sealBlock (preds,
               cur_bb,
               bb{ bbStmts = bbStmts bb >< cond_stmts
                 , bbTerminator = CondJmp cond_var then_b else_b },
               [then_b, else_b])

    let branch_preds = [cur_bb]
    let branch_succs = [cont_b]
    sealBlock =<< buildSSA' then_s (branch_preds, then_b, emptyBasicBlock then_b, branch_succs)
    sealBlock =<< buildSSA' else_s (branch_preds, else_b, emptyBasicBlock else_b, branch_succs)

    return ([then_b, else_b], cont_b, emptyBasicBlock cont_b, succs)

buildSSA' (While cond body) (preds, cur_bb, bb, succs) = do
    cond_b <- freshBlock
    body_b <- freshBlock
    cont_b <- freshBlock -- continuation

    -- terminate current bb, jump to the condition
    sealBlock (preds, cur_bb, bb{ bbTerminator = Jmp cond_b }, [cond_b])

    -- condition
    (cond_var, cond_stmts) <- bind_exp cond cond_b
    sealBlock ( [cur_bb, body_b]
              , cond_b
              , BasicBlock cond_b cond_stmts (CondJmp cond_var body_b cont_b) M.empty
              , [body_b, cont_b] )

    -- body
    sealBlock =<< buildSSA' body ([cond_b], body_b, emptyBasicBlock body_b, [cond_b])

    -- continuation
    return ([cond_b], cont_b, emptyBasicBlock cont_b, succs)

bind_exp :: Exp -> BBIdx -> SsaM (Var, Seq.Seq Stmt')
bind_exp (Con c) _ = do
    v <- freshVar
    return (v, Seq.singleton (Asgn' v (Con' c)))
bind_exp (X v) cur_bb = (, Seq.empty) <$> readVariable v cur_bb
bind_exp e cur_bb = do
    (e', e_stmts) <- flatten_exp e cur_bb
    v <- freshVar
    return (v, e_stmts |> Asgn' v e')

flatten_exp :: Exp -> BBIdx -> SsaM (Exp', Seq.Seq Stmt')
flatten_exp (Con c) _ = return (Con' c, Seq.empty)
flatten_exp (X v) cur_bb = (, Seq.empty) . X' <$> readVariable v cur_bb
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
    Asgn (Var 1) (Con Const) `Seq`
    While (Con Const) (If (Con Const) (Asgn (Var 1) (Con Const)) Skip) `Seq`
    Asgn (Var 3) (FunCall (X (Var 2)) [X (Var 1)])

runExample :: IO ()
runExample = putStrLn (showDot ( (fglToDotString . G.nemap show (const "")) (buildSSA fig2)))
