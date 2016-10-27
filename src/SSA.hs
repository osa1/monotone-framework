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

import Control.Exception (assert)
import Data.Foldable (toList)
import qualified Data.Map.Strict as M
import Data.Sequence ((><), (|>))
import qualified Data.Sequence as Seq
import qualified Data.Set as S

import Control.Monad.State.Strict

import Debug.Trace (trace)
import Prelude hiding (mod, pred)

import Utils (span_right)

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
  , bbVarDefs    :: !(M.Map Var Var)
      -- ^ Exported values of variable in the basic block.
  , bbIsSealed   :: !Bool
      -- ^ Can more predecessors be added to the block?
  } deriving (Show)

emptyBasicBlock :: BBIdx -> BasicBlock
emptyBasicBlock bb_idx = BasicBlock bb_idx Seq.empty ReturnT M.empty M.empty False

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

-- | A map from a basic block to its predecessors in the control-flow graph.
type Preds = M.Map BBIdx (S.Set BBIdx)

-- | Make first basic block a predecessor of the second basic block.
mkPred :: BBIdx -> BBIdx -> Preds -> Preds
mkPred bb1 bb2 preds = M.alter (maybe (Just (S.singleton bb2)) (Just . S.insert bb2)) bb1 preds

-- preds :: BBIdx -> Preds -> S.Set BBIdx
-- preds bb edges = M.findWithDefault (error ("Can't find bb: " ++ show bb)) bb edges

newtype SsaM a = SsaM { runSsaM :: State SsaS a }
  deriving (Functor, Applicative, Monad, MonadState SsaS)

data SsaS = SsaS
  { incompletePhis  :: !(M.Map BBIdx (M.Map Var Phi))
      -- ^ Argument-less phi nodes added for breaking loops. When a block is
      -- sealed, we remove it from this map and update its phi nodes.
  , freshVarCount   :: !Int
      -- ^ Counter for fresh variable generation.
  , freshBlockCount :: !Int
      -- ^ Variable for fresh basic block generation.
  , predGraph       :: !Preds
      -- ^ Predecessor graph. Edge A to B means B is a predecessor of A in
      -- control flow graph.
  , blocks          :: !(M.Map BBIdx BasicBlock)
      -- ^ Basic blocks in the control flow graph.
  }

initSsaS :: SsaS
initSsaS = SsaS
  { incompletePhis  = M.empty
  , freshVarCount   = 0
  , freshBlockCount = 0
  , predGraph       = M.empty
  , blocks          = M.empty
  }

addPreds :: BBIdx -> [BBIdx] -> SsaM ()
addPreds bb preds = modify' $ \s -> s{ predGraph = adjust' (S.union (S.fromList preds)) bb (predGraph s) }

blockBB :: BBIdx -> SsaM BasicBlock
blockBB bb = M.findWithDefault (bbNotInGraph bb) bb <$> gets blocks

blockPreds :: BBIdx -> SsaM (S.Set BBIdx)
blockPreds bb = M.findWithDefault (bbNotInGraph bb) bb <$> gets predGraph

bbNotInGraph :: BBIdx -> a
bbNotInGraph bb = error ("Basic block " ++ show (bbInt bb) ++ " is not in the graph.")

--------------------------------------------------------------------------------
-- * Helpers, SsaM operations

modifyBB :: BBIdx -> (BasicBlock -> BasicBlock) -> SsaM ()
modifyBB bb f = modify' (\s -> s{ blocks = adjust' f bb (blocks s) })

addPhi :: BBIdx -> Var -> Phi -> [Var] -> SsaM ()
addPhi bb var phi args =
    modifyBB bb $ \b -> b{ bbPhis    = M.insert phi args (bbPhis b)
                         , bbVarDefs = M.insert var phi  (bbVarDefs b) }

-- | Set exported value in a basic block for a source variable.
writeVariable :: Var -> BBIdx -> Var -> SsaM ()
writeVariable var block val = modify' f
  where
    f st = st{ blocks = alter' (maybe (emptyBasicBlock block){ bbVarDefs = M.singleton var val }
                                      (\b -> b{ bbVarDefs = M.insert var val (bbVarDefs b) }))
                               block
                               (blocks st) }

-- | Read exported value of a variable in a basic block. Recursively query
-- predecessors if the variable is not defined in the block.
readVariable :: Var -> BBIdx -> SsaM Var
readVariable var block = do
    bs <- gets blocks
    maybe (readVariableRecursive var block) return $
      M.lookup block bs >>= M.lookup var . bbVarDefs

freshPhi, freshVar :: SsaM Var
freshPhi = freshVar
freshVar = state (\st -> (Var (freshVarCount st), st{ freshVarCount = freshVarCount st + 1 }))

-- | Recursively query exported values of predecessors for a given variable.
-- May introduce a phi node.
readVariableRecursive :: Var -> BBIdx -> SsaM Var
readVariableRecursive var block = do
    bb <- blockBB block
    preds <- S.toList <$> blockPreds block

    val <-
      if | not (bbIsSealed bb)
          -> -- new predecessors may be added to the block, introduce a phi and
             -- record it as "incomplete"
             do val <- freshPhi
                trace ("inserting incomplete phi for node " ++ show block) (return ())
                modify' $ \st ->
                  st{ incompletePhis =
                        modifyMap'' M.singleton M.insert var val block (incompletePhis st) }
                return val

         ------------------------------------
         -- other cases are for sealed blocks
         ------------------------------------

         | [pred] <- preds
          -> -- optimize the common case of one predecessor: No phi needed
             trace ("single pred") $
             readVariable var pred

         | otherwise
          -> -- break potential cycles with operandless phi
             do trace ("inserting operandless phi") (return ())
                val <- freshPhi
                writeVariable var block val
                phi_args <- mapM (readVariable var) preds
                addPhi block var val phi_args
                return val

    writeVariable var block val
    return val

freshBlock :: SsaM BBIdx
freshBlock =
    state $ \st ->
      let bb = freshBlockCount st in
      ( BBIdx bb
      , st{ freshBlockCount = bb + 1
          , blocks          = M.insert (BBIdx bb) (emptyBasicBlock (BBIdx bb)) (blocks st)
          , predGraph       = M.insert (BBIdx bb) S.empty (predGraph st) } )

-- | Mark a block as "sealed". A block is sealed when all of its predecessors
-- are known. We complete incomplete phis in the basic block when it's sealed.
--
-- We never ask predecessors of non-sealed blocks, so no need for actually
-- adding edges to the graph until a block is sealed.
sealBlock :: BBIdx -> SsaM ()
sealBlock block = do
    -- trace ("sealBlock: " ++ show bb) (return ())
    -- trace ("succs: " ++ show succs) (return ())
    incomplete_phis <-
      state (\s -> (incompletePhis s, s{ incompletePhis = M.delete block (incompletePhis s) }))

    trace ("incompletePhis: " ++ show incomplete_phis) (return ())
    let bb_incomplete_phis = M.findWithDefault M.empty block incomplete_phis

    -- ask predecessors for the values of this variable
    preds <- S.toList <$> blockPreds block
    bb_phis <-
      M.fromList <$>
        forM (M.toList bb_incomplete_phis)
          (\(var, var_phi) -> (var_phi,) <$> mapM (readVariable var) preds)

    trace ("bb_phis: " ++ show bb_phis) (return ())

    -- add the node to the graph
    modifyBB block $ \bb -> bb{ bbIsSealed = True
                              , bbPhis     = bb_phis `M.union` bbPhis bb }

--------------------------------------------------------------------------------

buildSSA :: Stmt -> ([BasicBlock], Preds)
buildSSA stmt =
    let
      ssa = execState (runSsaM (do entry <- freshBlock
                                   sealBlock entry
                                   buildSSA' stmt entry)) initSsaS
    in
      assert (M.null (incompletePhis ssa)) $
      assert (all bbIsSealed (M.elems (blocks ssa))) $
      (M.elems (blocks ssa), predGraph ssa)

buildSSA' :: Stmt -> BBIdx -> SsaM BBIdx

buildSSA' (Seq s1 s2) bb = buildSSA' s1 bb >>= buildSSA' s2

buildSSA' Skip bb = return bb

buildSSA' (Return e) bb  = do
    (e_var, e_stmts) <- bind_exp e bb
    -- terminate the basic block
    modifyBB bb $ \b -> b{ bbStmts = bbStmts b >< e_stmts
                         , bbTerminator = ReturnVar e_var }

    -- TODO: Not sure about that part. We need to make sure that after a return
    -- we don't extend current basic block anymore.
    return (BBIdx (-1))

buildSSA' (Asgn var rhs) bb = do
    (rhs', rhs_stmts) <- flatten_exp rhs bb
    var' <- freshVar
    writeVariable var bb var'
    modifyBB bb $ \b -> b{ bbStmts = (bbStmts b >< rhs_stmts) |> Asgn' var' rhs' }
    return bb


buildSSA' (If cond then_s else_s) bb = do
    then_b <- freshBlock
    else_b <- freshBlock
    cont_b <- freshBlock -- continuation

    addPreds cont_b [then_b, else_b]
    addPreds then_b [bb]
    addPreds else_b [bb]

    sealBlock then_b
    sealBlock else_b
    sealBlock cont_b

    (cond_var, cond_stmts) <- bind_exp cond bb
    modifyBB bb $ \b -> b{ bbStmts = bbStmts b >< cond_stmts
                         , bbTerminator = CondJmp cond_var then_b else_b }

    void (buildSSA' then_s then_b)
    void (buildSSA' else_s else_b)

    return cont_b

buildSSA' (While cond body) bb = do
    cond_b <- freshBlock
    body_b <- freshBlock
    cont_b <- freshBlock -- continuation

    addPreds cond_b [body_b, bb]
    addPreds body_b [cond_b]
    addPreds cont_b [cond_b]

    sealBlock cond_b
    sealBlock body_b
    sealBlock cont_b

    -- trace ("body_b: " ++ show body_b) (return ())
    -- trace ("cont_b: " ++ show cont_b) (return ())

    -- terminate current bb, jump to the condition
    modifyBB bb $ \b -> b{ bbTerminator = Jmp cond_b }

    -- condition
    (cond_var, cond_stmts) <- bind_exp cond cond_b
    modifyBB cond_b $ \b -> b{ bbStmts = cond_stmts, bbTerminator = CondJmp cond_var body_b cont_b }

    -- body
    void (buildSSA' body body_b)

    -- continuation
    return cont_b

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

-- | A variant of 'Data.Map.alter' that doesn't allow removing entries. Type
alter' :: Ord k => (Maybe a -> a) -> k -> M.Map k a -> M.Map k a
alter' f = M.alter (Just . f)

-- | A variant of 'Data.Map.adjust' that fails if key is not in the map.
adjust' :: (Show k, Ord k) => (a -> a) -> k -> M.Map k a -> M.Map k a
adjust' f k m
  | Just a <- M.lookup k m
  = M.insert k (f a) m
  | otherwise
  = error ("adjust': Key not in map: " ++ show k)

--------------------------------------------------------------------------------
-- * Examples

fig2 :: Stmt
fig2 =
    Asgn (Var 1) (Con Const) `Seq`
    While (Con Const) (If (Con Const) (Asgn (Var 1) (Con Const)) Skip) `Seq`
    Asgn (Var 3) (FunCall (X (Var 2)) [X (Var 1)])

runExample :: Stmt -> IO ()
runExample stmt = do
    let (blocks, preds) = buildSSA stmt
    putStrLn "=== BLOCKS ==="
    mapM_ (\b -> print_block b (M.findWithDefault (bbNotInGraph (bbIdx b)) (bbIdx b) preds)) blocks
  where
    print_block :: BasicBlock -> S.Set BBIdx -> IO ()
    print_block bb preds = do
      putStrLn (span_right 10 (show (bbInt (bbIdx bb))) ++ ": " ++ show (toList (bbStmts bb)))
      putStrLn (span_right 12 "preds: " ++ show (S.toList preds))
      putStrLn (span_right 12 "phis: " ++ show (M.toList (bbPhis bb)))
      putStrLn (span_right 10 "terminator: " ++ show (bbTerminator bb))
      putStrLn ""
