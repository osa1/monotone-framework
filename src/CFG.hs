{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ViewPatterns #-}

module CFG
  ( CFG (..)
  , entryNode, exitNode
  , connectCFGs
  , funCFG
  , pgmCFG
  , concatCFGs
  ) where

--------------------------------------------------------------------------------

import Control.Monad (forM)
import Control.Monad.State.Strict (State, evalState, state)
import Control.Monad.Writer (WriterT, runWriterT, tell)
import Data.Graph
import qualified Data.Map as M
import qualified Data.Set as S

import qualified Array as A
import TIP.Syntax
import Utils

--------------------------------------------------------------------------------

data CFG = CFG
  { cfgGraph     :: !Graph
      -- ^ The actual control flow graph. Edges go to successors.
  , cfgNodeStmts :: !(A.Array Stmt)
      -- ^ Statements of nodes.
  }

-- | Only used as intermediate data.
data Block = Block
  { blockIdx   :: !Vertex
  , blockStmt  :: !Stmt
  , blockSuccs :: ![Vertex]
  } deriving (Show)

--------------------------------------------------------------------------------
-- Entry and exit nodes are having special treatment in analyses, so define them
-- here.

entryNode, exitNode, firstNode :: Vertex
entryNode = 1
exitNode  = 0
firstNode = 2

--------------------------------------------------------------------------------

-- | Generate control flow graph of a function.
funCFG :: Fun -> CFG
funCFG fun = CFG graph node_stmts
  where
    cfg_stuff :: [Block]
    cfg_stuff =
      Block exitNode Skip [] :
      evalState (iter entryNode exitNode (funBody fun)) firstNode

    graph :: Graph
    graph = A.fromAssocs $
            map (\b -> (blockIdx b, blockSuccs b)) cfg_stuff

    node_stmts :: A.Array Stmt
    node_stmts = A.fromAssocs $
                 map (\b -> (blockIdx b, blockStmt b)) cfg_stuff

    -- | Given current node index and node index of the continuation, generate
    -- list of blocks for a statement.
    iter
      :: Vertex -- ^ Current vertex
      -> Vertex -- ^ Continuation
      -> Stmt   -- ^ Statement of the block
      -> State Vertex [Block]

    -- Assignments and print statement have trivial control flow.
    iter cur_node cont stmt@(_ := _) = return [Block cur_node stmt [cont]]
    iter cur_node cont stmt@(_ :*= _) = return [Block cur_node stmt [cont]]
    iter cur_node cont stmt@(Output _) = return [Block cur_node stmt [cont]]
    iter cur_node cont stmt@Skip = return [Block cur_node stmt [cont]]

    iter cur_node cont (Seq stmt1 stmt2) = do
      stmt1_cont <- newBlock
      blocks1    <- iter cur_node stmt1_cont stmt1
      blocks2    <- iter stmt1_cont cont stmt2
      return (blocks1 ++ blocks2)

    iter cur_node cont stmt@(If _ stmt1 stmt2) = do
      then_node <- newBlock
      else_node <- newBlock
      then_blocks <- iter then_node cont stmt1
      else_blocks <- iter else_node cont stmt2
      return (Block cur_node stmt [then_node, else_node] : then_blocks ++ else_blocks)

    iter cur_node cont stmt@(While _ body) = do
      body_node <- newBlock
      body_blocks <- iter body_node cur_node body
      return (Block cur_node stmt [body_node, cont] : body_blocks)

    -- | Allocate a new block.
    newBlock :: State Vertex Vertex
    newBlock = state (\v -> (v, v + 1))

--------------------------------------------------------------------------------

-- | Concatenate a list of CFGs. Returns first nodes of CFGs in addition to the
-- combined CFG.
concatCFGs :: [(Id, CFG)] -> (CFG, [(Id, Int)])
concatCFGs cfgs =
    -- Just concatenate graph arrays and update indices, so that edges still
    -- point to right nodes.
    (CFG (A.fromList (concat graphs)) (A.fromList (concat stmts)), idxs)
  where
    (idxs, graphs, stmts) = unzip3 (concat_cfgs 0 cfgs)

    concat_cfgs _ [] = []
    concat_cfgs !cur_idx ((fun_id, CFG graph ss) : rest) =
      ( (fun_id, cur_idx),  map (map (+ cur_idx)) (A.toList graph), A.toList ss )
        : concat_cfgs (cur_idx + A.length graph) rest

-- | Final CFG will have all vertices in both CFGs. Edges will be added to given
-- vertices.
connectCFGs
  :: CFG
       -- ^ CFG that makes the jump.
  -> Vertex
      -- ^ The node that makes the jump. This node will have an outgoing edge to
      -- the other CFG's entry node.
  -> Vertex
      -- ^ Where to return after the other CFG. This node will have an incoming
      -- edge from other CFG's exit node.
  -> CFG
      -- ^ The CFG to connect.
  -> CFG

-- NOTE: This function relies on the fact that exit node is first node in graph,
-- and entry node is second.

connectCFGs cfg_from jump ret cfg_to =
    CFG new_cfg new_stmt_arr
  where
    cfg_from_size = A.length (cfgGraph cfg_from)

    -- jump target after node arrays are concatenated
    to_cfg_entry = cfg_from_size + 1

    -- update edges of cfg_to
    cfg_to_graph_updated =
      case map (map (+ cfg_from_size)) (A.toList (cfgGraph cfg_to)) of
        old_exit : rest -> (ret : old_exit) : rest
        _               -> error "connectCFGs: to CFG doesn't have enough nodes"

    -- update edges of cfg_from
    cfg_from_graph_updated =
      map (\(vtx, out_edges) -> if vtx == jump then to_cfg_entry : out_edges else out_edges)
          (A.assocs (cfgGraph cfg_from))

    -- new graph
    new_cfg =
      A.fromList (cfg_from_graph_updated ++ cfg_to_graph_updated)

    -- new statement array
    new_stmt_arr =
      A.fromList (A.toList (cfgNodeStmts cfg_from) ++ A.toList (cfgNodeStmts cfg_to))

--------------------------------------------------------------------------------

-- | Build a CFG with edges between functions, for interprocedural analysis.
-- Note that if a call target can't be resolved during CFG construction (e.g.
-- because of function pointers) there won't be an edge in call statement, and
-- some functions in the map may not be used at all.
--
-- A pre-processing step introduces temporaries for function calls.
pgmCFG :: M.Map Id Fun -> Id -> CFG
pgmCFG (introFunTemps -> funs) main =
    -- an internal state keeps track of functions that are merged to the main
    -- CFG
    undefined -- TODO: We need efficient graph updates here.
  where
    fun_cfgs = M.map funCFG funs
    combined_cfg = concatCFGs (M.toList fun_cfgs)

-- | Introduce temporaries to bind function call results. After this pass
-- function calls only appear in assignment right-hand sides.
introFunTemps :: M.Map Id Fun -> M.Map Id Fun
introFunTemps funs  =
    flip evalState 0 $
      forM funs $ \fun -> do
        (ret, new_locals) <- runWriterT (intro_temps (funBody fun))
        return fun{ funLocals = funLocals fun ++ S.toList new_locals, funBody = ret }
  where
    -- TODO: I really need a Writer-like monad with "add single element"
    -- function (instead of "tell" which uses mempty).

    intro_temps :: Stmt -> WriterT (S.Set Id) (State Int) Stmt

    intro_temps Skip = return Skip

    intro_temps (var := FunCall e es) = do
      -- fun result already bound to a variable so no need for a temporary
      (s,  e')  <- intro_temps_e e
      (ss, es') <- unzip <$> mapM intro_temps_e es
      return (stmts (s : ss) `seqs` (var := FunCall e' es'))

    intro_temps (var := e) = do
      (stmt, e') <- intro_temps_e e
      return (stmt `seqs` (var := e'))

    intro_temps (var :*= e) = do
      (stmt, e') <- intro_temps_e e
      return (stmt `seqs` (var :*= e'))

    intro_temps (Output e) = do
      (stmt, e') <- intro_temps_e e
      return (stmt `seqs` Output e')

    intro_temps (Seq s1 s2) =
      seqs <$> intro_temps s1 <*> intro_temps s2

    intro_temps (If e s1 s2) = do
      (s0, e') <- intro_temps_e e
      s1' <- intro_temps s1
      s2' <- intro_temps s2
      return (s0 `seqs` If e' s1' s2')

    intro_temps (While e s) = do
      (s0, e') <- intro_temps_e e
      s' <- intro_temps s
      return (s0 `seqs` While e' s')

    intro_temps_e :: Exp -> WriterT (S.Set Id) (State Int) (Stmt, Exp)

    intro_temps_e e@Int{} = return (Skip, e)

    intro_temps_e e@Var{} = return (Skip, e)

    intro_temps_e (FunCall e es) = do
      (s1, e')  <- intro_temps_e e
      (ss, es') <- unzip <$> mapM intro_temps_e es
      ret_var   <- fresh
      return (stmts (s1 : ss) `seqs` (ret_var := FunCall e' es'), Var ret_var)

    intro_temps_e (Binop e1 op e2) = do
      (s1, e1') <- intro_temps_e e1
      (s2, e2') <- intro_temps_e e2
      return (seqs s1 s2, Binop e1' op e2')

    intro_temps_e e@Input = return (Skip, e)

    intro_temps_e e@AddrOf{} = return (Skip, e)

    intro_temps_e e@Malloc = return (Skip, e)

    intro_temps_e (Deref e) = do
      (ss, e') <- intro_temps_e e
      return (ss, Deref e')

    intro_temps_e e@Null = return (Skip, e)

    fresh :: WriterT (S.Set Id) (State Int) Id
    fresh = do
      i <- state (\i -> (i, i + 1))
      let var = Id ("__fn_" ++ show i)
      tell (S.singleton var)
      return var

--------------------------------------------------------------------------------

showCFG :: CFG -> String
showCFG (CFG graph ss) = unlines (map (uncurry showBlock) (A.assocs ss))
  where
    showBlock :: Int -> Stmt -> String
    showBlock node stmt =
      let succs = graph A.! node
       in span_right 2 (show node) ++ ": " ++ show stmt ++ " (succs: " ++ show succs ++ ")"

instance Show CFG where
  show = showCFG
