{-# LANGUAGE TupleSections #-}

module CFG
  ( CFG (..)
  , entryNode, exitNode
  , funCFG
  , multiFunCFG
  , introFunTemps
  , insertCallStmts
  , cfgToDot
  ) where

--------------------------------------------------------------------------------

import Control.Monad (forM)
import Control.Monad.State.Strict (State, evalState, state)
import Control.Monad.Writer (WriterT, runWriterT, tell)
import Data.List (foldl')
import qualified Data.Map as M
import qualified Data.Set as S

import qualified Data.Graph.Inductive as G
import Data.Graph.Inductive.Dot (fglToDotString)
import qualified Data.Graph.Inductive.PatriciaTree as GI
import Text.Dot (Dot)

import TIP.Syntax
import Utils

import Prelude hiding (succ)

--------------------------------------------------------------------------------

-- | Control flow graph. Edges are to successors. Nodes are labelled with
-- statements.
data CFG = CFG
  { cfgGraph    :: GI.Gr Stmt ()
      -- ^ The actual graph
  , cfgFunExits :: M.Map Id G.Node
      -- ^ Exit nodes of functions in the CFG. Entry node is exit node + 1.
  }

emptyCFG :: CFG
emptyCFG = CFG G.empty M.empty

--------------------------------------------------------------------------------
-- Entry and exit nodes are having special treatment in analyses, so we define
-- them here.

entryNode, exitNode, firstNode :: G.Node
entryNode = 1
exitNode  = 0
firstNode = 2

--------------------------------------------------------------------------------

-- | Generate control flow graph of a single function.
funCFG :: Fun -> CFG
funCFG fun = CFG graph (M.singleton (funName fun) 0)
  where
    -- Exit node returns from the function
    exit_node :: G.LNode Stmt
    exit_node = (exitNode, Skip)

    graph :: GI.Gr Stmt ()
    graph =
      uncurry G.mkGraph $
        evalState (iter entryNode exitNode (funBody fun) ([exit_node], [])) firstNode

    -- | Given current node index and node index of the continuation, generate
    -- graph nodes and edges of the control flow graph.
    iter
      :: G.Node -- ^ Current node
      -> G.Node -- ^ Continuation. This should be a node in the accumulator.
      -> Stmt   -- ^ Statement of current node
      -> ( [G.LNode Stmt]
                -- Node accumulator.
         , [G.LEdge ()]
                -- Edge accumulator. We don't accumulate edges in the graph
                -- accumulator because we add edges to non-existing nodes during
                -- the construction.
         )
      -> State G.Node ([G.LNode Stmt], [G.LEdge ()])

    -- Call and Ret nodes are added after CFG is constructed
    iter _ _ Call{} _ = error "funCFG: Found Call statement"
    iter _ _ Ret{}  _ = error "funCFG: Found Ret statement"

    -- Assignments and print statement have trivial control flow.
    iter cur_node cont stmt@(_ := _)   acc = triv cur_node cont stmt acc
    iter cur_node cont stmt@(_ :*= _)  acc = triv cur_node cont stmt acc
    iter cur_node cont stmt@(Output _) acc = triv cur_node cont stmt acc
    iter cur_node cont stmt@Skip       acc = triv cur_node cont stmt acc

    iter cur_node cont (Seq stmt1 stmt2) acc = do
      stmt1_cont <- newBlock
      iter cur_node stmt1_cont stmt1 acc >>=
        iter stmt1_cont cont stmt2

    iter cur_node cont (If cond stmt1 stmt2) acc = do
      then_node <- newBlock
      else_node <- newBlock
      (ns, es) <- iter then_node cont stmt1 acc >>=
                    iter else_node cont stmt2
      return ( (cur_node, If cond Skip Skip) : ns
             , (cur_node, then_node, ()) :
               (cur_node, else_node, ()) :
               es
             )

    iter cur_node cont (While cond body) acc = do
      body_node <- newBlock
      (ns, es) <- iter body_node cur_node body acc
      return ( (cur_node, While cond Skip) : ns
             , (cur_node, body_node, ()) :
               (cur_node, cont, ()) :
               es
             )

    triv cur_node cont stmt (ns, es) =
      return ( (cur_node, stmt) : ns
             , (cur_node, cont, ()) : es )

    -- | Allocate a new block.
    newBlock :: State G.Node G.Node
    newBlock = state (\v -> (v, v + 1))

--------------------------------------------------------------------------------

-- | Generate a CFG for a list of functions. Graph nodes of functions won't be
-- connected.
multiFunCFG :: [Fun] -> CFG
multiFunCFG funs = foldl' iter emptyCFG fun_graphs
  where
    fun_graphs :: [(Fun, GI.Gr Stmt ())]
    fun_graphs = map (\fun -> (fun, cfgGraph (funCFG fun))) funs

    iter :: CFG -> (Fun, GI.Gr Stmt ()) -> CFG
    iter cur_cfg (fun, fun_graph) =
      let
        cur_graph   = cfgGraph cur_cfg
        cur_size    = G.noNodes cur_graph
        nodes_added = foldl' (\g (node, lbl) -> G.insNode (node + cur_size, lbl) g)
                             cur_graph (G.labNodes fun_graph)
        edges_added = foldl' (\g (from, to, lbl) -> G.insEdge (from + cur_size, to + cur_size, lbl) g)
                             nodes_added (G.labEdges fun_graph)
      in
        CFG { cfgGraph = edges_added
            , cfgFunExits = M.insert (funName fun) cur_size (cfgFunExits cur_cfg)
            }

-- | Insert  `Call` and `Ret` statements for interprocedural analysis.
--
-- This should be called after `introFunTemps` as it only looks for function
-- calls in form `id := f(...)`.
insertCallStmts :: CFG -> CFG
insertCallStmts cfg@(CFG graph funs) = cfg{ cfgGraph = go (G.nodes graph) avail_node_0 graph }
  where
    -- first available node slot in the CFG
    avail_node_0 = snd (G.nodeRange graph) + 1

    go :: G.DynGraph gr => [G.Node] -> G.Node -> gr Stmt () -> gr Stmt ()
    go []       _         gr = gr
    go (n : ns) free_node gr =
      let
        (_, _, stmt, succs) = G.context gr n
      in
        case stmt of
          ret_id := FunCall (Var fun_id) args

            | Just callee_exit <- M.lookup fun_id funs
            , [((), succ)] <- succs
            -> let
                 -- 1. Current node becomes a Call node with successors to
                 --    functions.
                 --
                 -- 2. We add a new "Ret" node with a successor to current
                 --    node's successor.
                 --
                 -- 3. Callee's exit gets a new successor to this "Ret" node.

                 -- entry node of the callee
                 callee_entry = callee_exit + 1

                 gr' =
                   G.insEdge (callee_exit, free_node, ()) $
                   G.insEdge (free_node, succ, ()) $
                   G.insNode (free_node, Ret ret_id) $
                   (G.&) ([], n, Call args, [((), callee_entry)]) $
                   G.delEdge (n, succ) $
                   gr
               in
                 go ns (free_node + 1) gr'

          _ -> go ns free_node gr

--------------------------------------------------------------------------------

-- | Introduce temporaries to bind function call results. After this pass
-- function calls only appear in assignment right-hand sides.
introFunTemps :: Traversable t => t Fun -> t Fun
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

    intro_temps Call{} = error "introFunTemps: Found Call statement"
    intro_temps Ret{}  = error "introFunTemps: Found Ret statement"

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
showCFG (CFG graph _) = unlines (map (showBlock . fst) (G.labNodes graph))
  where
    showBlock :: G.Node -> String
    showBlock node =
      let
        (preds, _, stmt, succs) = G.context graph node
      in
        span_right 2 (show node) ++
           ": " ++ show stmt ++ " (preds: " ++ show (map snd preds) ++ ") (sucss: " ++
           show (map snd succs) ++ ")"

instance Show CFG where
  show = showCFG

cfgToDot :: CFG -> Dot ()
cfgToDot = fglToDotString . G.nemap show (const "") . cfgGraph
