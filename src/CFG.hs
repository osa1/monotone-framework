module CFG
  ( CFG (..)
  , entryNode, exitNode
  , funCFG
  ) where

--------------------------------------------------------------------------------

import Control.Monad.State.Strict (State, evalState, state)
import Data.Array (Array, array, elems, (!))
import Data.Graph

import TIP.Syntax
import Utils

--------------------------------------------------------------------------------

data CFG = CFG
  { cfgGraph     :: !Graph
      -- ^ The actual control flow graph. Edges go to successors.
  , cfgNodeStmts :: !(Array Int Stmt)
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
    graph = array (0, length cfg_stuff - 1) $
            map (\b -> (blockIdx b, blockSuccs b)) cfg_stuff

    node_stmts :: Array Int Stmt
    node_stmts = array (0, length cfg_stuff - 1) $
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

showCFG :: CFG -> String
showCFG (CFG graph ss) = unlines (zipWith showBlock [ 0 .. ] (elems ss))
  where
    showBlock :: Int -> Stmt -> String
    showBlock node stmt =
      let succs = graph ! node
       in span_right 2 (show node) ++ ": " ++ show stmt ++ " (succs: " ++ show succs ++ ")"

instance Show CFG where
  show = showCFG
