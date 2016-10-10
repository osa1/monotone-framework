{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns        #-}

-- | Definition of a lattice, as described in section 4.2.
module Main where

import Data.Array (Array, array, elems, (!))
import Data.Graph
import Data.List (foldl', intercalate)
import qualified Data.Map.Strict as M
import Data.Maybe (fromJust, fromMaybe)
import qualified Data.Set as S
import Data.String (IsString (..))
import GHC.Generics

import Control.Monad.State.Strict (State, evalState, state)

import Prelude hiding (exp, id, span)

import Control.DeepSeq

import Debug.Trace

--------------------------------------------------------------------------------
-- First we define our syntax.

-- | Expressions
data Exp
  = Int Int
      -- ^ Integer literal
  | Var Id
      -- ^ Variable
  | FunCall Exp [Exp]
      -- ^ Function call
  | Binop Exp Binop Exp
      -- ^ Binary operation
  | Input
      -- ^ Read an integer from stdin.
  | AddrOf Id
      -- ^ Address of a variable. Like `&` in C.
  | Malloc
      -- ^ Allocate memory.
  | Deref Exp
      -- ^ Dereference a pointer. Like `*` in C.
  | Null
      -- ^ Null pointer literal
  deriving (Show, Eq, Ord)

instance IsString Exp where
  fromString = Var . Id

-- | Binary operators
data Binop = Plus | Minus | Mult | Div | Gt | Eq
  deriving (Show, Eq, Ord)

-- | Identifiers are just Haskell strings.
newtype Id = Id { unwrapId :: String }
  deriving (Eq, Ord)

instance IsString Id where
  fromString = Id

instance Show Id where
  show = unwrapId

-- | Statements
data Stmt
  = Skip
      -- ^ As a placeholder in empty blocks (e.g. entry and exit blocks)
  | Id := Exp
      -- ^ Assignment
  | Id :*= Exp
      -- ^ Move to the address.
  | Output Exp
      -- ^ Print to stdout.
  | Seq Stmt Stmt
      -- ^ Sequencing
  | If Exp Stmt Stmt
      -- ^ Conditional
  | While Exp Stmt
      -- ^ Loop
  deriving (Show)

stmts :: [Stmt] -> Stmt
stmts = foldr1 Seq

-- | Functions
data Fun = Fun
  { funName   :: Id
      -- ^ Function name
  , funArgs   :: [Id]
      -- ^ Arguments
  , funLocals :: [Id]
      -- ^ Local variables
  , funBody   :: Stmt
      -- ^ The body
  , funRet    :: Exp
      -- ^ Return value
  }

funVars :: Fun -> S.Set Id
funVars fun = S.fromList (funArgs fun) `S.union` S.fromList (funLocals fun)

-- Example programs from section 2.2

ite :: Fun
ite = Fun
  { funName   = "ite"
  , funArgs   = ["n"]
  , funLocals = ["f"]
  , funBody   = stmts
      [ "f" := Int 1
      , While (Binop "n" Gt (Int 0)) $ stmts
          [ "f" := Binop "f" Mult "n"
          , "n" := Binop "n" Minus (Int 1)
          ]
      ]
  , funRet    = Var "f"
  }

rec :: Fun
rec = Fun
  { funName   = "rec"
  , funArgs   = ["n"]
  , funLocals = ["f"]
  , funBody   = stmts
      [ If (Binop "n" Eq (Int 0))
           ("f" := Int 1)
           ("f" := Binop "n" Mult (FunCall "rec" [Binop "n" Minus (Int 1)]))
      ]
  , funRet    = "f"
  }

-- Next two programs go together
foo, main' :: Fun
foo = Fun
  { funName   = "foo"
  , funArgs   = ["p", "x"]
  , funLocals = ["f", "q"]
  , funBody   = stmts
      [ If (Binop (Deref "p") Eq (Int 0))
           ("f" := Int 1)
           (stmts [ "q" := Malloc
                  , "q" :*= Binop (Deref "p") Minus (Int 1)
                  , "f" := Binop (Deref "p") Mult (FunCall "x" ["q", "x"])
                  ])
      ]
  , funRet    = "f"
  }

bar :: Fun
bar = Fun
  { funName = "bar"
  , funArgs = []
  , funLocals = ["x", "y", "i"]
  , funBody = stmts
      [ "x" := Int 0   -- node 1
      , "y" := Int 1   -- node 2
      , "i" := Int 100 -- node 3
      , While (Binop "i" Gt (Int 0)) $ stmts -- node 4
          [ "y" := Binop "y" Mult (Int 2) -- node 5
          , "x" := Binop "x" Plus "y" -- node 6
          , "i" := Binop "i" Minus (Int 1) -- node 7
          ]
      ]
  , funRet = "x"
  }

main' = Fun
  { funName   = "main"
  , funArgs   = []
  , funLocals = ["n"]
  , funBody   = "n" := Input
  , funRet    = FunCall "foo" [AddrOf "n", "foo"]
  }

--------------------------------------------------------------------------------
-- Done with the syntax and programs. Before moving on to the analysis, we need
-- to define one more thing: control flow graph.

data CFG = CFG
  { cfgGraph     :: !Graph
      -- ^ The actual graph.
  , cfgNodeStmts :: !(Array Int Stmt)
      -- ^ Statements of nodes.
  }

-- | Only used as intermediate data.
data Block = Block
  { blockIdx   :: !Vertex
  , blockStmt  :: !Stmt
  , blockSuccs :: ![Vertex]
  } deriving (Show)

entryNode, exitNode, firstNode :: Vertex
entryNode = 0
exitNode  = 1
firstNode = 2

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
      -> Stmt -> State Vertex [Block]

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

-- | A semilattice is a set with "join" operation.
data SemiLattice a = SemiLattice
  { join   :: !(a -> a -> a)
      -- ^ Join (or "least upper bound"). Must be idempotent, commutative, and
      -- associative.
  , bottom :: !a
      -- ^ Bottom is an unique element such that `forall a . join bottom a == a`.
  }

-- We'll actually need a "bounded semilattice", which can be achieved just by
-- adding `Bounded a => ...` constraint. More on this later.

-- The paper "Monotone Data Flow Analysis Frameworks" defines a framework as a
-- semilattice + a function space (of transfer functions). I don't find this
-- definition too useful. So we just focus on instances.

-- | A "monotone data flow analysis" is a semilattice, a flow graph, and a
-- mapping from flow graph nodes to transfer functions.
data FlowAnalysis a = FlowAnalysis
  { lattice          :: !(SemiLattice a)
      -- ^ The lattice
  , flowGraph        :: !CFG
      -- ^ The flow graph
  , transferFunction :: !(Vertex -> ([a] -> a))
      -- ^ Transfer functions
  }

-- Goal: Find maximal solution. E.g. a solution MS such that, for every solution
-- S, "S `meet` MS = S", or in other words, "S <= MS".

-- solve :: forall a . (NFData a, Eq a) => FlowAnalysis a -> [a]
solve flowAnal =
    -- start with the bottom, apply transfer functions repeatedly until a
    -- fixpoint
    run l0
  where
    l0  = replicate (length vtx) (bottom (lattice flowAnal))

    vtx = vertices (cfgGraph (flowGraph flowAnal))
    transfer_functions = map (transferFunction flowAnal) vtx

    -- This is what's called "combined function F : L^n -> L^n" in Chapter 5.
    -- f :: [a] -> [a]
    f as = map ($ as) transfer_functions

    run l =
      let next = f l
       in if next == l then l else run next

--------------------------------------------------------------------------------
-- * Sign analysis

data Sign1
  = Pos | Neg | Zero
  | Top    -- ^ set of all integers
  | Bottom -- ^ empty set
  deriving (Show, Eq, Generic, NFData)

sign1Join, sign1LUB :: Sign1 -> Sign1 -> Sign1
sign1Join Top    _      = Top
sign1Join _      Top    = Top
sign1Join Bottom x      = x
sign1Join x      Bottom = x
sign1Join Pos    Pos    = Pos
sign1Join Neg    Neg    = Neg
sign1Join Zero   Zero   = Zero
sign1Join _      _      = Top

-- just a synonym
sign1LUB = sign1Join

sign1Lattice :: SemiLattice Sign1
sign1Lattice = SemiLattice
  { join   = sign1Join
  , bottom = Bottom
  }


varMapLattice :: S.Set Id -> SemiLattice a -> SemiLattice (M.Map Id a)
varMapLattice vars l = SemiLattice
  { join   = M.unionWith (join l)
  , bottom = M.fromList (zip (S.toList vars) (repeat (bottom l)))
  }

-- | Abstract evaluation.
eval :: M.Map Id Sign1 -> Exp -> Sign1
eval env exp =
  case exp of
    Int i
      | i > 0     -> Pos
      | i < 0     -> Neg
      | otherwise -> Zero
    Var v -> fromJust (M.lookup v env)
    Binop e1 op e2 -> applyOp op (eval env e1) (eval env e2)
    _ -> Top

applyOp :: Binop -> Sign1 -> Sign1 -> Sign1

-- addition
applyOp Plus Bottom  _       = Bottom
applyOp Plus _       Bottom  = Bottom
applyOp Plus Top     _       = Top
applyOp Plus _       Top     = Top
applyOp Plus Pos     Pos     = Pos
applyOp Plus Pos     Neg     = Top
applyOp Plus Pos     Zero    = Pos
applyOp Plus Neg     Pos     = Top
applyOp Plus Neg     Neg     = Neg
applyOp Plus Neg     Zero    = Neg
applyOp Plus Zero    Pos     = Pos
applyOp Plus Zero    Neg     = Neg
applyOp Plus Zero    Zero    = Zero

-- negation
applyOp Minus Bottom  _      = Bottom
applyOp Minus _       Bottom = Bottom
applyOp Minus Top     _      = Top
applyOp Minus _       Top    = Top
applyOp Minus Pos     Pos    = Top
applyOp Minus Pos     Neg    = Pos
applyOp Minus Pos     Zero   = Pos
applyOp Minus Neg     Pos    = Neg
applyOp Minus Neg     Neg    = Top
applyOp Minus Neg     Zero   = Neg
applyOp Minus Zero    Pos    = Neg
applyOp Minus Zero    Neg    = Pos
applyOp Minus Zero    Zero   = Zero

-- multiplication
applyOp Mult Bottom  _       = Bottom
applyOp Mult _       Bottom  = Bottom
applyOp Mult Top     Zero    = Zero
applyOp Mult Top     _       = Top
applyOp Mult Pos     Pos     = Pos
applyOp Mult Pos     Neg     = Neg
applyOp Mult Pos     Zero    = Zero
applyOp Mult Pos     Top     = Top
applyOp Mult Neg     Pos     = Neg
applyOp Mult Neg     Neg     = Pos
applyOp Mult Neg     Zero    = Zero
applyOp Mult Neg     Top     = Top
applyOp Mult Zero    _       = Zero

-- division
applyOp Div Bottom  _        = Bottom
applyOp Div _       Bottom   = Bottom
applyOp Div Top     _        = Top
applyOp Div _       Top      = Top
applyOp Div Pos     Pos      = Pos
applyOp Div Pos     Neg      = Neg
applyOp Div Pos     Zero     = Bottom -- IMPORTANT! optimization opportunity
applyOp Div Neg     Pos      = Neg
applyOp Div Neg     Neg      = Pos
applyOp Div Neg     Zero     = Bottom
applyOp Div Zero    Pos      = Zero
applyOp Div Zero    Neg      = Zero
applyOp Div Zero    Zero     = Bottom

-- other operators don't return integers
applyOp Gt _ _               = Bottom -- Not Top!
applyOp Eq _ _               = Bottom -- Not Top!

sign1FlowAnal :: Fun -> FlowAnalysis (M.Map Id Sign1)
sign1FlowAnal fun = FlowAnalysis
  { lattice          = lat
  , flowGraph        = cfg
  , transferFunction = transfer_fun
  }
  where
    lat = varMapLattice (funVars fun) sign1Lattice
    cfg = funCFG fun
    cfg_transposed = transposeG (cfgGraph cfg)

    transfer_fun :: Vertex -> [M.Map Id Sign1] -> M.Map Id Sign1
    transfer_fun vtx ls =
      let
        -- predecessors of the node
        preds = cfg_transposed ! vtx
        -- node statement
        stmt = cfgNodeStmts cfg ! vtx
        -- lattices of predecessors
        pred_lats = map (\p -> ls !! p) preds
        join_ = foldl' (join lat) (bottom lat) pred_lats
      in
        case stmt of
          var := rhs -> M.insert var (eval join_ rhs) join_
          Seq{}      -> error "Seq in CFG."
          _          -> join_

--------------------------------------------------------------------------------
-- * Liveness analysis

-- | Liveness analysis lattice is parametric on program variables. Lattice
-- values are supersets of set of all variables in the program.
livenessAnalLat :: S.Set Id -> SemiLattice (S.Set Id)
livenessAnalLat vars = SemiLattice
  { join   = S.union
  , bottom = S.empty
  }

expVars :: Exp -> S.Set Id
expVars Int{}           = S.empty
expVars (Var id)        = S.singleton id
expVars (FunCall e1 es) = S.unions (map expVars (e1 : es))
expVars (Binop e1 _ e2) = expVars e1 `S.union` expVars e2
expVars Input{}         = S.empty
expVars (AddrOf id)     = S.singleton id
expVars Malloc          = S.empty
expVars (Deref e)       = expVars e
expVars Null            = S.empty

livenessAnal :: S.Set Id -> Fun -> FlowAnalysis (S.Set Id)
livenessAnal vars fun = FlowAnalysis
  { lattice          = lat
  , flowGraph        = cfg
  , transferFunction = transfer_fun
  }
  where
    lat = livenessAnalLat vars
    cfg = funCFG fun

    transfer_fun :: Vertex -> [S.Set Id] -> S.Set Id
    transfer_fun 0   _  = expVars (funRet fun)
    transfer_fun vtx ls =
      let
        -- sucessors of the node
        succs = cfgGraph cfg ! vtx
        -- node statement
        stmt = cfgNodeStmts cfg ! vtx
        -- lattices of successors
        succ_lats = map (\p -> ls !! p) succs
        join_ = foldl' (join lat) (bottom lat) succ_lats
      in
        case stmt of
          Skip      -> join_
          id := e   -> S.delete id join_ `S.union` expVars e
          id :*= e  -> S.delete id join_ `S.union` expVars e
          Output e  -> join_ `S.union` expVars e
          Seq{}     -> error "Seq in CFG."
          If e _ _  -> join_ `S.union` expVars e
          While e _ -> join_ `S.union` expVars e

livenessExample :: Fun
livenessExample = Fun
  { funName = "le"
  , funArgs = []
  , funLocals = ["x", "y", "z"]
  , funBody = stmts
      [ "x" := Input -- 1
      , While (Binop "x" Gt (Int 1)) $ stmts -- 2
          [ "y" := Binop "x" Div (Int 2) -- 3
          , If (Binop "y" Gt (Int 3)) -- 4
               ("x" := Binop "x" Minus "y") -- 5
               Skip -- 6
          , "z" := Binop "x" Minus (Int 4) -- 7
          , If (Binop "z" Gt (Int 0)) -- 7
               ("x" := Binop "x" Div (Int 2)) -- 9
               Skip -- 10
          , "z" := Binop "z" Minus (Int 1) -- 11
          ]
      , Output "x" -- 12
      ]
  , funRet = Null
  }

--------------------------------------------------------------------------------
-- * Available expressions

-- | Set of all expressions in a statement.
stmtExps :: Stmt -> S.Set Exp
stmtExps Skip = S.empty
stmtExps (_ := e) = subExps e
stmtExps (_ :*= e) = subExps e
stmtExps (Output e) = subExps e
stmtExps (Seq s1 s2) = stmtExps s1 `S.union` stmtExps s2
stmtExps (If e s1 s2) = subExps e `S.union` stmtExps s1 `S.union` stmtExps s2
stmtExps (While e s) = subExps e `S.union` stmtExps s

-- | Set of all expression in the program. See `availExprLat`.
funExps :: Fun -> S.Set Exp
funExps = stmtExps . funBody

-- | The set of all subexpressions of an expression.
-- (the expression itself will be in the set)
subExps :: Exp -> S.Set Exp
subExps e@Int{} = S.singleton e
subExps e@Var{} = S.singleton e
subExps e@(FunCall e1 es) = S.insert e (S.unions (subExps e1 : map subExps es))
subExps e@(Binop e1 _ e2) = S.insert e (subExps e1 `S.union` subExps e2)
subExps e@Input = S.singleton e
subExps e@(AddrOf x) = S.fromList [ e, Var x ] -- CARE
subExps e@Malloc = S.singleton e
subExps e@(Deref e1) = S.insert e (subExps e1)
subExps e@Null = S.singleton e

-- | Remove expressions from the set that reference to the given id.
removeReferencing :: S.Set Exp -> Id -> S.Set Exp
removeReferencing s x = S.filter (\e -> not (S.member (Var x) (subExps e))) s

-- | The lattice elements are all supersets of all expression in the program.
availExprLat :: Fun -> SemiLattice (S.Set Exp)
availExprLat fun = SemiLattice
  { join   = S.intersection
  , bottom = funExps fun
  }

availExprAnal :: Fun -> FlowAnalysis (S.Set Exp)
availExprAnal fun = FlowAnalysis
  { lattice          = lat
  , flowGraph        = cfg
  , transferFunction = transfer_fun
  }
  where
    lat = availExprLat fun
    cfg = funCFG fun
    cfg_transposed = transposeG (cfgGraph cfg)

    transfer_fun :: Vertex -> [S.Set Exp] -> S.Set Exp
    transfer_fun vtx _
      | vtx == entryNode = S.empty
    transfer_fun vtx ls =
      let
        -- predecessors of the node
        preds = cfg_transposed ! vtx
        -- node statement
        stmt = cfgNodeStmts cfg ! vtx
        -- lattices of predecessors
        pred_lats = map (\p -> ls !! p) preds
        join_ = foldl' (join lat) (bottom lat) pred_lats
      in
        case stmt of
          Skip      -> join_
          x := e    -> removeReferencing (join_ `S.union` subExps e) x
          x :*= e   -> removeReferencing (join_ `S.union` subExps e) x
          Output e  -> join_ `S.union` subExps e
          Seq{}     -> error "Seq in CFG."
          If e _ _  -> join_ `S.union` subExps e
          While e _ -> join_ `S.union` subExps e

availExpr_test :: Fun
availExpr_test = Fun
  { funName = "ae_test"
  , funArgs = []
  , funLocals = ["x", "y", "z", "a", "b"]
  , funBody = stmts
      [ "z" := Binop "a" Plus "b"
      , "y" := Binop "a" Mult "b"
      , While (Binop "y" Gt (Binop "a" Plus "b")) $ stmts
          [ "a" := Binop "a" Plus (Int 1)
          , "x" := Binop "a" Plus "b"
          ]
      ]
  , funRet = Null
  }

--------------------------------------------------------------------------------
-- * Very busy expressions

-- | The lattice is the same as "available expressions" lattice.
veryBusyExprLat :: Fun -> SemiLattice (S.Set Exp)
veryBusyExprLat = availExprLat

veryBusyExprAnal :: Fun -> FlowAnalysis (S.Set Exp)
veryBusyExprAnal fun = FlowAnalysis
  { lattice          = lat
  , flowGraph        = cfg
  , transferFunction = transfer_fun
  }
  where
    lat = veryBusyExprLat fun
    cfg = funCFG fun

    transfer_fun :: Vertex -> [S.Set Exp] -> S.Set Exp
    transfer_fun vtx _
      | vtx == exitNode = S.empty
    transfer_fun vtx ls =
      let
        -- successors of the node
        succs = cfgGraph cfg ! vtx
        -- node statement
        stmt = cfgNodeStmts cfg ! vtx
        -- lattices of successors
        succ_lats = map (\p -> ls !! p) succs
        join_ = foldl' (join lat) (bottom lat) succ_lats
      in
        case stmt of
          Skip      -> join_
          x := e    -> removeReferencing join_ x `S.union` subExps e
          x :*= e   -> removeReferencing join_ x `S.union` subExps e
          Output e  -> join_ `S.union` subExps e
          Seq{}     -> error "Seq in CFG."
          If e _ _  -> join_ `S.union` subExps e
          While e _ -> join_ `S.union` subExps e

veryBusyExpr_test :: Fun
veryBusyExpr_test = Fun
  { funName = ""
  , funArgs = []
  , funLocals = ["x", "a", "b"]
  , funBody = stmts
      [ "x" := Input
      , "a" := Binop "x" Minus (Int 1)
      , "b" := Binop "x" Minus (Int 2)
      , While (Binop "x" Gt (Int 0)) $ stmts
          [ Output (Binop (Binop "a" Mult "b") Minus "x")
          , "x" := Binop "x" Minus (Int 1)
          ]
      , Output (Binop "a" Mult "b")
      ]
  , funRet = Null
  }

--------------------------------------------------------------------------------
-- * Constant propagation

-- | Out lattice elements for constant propagation.
data Const = TopConst | IntConst Int | BottomConst
  deriving (Show, Eq)

constJoin :: Const -> Const -> Const
constJoin TopConst    _           = TopConst
constJoin _           TopConst    = TopConst
constJoin BottomConst c           = c
constJoin c           BottomConst = c
constJoin c1          c2
  | c1 == c2  = c1
  | otherwise = TopConst

constPropLat :: SemiLattice Const
constPropLat = SemiLattice
  { join   = constJoin
  , bottom = BottomConst
  }

applyOp' :: Binop -> Int -> Int -> Const
applyOp' Plus  x y = IntConst (x + y)
applyOp' Minus x y = IntConst (x - y)
applyOp' Mult  x y = IntConst (x * y)
applyOp' Div   x y = IntConst (x `div` y)
applyOp' Gt    _ _ = TopConst
applyOp' Eq    _ _ = TopConst

applyConstPropOp :: Binop -> Const -> Const -> Const
applyConstPropOp op (IntConst i1) (IntConst i2) = applyOp' op i1 i2

-- TODO: ??? Confused here ???
applyConstPropOp _  BottomConst   _             = BottomConst
applyConstPropOp _  _             BottomConst   = BottomConst

-- TODO: Can't we make this better by returning const for `T * 0`?
applyConstPropOp _  TopConst      _             = TopConst
applyConstPropOp _  _             TopConst      = TopConst

evalConstProp :: M.Map Id Const -> Exp -> Const
evalConstProp _ (Int i) = IntConst i
evalConstProp m (Var i) =
  fromJust (M.lookup i m)
  -- or alternatively
  -- fromMaybe TopConst (M.lookup i m)
evalConstProp _ FunCall{} = TopConst
evalConstProp m (Binop e1 op e2) = applyConstPropOp op (evalConstProp m e1) (evalConstProp m e2)
evalConstProp _ Input = TopConst
evalConstProp _ (AddrOf _) = TopConst
evalConstProp _ Malloc = TopConst
evalConstProp _ Deref{} = TopConst
evalConstProp _ Null = TopConst

constPropAnal :: Fun -> FlowAnalysis (M.Map Id Const)
constPropAnal fun = FlowAnalysis
  { lattice          = lat
  , flowGraph        = cfg
  , transferFunction = transfer_fun
  }
  where
    lat = varMapLattice (funVars fun) constPropLat
    cfg = funCFG fun
    cfg_transposed = transposeG (cfgGraph cfg)

    transfer_fun vtx ls =
      let
        preds = cfg_transposed ! vtx
        stmt = cfgNodeStmts cfg ! vtx
        pred_lats = map (ls !!) preds
        join_ = foldl' (join lat) (bottom lat) pred_lats
      in
        case stmt of
          var := rhs -> M.insert var (evalConstProp join_ rhs) join_
          Seq{}      -> error "Seq in CFG."
          _          -> join_

constPropEx :: Fun
constPropEx = Fun
  { funName = ""
  , funArgs = []
  , funLocals = ["x", "y", "z"]
  , funBody = stmts
      [ "x" := Int 27
      , "y" := Input
      , "z" := Binop (Int 2) Mult (Binop "x" Plus "y")
      , If (Binop (Int 0) Gt "x")
           ("y" := Binop "z" Minus (Int 3))
           ("y" := Int 12)
      , Output "y"
      ]
  , funRet = Null
  }

--------------------------------------------------------------------------------

showMapLatResult :: forall a . Show a => [M.Map Id a] -> String
showMapLatResult maps = concat . map unlines $
    [ sep
    , col (Just "Node") (Just "Var") (Just "Val") ]
    : zipWith showNodeMap_first [ 0 .. ] (map M.toList maps)
    ++ [[sep]]
  where
    sep = "+----------------------------+"

    col :: Maybe String -> Maybe String -> Maybe String -> String
    col (fromMaybe "" -> node) (fromMaybe "" -> var) (fromMaybe "" -> val) =
      "| " ++ span 6 node ++ " | " ++ span 6 var ++ " | " ++ span 8 val ++ " |"

    showNodeMap_first :: Int -> [(Id, a)] -> [String]
    showNodeMap_first node_idx [] =
      [col (Just (show node_idx)) Nothing Nothing]
    showNodeMap_first node_idx ((var, val) : rest) =
      col (Just (show node_idx)) (Just (show var)) (Just (show val))
        : showNodeMap rest

    showNodeMap :: [(Id, a)] -> [String]
    showNodeMap [] = []
    showNodeMap ((var, val) : rest) =
      col Nothing (Just (show var)) (Just (show val))
        : showNodeMap rest

span :: Int -> String -> String
span n s = s ++ replicate (n - length s) ' '

span_right :: Int -> String -> String
span_right n s = replicate (n - length s) ' ' ++ s

showCFG :: CFG -> String
showCFG (CFG graph stmts) = unlines (zipWith showBlock [ 0 .. ] (elems stmts))
  where
    showBlock :: Int -> Stmt -> String
    showBlock node stmt =
      let succs = graph ! node
       in span_right 2 (show node) ++ ": " ++ show stmt ++ " (succs: " ++ show succs ++ ")"

showSetLatResult :: Show a => [S.Set a] -> String
showSetLatResult =
    unlines . zipWith (\node_idx set -> span_right 2 (show node_idx) ++ ": " ++ showSet set) [ 0 :: Int .. ]
  where
    showSet s = "{" ++ intercalate "," (map show (S.toList s)) ++ "}"

main :: IO ()
main = do
    -- putStrLn (showCFG (funCFG bar))
    -- let !ret = solve (sign1FlowAnal bar)
    -- putStrLn (showMapLatResult ret)

    -- putStrLn (showCFG (funCFG livenessExample))
    -- let !ret = solve (livenessAnal (funVars livenessExample) livenessExample)
    -- putStrLn (showSetLatResult ret)

    -- putStrLn (showCFG (funCFG availExpr_test))
    -- let !ret = solve (availExprAnal availExpr_test)
    -- putStrLn (showSetLatResult ret)

    -- putStrLn (showCFG (funCFG veryBusyExpr_test))
    -- let !ret = solve (veryBusyExprAnal veryBusyExpr_test)
    -- putStrLn (showSetLatResult ret)

    putStrLn (showCFG (funCFG constPropEx))
    putStrLn (showMapLatResult (solve (constPropAnal constPropEx)))

    return ()
