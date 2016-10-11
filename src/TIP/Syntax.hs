module TIP.Syntax where

--------------------------------------------------------------------------------

import Data.List (foldl')
import qualified Data.Set as S
import Data.String (IsString (..))

--------------------------------------------------------------------------------
-- * AST definition

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

-- Helps when buildling AST by hand (so, like, all the time).
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

--------------------------------------------------------------------------------
-- * Utilities

stmts :: [Stmt] -> Stmt
stmts []       = Skip
stmts (s : ss) = foldl' Seq s ss

funVars :: Fun -> S.Set Id
funVars fun = S.fromList (funArgs fun) `S.union` S.fromList (funLocals fun)

expVars :: Exp -> S.Set Id
expVars Int{}           = S.empty
expVars (Var var)       = S.singleton var
expVars (FunCall e1 es) = S.unions (map expVars (e1 : es))
expVars (Binop e1 _ e2) = expVars e1 `S.union` expVars e2
expVars Input{}         = S.empty
expVars (AddrOf var)    = S.singleton var
expVars Malloc          = S.empty
expVars (Deref e)       = expVars e
expVars Null            = S.empty

-- | Set of all expressions in a statement.
stmtExps :: Stmt -> S.Set Exp
stmtExps Skip         = S.empty
stmtExps (_ := e)     = subExps e
stmtExps (_ :*= e)    = subExps e
stmtExps (Output e)   = subExps e
stmtExps (Seq s1 s2)  = stmtExps s1 `S.union` stmtExps s2
stmtExps (If e s1 s2) = subExps e `S.union` stmtExps s1 `S.union` stmtExps s2
stmtExps (While e s)  = subExps e `S.union` stmtExps s

-- | Set of all expressions in a program.
funExps :: Fun -> S.Set Exp
funExps = stmtExps . funBody

-- | Set of all subexpressions of an expression.
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
