{-# LANGUAGE OverloadedStrings #-}

-- | Some example TIP programs.
module TIP.Examples where

--------------------------------------------------------------------------------

import Analysis
import CFG
import TIP.Syntax

--------------------------------------------------------------------------------

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
  , funRet    = "f"
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
  , funLocals = ["n", "ret"]
  , funBody   = stmts $
      [ "n" := Input
      , "ret" := FunCall "foo" [AddrOf "n", "foo"]
      ]
  , funRet    = "ret"
  }

livenessExample :: Fun
livenessExample = Fun
  { funName = "le"
  , funArgs = []
  , funLocals = ["x", "y", "z", "ret"]
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
      , "ret" := Null
      ]
  , funRet = "ret"
  }

availExprExample :: Fun
availExprExample = Fun
  { funName = "ae_test"
  , funArgs = []
  , funLocals = ["x", "y", "z", "a", "b", "ret"]
  , funBody = stmts
      [ "z" := Binop "a" Plus "b"
      , "y" := Binop "a" Mult "b"
      , While (Binop "y" Gt (Binop "a" Plus "b")) $ stmts
          [ "a" := Binop "a" Plus (Int 1)
          , "x" := Binop "a" Plus "b"
          ]
      , "ret" := Null
      ]
  , funRet = "ret"
  }

veryBusyExprExample :: Fun
veryBusyExprExample = Fun
  { funName = ""
  , funArgs = []
  , funLocals = ["x", "a", "b", "ret"]
  , funBody = stmts
      [ "x" := Input
      , "a" := Binop "x" Minus (Int 1)
      , "b" := Binop "x" Minus (Int 2)
      , While (Binop "x" Gt (Int 0)) $ stmts
          [ Output (Binop (Binop "a" Mult "b") Minus "x")
          , "x" := Binop "x" Minus (Int 1)
          ]
      , Output (Binop "a" Mult "b")
      , "ret" := Null
      ]
  , funRet = "ret"
  }

constPropExample :: Fun
constPropExample = Fun
  { funName = ""
  , funArgs = []
  , funLocals = ["x", "y", "z", "ret"]
  , funBody = stmts
      [ "x" := Int 27
      , "y" := Input
      , "z" := Binop (Int 2) Mult (Binop "x" Plus "y")
      , If (Binop (Int 0) Gt "x")
           ("y" := Binop "z" Minus (Int 3))
           ("y" := Int 12)
      , Output "y"
      , "ret" := Null
      ]
  , funRet = "ret"
  }

intAnalExample :: Fun
intAnalExample = Fun
  { funName = ""
  , funArgs = []
  , funLocals = ["x", "y", "ret"]
  , funBody = stmts
      [ "y" := Int 0 -- 1
      , "x" := Int 7 -- 2
      , "x" := Binop "x" Plus (Int 1) -- 3
      , While Input $ stmts -- 4
          [ "x" := (Int 7) -- 5
          , "x" := Binop "x" Plus (Int 1) -- 6
          , "y" := Binop "y" Plus (Int 1) -- 7
          ]
      , "ret" := Null
      ]
  , funRet = "ret"
  }

pathSensitivityExample :: Fun
pathSensitivityExample = Fun
  { funName = ""
  , funArgs = []
  , funLocals = ["x", "y", "z", "ret"]
  , funBody = stmts
      [ "x" := Input -- 1
      , "y" := Int 0 -- 2
      , "z" := Int 0 -- 3
      , While (Binop "x" Gt (Int 0)) $ stmts -- 4
          [ "z" := Binop "z" Plus "x" -- 5
          , If (Binop (Int 17) Gt "y") -- 6
               ("y" := Binop "y" Plus (Int 1)) -- 7
               Skip -- 8
          , "x" := Binop "x" Minus (Int 1) -- 9
          ]
      , "ret" := Null
      ]
  , funRet = "ret"
  }

--------------------------------------------------------------------------------

allExamples :: [Fun]
allExamples =
  [ ite, rec, bar
  , livenessExample
  , veryBusyExprExample
  , constPropExample
  , intAnalExample
  ]

--------------------------------------------------------------------------------

runExample :: Eq ret => Fun -> (Fun -> FlowAnalysis ret) -> ([ret] -> String) -> IO ()
runExample fun anal toStr = do
    putStrLn (show (funCFG fun))
    putStrLn (toStr (solve (anal fun)))
