{-# LANGUAGE OverloadedStrings #-}

-- | Some example TIP programs.
module TIP.Examples where

--------------------------------------------------------------------------------

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

availExprExample :: Fun
availExprExample = Fun
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

veryBusyExprExample :: Fun
veryBusyExprExample = Fun
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

constPropExample :: Fun
constPropExample = Fun
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

intAnalExample :: Fun
intAnalExample = Fun
  { funName = ""
  , funArgs = []
  , funLocals = ["x", "y"]
  , funBody = stmts
      [ "y" := Int 0
      , "x" := Int 7
      , "x" := Binop "x" Plus (Int 1)
      , While Input $ stmts
          [ "x" := (Int 7)
          , "x" := Binop "x" Plus (Int 1)
          , "y" := Binop "y" Plus (Int 1)
          ]
      ]
  , funRet = Null
  }
