{-# LANGUAGE LambdaCase #-}

module Main where

--------------------------------------------------------------------------------

import Data.Maybe (listToMaybe)
import System.Environment (getArgs)
import System.Exit (exitFailure)

import CFG (cfgToDot, funCFG)
import TIP.Examples (allExamples)
import TIP.Syntax (Fun, Id (..), funName)

import Text.Dot (showDot)

--------------------------------------------------------------------------------

main :: IO ()
main =
  getArgs >>= \case
    [fname] -> generateDot fname
    _ -> putStrLn "USAGE: fun-to-dot <function name>" >> exitFailure

findFun :: String -> Maybe Fun
findFun fname = listToMaybe (filter ((==) (Id fname) . funName) allExamples)

generateDot :: String -> IO ()
generateDot fname =
    case findFun fname of
      Nothing  -> putStrLn ("Can't find function " ++ fname) >> exitFailure
      Just fun -> putStrLn (showDot (cfgToDot (funCFG fun)))
