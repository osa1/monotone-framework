{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns        #-}

module Utils
  ( showMapLatResult
  , showSetLatResult
  , span, span_right
  ) where

--------------------------------------------------------------------------------

import Data.List (intercalate)
import qualified Data.Map as M
import Data.Maybe (fromMaybe)
import qualified Data.Set as S

import Prelude hiding (span)

--------------------------------------------------------------------------------

showMapLatResult :: forall k v . (Show k, Show v) => [M.Map k v] -> String
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

    showNodeMap_first :: Int -> [(k, v)] -> [String]
    showNodeMap_first node_idx [] =
      [col (Just (show node_idx)) Nothing Nothing]
    showNodeMap_first node_idx ((var, val) : rest) =
      col (Just (show node_idx)) (Just (show var)) (Just (show val))
        : showNodeMap rest

    showNodeMap :: [(k, v)] -> [String]
    showNodeMap [] = []
    showNodeMap ((var, val) : rest) =
      col Nothing (Just (show var)) (Just (show val))
        : showNodeMap rest

span :: Int -> String -> String
span n s = s ++ replicate (n - length s) ' '

span_right :: Int -> String -> String
span_right n s = replicate (n - length s) ' ' ++ s

showSetLatResult :: Show a => [S.Set a] -> String
showSetLatResult =
    unlines . zipWith (\node_idx set -> span_right 2 (show node_idx) ++ ": " ++ showSet set) [ 0 :: Int .. ]
  where
    showSet s = "{" ++ intercalate "," (map show (S.toList s)) ++ "}"
