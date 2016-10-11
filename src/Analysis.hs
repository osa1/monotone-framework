{-# LANGUAGE ScopedTypeVariables #-}

module Analysis where

--------------------------------------------------------------------------------

import Data.Array ((!))
import Data.Graph
import Data.List (foldl')
import Data.Maybe (fromMaybe)

import CFG
import SemiLattice

--------------------------------------------------------------------------------

-- | A "monotone data flow analysis" is a semilattice, a flow graph, and a
-- mapping from flow graph nodes to transfer functions.
data FlowAnalysis a = FlowAnalysis
  { lattice       :: SemiLattice a
      -- ^ The lattice
  , flowGraph     :: CFG
      -- ^ The flow graph
  , constraintGen :: Vertex -> ([a] -> a)
      -- ^ Constraint generator generates a "dataflow constraint" that relates
      -- the value of the node to the values of other nodes (typically to
      -- successor or predecessor nodes).
  , widen         :: Maybe ([a] -> [a])
      -- ^ Optional widening step. Requirements for a sound widening function:
      --
      --     - It should be "extensive":
      --       `forall l . l <= widen l`.
      --
      --     - It should be "monotonic":
      --       `forall l1 l2 . l1 <= l2 -> widen l1 <= widen l2
      --
      --     - It should operate on a subset of the original lattice that has
      --       finite height ("bounded lattice"), so that the fixpoint algorithm
      --       can work again.
  }

-- | Helper for buildling forward analyses.
mkFwdAnal :: SemiLattice a -> CFG
          -> (a -> Vertex -> a)
             -- ^ a: LUB of predecessors, Vertex: Current node
          -> FlowAnalysis a
mkFwdAnal lat cfg trans = FlowAnalysis
  { lattice       = lat
  , flowGraph     = cfg
  , constraintGen = constr_gen
  , widen         = Nothing
  }
  where
    -- need to transpose the graph to get predecessors
    cfg_transposed = transposeG (cfgGraph cfg)
    constr_gen vtx ls =
      let
        preds     = cfg_transposed ! vtx
        pred_lats = map (ls !!) preds
        join_     = foldl' (join lat) (bottom lat) pred_lats
      in
        trans join_ vtx

-- | Helper for buildling backward analyses.
mkBkwAnal :: SemiLattice a -> CFG
          -> (a -> Vertex -> a)
             -- ^ a: LUB of successors, Vertex: Current node
          -> FlowAnalysis a
mkBkwAnal lat cfg trans = FlowAnalysis
  { lattice       = lat
  , flowGraph     = cfg
  , constraintGen = constr_gen
  , widen         = Nothing
  }
  where
    constr_gen vtx ls =
      let
        succs     = cfgGraph cfg ! vtx
        succ_lats = map (ls !!) succs
        join_     = foldl' (join lat) (bottom lat) succ_lats
      in
        trans join_ vtx

-- | A simple solver. Finds minimal solution if lattice is bounded, but does it
-- inefficiently.
solve :: forall a . Eq a => FlowAnalysis a -> [a]
solve flowAnal =
    -- start with the bottom, apply transfer functions repeatedly until a
    -- fixpoint
    run l0
  where
    l0  = replicate (length vtx) (bottom (lattice flowAnal))

    vtx = vertices (cfgGraph (flowGraph flowAnal))
    constrs = map (constraintGen flowAnal) vtx

    -- This is what's called "combined function F : L^n -> L^n" in Chapter 5.
    f :: [a] -> [a]
    f as = fromMaybe id (widen flowAnal) (map ($ as) constrs)

    run l =
      let next = f l
       in if next == l then l else run next
