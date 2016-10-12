{-# LANGUAGE ScopedTypeVariables #-}

module Analysis where

--------------------------------------------------------------------------------

import qualified Data.Graph.Inductive as G
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
  , constraintGen :: G.Node -> ([a] -> a)
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
          -> (a -> G.Node -> a)
             -- ^ a: LUB of predecessors, Vertex: Current node
          -> FlowAnalysis a
mkFwdAnal lat cfg trans = FlowAnalysis
  { lattice       = lat
  , flowGraph     = cfg
  , constraintGen = constr_gen
  , widen         = Nothing
  }
  where
    constr_gen node ls =
      let
        preds     = G.pre' (G.context cfg node)
        pred_lats = map (ls !!) preds
        join_     = foldl' (join lat) (bottom lat) pred_lats
      in
        trans join_ node

-- | Helper for buildling backward analyses.
mkBkwAnal :: SemiLattice a -> CFG
          -> (a -> G.Node -> a)
             -- ^ a: LUB of successors, Vertex: Current node
          -> FlowAnalysis a
mkBkwAnal lat cfg trans = FlowAnalysis
  { lattice       = lat
  , flowGraph     = cfg
  , constraintGen = constr_gen
  , widen         = Nothing
  }
  where
    constr_gen node ls =
      let
        succs     = G.suc' (G.context cfg node)
        succ_lats = map (ls !!) succs
        join_     = foldl' (join lat) (bottom lat) succ_lats
      in
        trans join_ node

-- | A simple solver. Finds minimal solution if lattice is bounded, but does it
-- inefficiently.
solve :: forall a . Eq a => FlowAnalysis a -> [a]
solve flowAnal =
    -- start with the bottom, apply transfer functions repeatedly until a
    -- fixpoint
    run l0
  where
    l0  = replicate (length nodes) (bottom (lattice flowAnal))

    nodes = map fst (G.labNodes (flowGraph flowAnal))
    constrs = map (constraintGen flowAnal) nodes

    -- This is what's called "combined function F : L^n -> L^n" in Chapter 5.
    f :: [a] -> [a]
    f as = fromMaybe id (widen flowAnal) (map ($ as) constrs)

    run l =
      let next = f l
       in if next == l then l else run next
