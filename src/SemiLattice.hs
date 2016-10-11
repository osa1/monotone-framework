module SemiLattice where

--------------------------------------------------------------------------------

import Data.List (foldl')
import Data.Maybe (listToMaybe)

--------------------------------------------------------------------------------

-- | A semilattice is a partially ordered set with "join" operation.
data SemiLattice a = SemiLattice
  { join   :: !(a -> a -> a)
      -- ^ Join (or "least upper bound"). Must be idempotent, commutative, and
      -- associative.
  , bottom :: !a
      -- ^ Bottom is an unique element such that `forall a . join bottom a == a`.
  }

-- | Find top element of a semilattice.
findTop :: (Bounded a, Enum a) => SemiLattice a -> a
findTop lat = foldl' (join lat) (bottom lat) [ minBound .. maxBound ]

-- | Generate a decision procedure for partial order relation (`<=`) of the
-- given semilattice.
latLtRel :: Eq a => SemiLattice a -> (a -> a -> Maybe Bool)
latLtRel lat x y
  | x == y    = Just True
  | lub == x  = Just False
  | lub == y  = Just True
  | otherwise = Nothing
  where
    lub = join lat x y

-- | Test monotonicity of a given operation in O(n^3) time where n is number of
-- elements in the lattice. Returns the counterexample if found.
testOpMonotonicity :: (Bounded a, Enum a, Eq a)
                   => SemiLattice a -> (a -> a -> a) -> Maybe (a, a)
testOpMonotonicity lat op =
    listToMaybe [ (x1, x2)
                | x1 <- all_values
                , x2 <- all_values
                , x3 <- all_values
                , rel x1 x2 == Just True
                , op x1 x3 `rel` op x2 x3 /= Just True ]
  where
    all_values = [ minBound .. maxBound ]
    rel = latLtRel lat
