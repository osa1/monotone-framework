module SemiLattice where

--------------------------------------------------------------------------------

import Data.List (foldl')
import Data.Maybe (listToMaybe)

--------------------------------------------------------------------------------

-- | A semilattice is a partially ordered set with "join" operation.
--
-- A semilattice can be defined in two ways:
--
-- 1. By providing a set and a join operation that is idempotent, commutative,
--    and associative.
--
-- 2. By providing a set and a decision procedure for the partial ordering. The
--    the relation must be reflexive, anti-symmetric, and transitive.
--
-- In this definition we use (1) because 1) we've never encountered a case where
-- we need a decision procedure for the ordering relation 2) given an efficient
-- "join" function it's possible to recover an efficient decision procedure for
-- the relation, see `latLtRel`.
--
-- === Why is this a record instead of a typeclass?
-- For same @a@ multiple SemiLattices can be defined. A trivial example is, for
-- a "complete lattice" @C a@ (we don't define a type for this here) for an @a@,
-- two semilattices can be defined.
--
-- - One that uses @C a@'s bottom as bottom and join as join.
-- - One that uses @C a@'s top as bottom and meet as join.
--
data SemiLattice a = SemiLattice
  { join   :: !(a -> a -> a)
      -- ^ Join (or "least upper bound"). Must be idempotent, commutative, and
      -- associative.
  , bottom :: !a
      -- ^ Bottom is an unique element such that @forall a . join bottom a == a@.
  }

-- | Find top element of a semilattice.
findTop :: (Bounded a, Enum a) => SemiLattice a -> a
findTop lat = foldl' (join lat) (bottom lat) [ minBound .. maxBound ]
              -- alternatively we could use foldl1' becuase the set can't be empty

-- | Generate a decision procedure for partial order relation (@<=@) of the
-- given semilattice.
--
-- The relation is reflexive, transitive, and anti-symmetric.
latLtRel :: Eq a => SemiLattice a -> (a -> a -> Bool)
latLtRel lat x y = join lat x y == y

-- | Test monotonicity of a given operation in O(n^3) time where n is number of
-- elements in the lattice. Returns the counterexample if found.
testOpMonotonicity :: (Bounded a, Enum a, Eq a)
                   => SemiLattice a -> (a -> a -> a) -> Maybe (a, a)
testOpMonotonicity lat op =
    listToMaybe [ (x1, x2)
                | x1 <- all_values
                , x2 <- all_values
                , x3 <- all_values
                , x1 `rel` x2
                , not (op x1 x3 `rel` op x2 x3) ]
  where
    all_values = [ minBound .. maxBound ]
    rel = latLtRel lat
