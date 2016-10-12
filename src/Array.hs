-- | Because 'array' sucks.
module Array
  ( Array
  , fromList
  , toList
  , (!)
  , Array.length
  , assocs
  , fromAssocs
  ) where

import qualified Data.Array as A

type Array a = A.Array Int a

fromList :: [a] -> Array a
-- two pass but whatever. it's 'array' to blame.
fromList lst = A.listArray (0, Prelude.length lst - 1) lst

toList :: Array a -> [a]
toList = A.elems

infixl 9 !
(!) :: Array e -> Int -> e
(!) = (A.!)

length :: Array a -> Int
length = snd . A.bounds

assocs :: Array a -> [(Int, a)]
assocs = A.assocs

fromAssocs :: [(Int, a)] -> Array a
fromAssocs lst = A.array (0, Prelude.length lst - 1) lst
