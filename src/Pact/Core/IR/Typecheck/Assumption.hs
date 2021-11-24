module Pact.Core.IR.Typecheck.Assumption where

import Pact.Core.Type
import Data.Foldable(foldl')

-- Todo:
-- This is better as a Map n (Type tyname)
-- It would make for logn removals as opposed to asymptotically `n` removals,
-- at the cost of a slightly slower extend.
newtype Assumption n tn = Assumption { assumptions :: [(n, Type tn)] }
  deriving (Eq, Show)

empty :: Assumption n tn
empty = Assumption []

extend :: Assumption n tn -> (n, Type tn) -> Assumption n tn
extend (Assumption a) (x, s) = Assumption ((x, s) : a)

remove :: (Eq n) => Assumption n tn -> n -> Assumption n tn
remove (Assumption a) var = Assumption (filter (\(n, _) -> n /= var) a)

lookup :: (Eq n) => n -> Assumption n tn -> [Type tn]
lookup key (Assumption a) = map snd (filter (\(n, _) -> n == key) a)

merge :: Assumption n tn -> Assumption n tn -> Assumption n tn
merge (Assumption a) (Assumption b) = Assumption (a ++ b)

mergeAssumptions :: [Assumption n tn] -> Assumption n tn
mergeAssumptions = foldl' merge empty

singleton :: n -> Type tn -> Assumption n tn
singleton x y = Assumption [(x, y)]

keys :: Assumption n tn -> [n]
keys (Assumption a) = map fst a
