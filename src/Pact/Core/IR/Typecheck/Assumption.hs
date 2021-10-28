module Pact.Core.IR.Typecheck.Assumption where

import Pact.Core.Type
import Data.Foldable(foldl')

newtype Assumption n = Assumption { assumptions :: [(n, Type n)] }
  deriving (Eq, Show)

empty :: Assumption n
empty = Assumption []

extend :: Assumption n -> (n, Type n) -> Assumption n
extend (Assumption a) (x, s) = Assumption ((x, s) : a)

remove :: (Eq n) => Assumption n -> n -> Assumption n
remove (Assumption a) var = Assumption (filter (\(n, _) -> n /= var) a)

lookup :: (Eq n) => n -> Assumption n -> [Type n]
lookup key (Assumption a) = map snd (filter (\(n, _) -> n == key) a)

merge :: Assumption n -> Assumption n -> Assumption n
merge (Assumption a) (Assumption b) = Assumption (a ++ b)

mergeAssumptions :: [Assumption n] -> Assumption n
mergeAssumptions = foldl' merge empty

singleton :: n -> Type n -> Assumption n
singleton x y = Assumption [(x, y)]

keys :: Assumption n -> [n]
keys (Assumption a) = map fst a
