module Pact.Core.Builtin where

-- monomorphised builtin operations
data ResolvedBuiltin
  = AddInt
  | SubInt
  deriving (Eq, Show)
