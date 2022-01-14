module Pact.Core.Builtin where

data RawBuiltin
  = RawAdd
  | RawSub
  | RawMultiply
  | RawDivide
  | RawMap
  | RawFilter
  | RawIf
  | RawIntToStr
  | RawConcat
  | RawStrToInt
  | RawTake
  | RawDrop
  | RawLength
  | RawDistinct
  deriving (Eq, Show, Ord, Enum)

-- monomorphised builtin operations
data ResolvedBuiltin
  = AddInt
  | SubInt
  deriving (Eq, Show, Ord, Enum)
