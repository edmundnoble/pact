module Pact.Core.Names where

import Data.Text(Text)
import Data.IORef (IORef, atomicModifyIORef')
import Pact.Types.Lang (TypeName(TypeName))

newtype Unique = Unique Int deriving (Show, Eq, Ord)

newtype Supply = Supply (IORef Int)


newtype ByUnique a = ByUnique a deriving (Eq, Show)

class HasUnique a where
  getUnique :: a -> Unique

instance (HasUnique a) => Eq (ByUnique a) where
  l == r = getUnique l == getUnique

instance (HasUnique a) => Ord (ByUnique a) where
  l <= r = getUnique l <= getUnique r

newUnique :: Supply -> IO Unique
newUnique (Supply ref) =
  atomicModifyIORef' ref $ \x ->
    let z = x+1 in (z,Unique z)

data NameKind
  = TopLevelName -- Script top level names, not bound to any module
  | ModuleBoundName !Text
  | LocallyBoundName
  deriving (Show, Eq)

data Name
  = Name
  { _nameRaw :: !Text
  , _nameUnique :: !Unique
  , _nameKind :: NameKind }
  deriving (Show, Eq)

data TypeVar
  = TypeVar
  { _tyVarName :: !Text
  , _tyVarUnique :: !Unique }
  | UnificationVar
  { _tyVarName :: !Text
  , _tyVarUnique :: !Unique }
  deriving (Show, Eq)

data TypeName
  = TypeName
  { _tyname :: !Text
  , _tynameUnique :: !Unique }
  deriving (Show, Eq)

instance HasUnique Name where
  getUnique = _nameUnique

instance HasUnique TypeVar where
  getUnique = \case
    TypeVar _ u -> u
    UnificationVar _ u -> u

instance HasUnique TypeName where
  getUnique = _tynameUnique
