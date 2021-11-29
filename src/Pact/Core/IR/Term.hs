{-# LANGUAGE LambdaCase #-}

-- |
-- Module      :  Pact.Core.IR.Term
-- Copyright   :  (C) 2016 Stuart Popejoy
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Stuart Popejoy <stuart@kadena.io>, Jose Cardona <jose@kadena.io>
--
-- Our Core IR, which supports let-bound terms for type inference
--

module Pact.Core.IR.Term where

import Control.Lens
import Pact.Types.Hash (Hash)
import Pact.Types.Exp (Literal)
import Pact.Core.Type
import Pact.Core.Names
import Pact.Core.Builtin
import qualified Pact.Types.Names as PNames
import Data.Text(Text)

data DefType
  = DefCap
  | Defun
  | DefPact
  | DefConst
  deriving Show

data Def name tyname builtin info
  = Def
  { _defName :: name
  , _defTerm :: Term name builtin info
  , _defTermType :: Maybe (Type tyname)
  , _defType :: DefType
  } deriving Show

-- Todo:
-- Support module guard
data Module name tyname builtin info
  = Module
  { _modName :: name
  , _modDefs :: [Def name tyname builtin info]
  , _modHash :: Hash
  } deriving Show

type TermP = Term PNames.Name Text RawBuiltin
type DefP = Def PNames.Name Text RawBuiltin
type ModuleP = Module PNames.Name Text RawBuiltin
type CoreProgramP info = [ModuleP info]

data Term name builtin info
  = Var name info
  -- ^ single variables e.g x
  | Lam name (Term name builtin info) info
  -- ^ \x.e
  | Let name (Term name builtin info) (Term name builtin info) info
  -- ^ let x = e1 in e2
  | App (Term name builtin info) (Term name builtin info) info
  -- ^ (e1 e2)
  | Sequence (Term name builtin info) (Term name builtin info) info
  -- ^ (e1) (e2)
  | Error String info
  -- ^ error term , error "blah"
  | Builtin builtin info
  -- ^ Built-in ops, e.g (+)
  | DynAccess Text info
  -- ^ For some module m, m::f
  | Constant Literal info
  -- ^ Literals
  deriving (Show)

termInfo :: Lens' (Term name builtin info) info
termInfo f = \case
  Var n i -> Var n <$> f i
  Let n t1 t2 i ->
    Let n t1 t2 <$> f i
  Lam n term i -> Lam n term <$> f i
  App t1 t2 i -> App t1 t2 <$> f i
  Error s i -> Error s <$> f i
  Builtin b i -> Builtin b <$> f i
  Constant l i -> Constant l <$> f i
  Sequence l r i -> Sequence l r <$> f i
  DynAccess t i -> DynAccess t <$> f i

instance Plated (Term name builtin info) where
  plate f = \case
    Var n i -> pure (Var n i)
    Lam n term i -> Lam n <$> f term <*> pure i
    Let n t1 t2 i -> Let n <$> f t1 <*> f t2 <*> pure i
    App t1 t2 i -> App <$> f t1 <*> f t2 <*> pure i
    Error s i -> pure (Error s i)
    Builtin b i -> pure (Builtin b i)
    Constant l i -> pure (Constant l i)
    Sequence l r i -> Sequence <$> f l <*> f r <*> pure i
    DynAccess t i -> pure (DynAccess t i)
