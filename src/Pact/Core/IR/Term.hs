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
import Pact.Types.Exp (Literal)

data Term name builtin info
  = Var name info
  | Lam name (Term name builtin info) info
  | Let name (Term name builtin info) (Term name builtin info) info
  | App (Term name builtin info) (Term name builtin info) info
  | Sequence (Term name builtin info) (Term name builtin info) info
  | Error String info
  | Builtin builtin info
  | Constant Literal info
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
