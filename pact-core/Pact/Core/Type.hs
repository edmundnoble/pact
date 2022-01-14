{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards #-}


module Pact.Core.Type where

import Control.Lens
-- import Data.Maybe(fromMaybe)
import qualified Data.Map.Strict as Map
import Pact.Types.Exp (Literal(..))


data PrimType =
  TyInt |
  TyDecimal |
  TyTime |
  TyBool |
  TyString |
  TyUnit
  deriving (Eq,Ord,Show)

data Row n
  = RowTy (Map.Map n (Type n)) (Maybe n)
  | RowVar n
  | EmptyRow
  deriving (Eq, Show)

newtype InterfaceType n
  = InterfaceType n
  deriving (Eq, Show)

data ModuleType n
  = ModuleType n [n]
  deriving (Eq, Show)

-- Todo: caps are a bit strange here
-- same with defpacts. Not entirely sure how to type those yet.
-- | Our internal core type language
--   Tables, rows and and interfaces are quite similar,
--    t ::= B
--      |   v
--      |   t -> t
--      |   row
--      |   list<t>
--      |   interface name row
--
--    row  ::= {name:t, row*}
--    row* ::= name:t | ϵ
data Type n
  = TyVar n
  | TyPrim PrimType
  | TyFun (Type n) (Type n)
  | TyRow (Row n)
  -- ^ Row objects
  | TyList (Type n)
  -- ^ List aka [a]
  -- | TyTable (Maybe n) (Row n)
  -- -- ^ Tables, which may be inlined or optionally named
  -- -- | TyCap n (Type n) [TyRow n]
  -- -- ^ Capabilities (do we want the dependent caps as part of the type?)
  | TyInterface (InterfaceType n)
   -- ^ interfaces, which are nominal
  | TyModule (ModuleType n)
  -- ^ module type being the name of the module + implemented interfaces.
  | TyForall [n] [n] (Type n)
  -- ^ Universally quantified types, which have to be part of the type
  -- constructor since system F
  -- Todo: probably want `NonEmpty a` here since TyForall [] [] t = t
  deriving (Show, Eq)

traverseRowTy :: Traversal' (Row n) (Type n)
traverseRowTy f = \case
  RowTy tys rv -> RowTy <$> traverse f tys <*> pure rv
  RowVar n -> pure (RowVar n)
  EmptyRow -> pure EmptyRow


instance Plated (Type n) where
  plate f = \case
    TyVar n -> pure (TyVar n)
    TyPrim k -> pure (TyPrim k)
    TyFun l r -> TyFun <$> f l <*> f r
    TyRow rows -> TyRow <$> traverseRowTy f rows
    TyList t -> TyList <$> f t
    -- TyTable n rows ->
    --   TyTable n <$> traverseRowTy f rows
    TyInterface n ->
      pure $ TyInterface n
    TyModule n -> pure $ TyModule n
    TyForall ns rs ty ->
      TyForall ns rs <$> f ty


typeOfLit :: Literal -> Type n
typeOfLit = TyPrim . \case
  LString{} -> TyString
  LInteger{} -> TyInt
  LDecimal{} -> TyDecimal
  LBool{} -> TyBool
  LTime{} -> TyTime
