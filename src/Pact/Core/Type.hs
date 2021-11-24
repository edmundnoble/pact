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
  -- | TyInterface n (Row n)
  -- ^ interfaces as named rows, where defuns/consts correspond to fields
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
    -- TyInterface n rows ->
      -- TyInterface n <$> traverseRowTy f rows
    TyForall ns rs ty ->
      TyForall ns rs <$> f ty

-- note: Row variables cannot be "Substituted" for non-rows.
-- substInTy :: Ord n => Map.Map n (Type n) -> Type n -> Type n
-- substInTy m = \case
--     TyVar n -> fromMaybe (TyVar n) $ m ^. at n
--     TyPrim p -> TyPrim p
--     TyList tys -> TyList (substInTy m tys)
--     TyRow r -> substRow r
--     TyForall ns rs ty ->
--       let m' = Map.fromList [(n', TyVar n') | n' <- ns] `Map.union` m
--       in TyForall ns (substInTy m' ty)
--     x -> x
--   where
--   substRow = \case
--     RowTyVar r -> fromMaybe (TyRow (RowTyVar r)) $ m ^. at (_rowVar r)
--     RowTy fields mv ->
--       case mv of
--         Nothing -> TyRow $ RowTy (substInTy m <$> fields) Nothing
--         Just rv -> case m ^. at (_rowVar rv) of
--           Just (TyRow (RowTyVar rv')) -> TyRow $ RowTy (substInTy m <$> fields) (Just rv')
--           Just (TyRow (RowTy fields' rv')) -> TyRow $ RowTy (Map.union fields fields') rv'
--           Just _ -> error "fatal: row variable unified with non-row"
--           _ -> TyRow $ RowTy (substInTy m <$> fields) mv


typeOfLit :: Literal -> Type n
typeOfLit = TyPrim . \case
  LString{} -> TyString
  LInteger{} -> TyInt
  LDecimal{} -> TyDecimal
  LBool{} -> TyBool
  LTime{} -> TyTime

-- instance (Ord n) => Eq (Type n) where
--   (TyVar n) == (TyVar n') = n == n'
--   (TyPrim p) == (TyPrim p') = p == p'
--   (TyFun l r) == (TyFun l' r') =
--     l == l' && r == r'
--   (TyRow row') == (TyRow row) =
--     row == row'
--   (TyList n) == (TyList n') = n == n'
  -- (TyTable _ row) == (TyTable _ row') =
  --   row == row'
  -- (TyInterface n row) == (TyInterface n' row') =
  --   n == n' && row == row'
  -- (TyForall ns rs ty) == (TyForall ns' rs' ty') =
  --   ns == rs ==
  -- _ == _ = False
