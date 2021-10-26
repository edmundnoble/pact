{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TupleSections #-}

module Pact.Core.Type where

import Control.Lens
import Data.Maybe(fromMaybe)
import qualified Data.Map.Strict as Map

data PrimType =
  TyInt |
  TyDecimal |
  TyTime |
  TyBool |
  TyString |
  TyUnit
  deriving (Eq,Ord,Show)

data TyRow n =
  Row (n, Type n) | EmptyRow
  deriving (Eq,Ord,Show)


data TypeScheme n
  = TypeScheme [n] (Type n)
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
  | TyRow [TyRow n]
  -- ^ Row objects
  | TyList (Type n)
  -- ^ List aka [a]
  | TyTable (Maybe n) [TyRow n]
  -- ^ Tables, which may be inlined or optionally named
  -- | TyCap n (Type n) [TyRow n]
  -- ^ Capabilities (do we want the dependent caps as part of the type?)
  | TyInterface n [TyRow n]
  -- ^ interfaces as named rows, where defuns/consts correspond to fields
  | TyForall [n] (Type n)
  -- ^ Universally quantified types, which have to be part of the type
  -- constructor since system F
  -- Todo: probably want `NonEmpty a` here
  deriving (Ord, Show)

traverseRowTy :: Traversal' (TyRow n) (Type n)
traverseRowTy f = \case
  Row (n, ty) -> Row . (n,) <$> f ty
  EmptyRow -> pure EmptyRow


instance Plated (Type n) where
  plate f = \case
    TyVar n -> pure (TyVar n)
    TyPrim k -> pure (TyPrim k)
    TyFun l r -> TyFun <$> f l <*> f r
    TyRow rows -> TyRow <$> traverse (traverseRowTy f) rows
    TyList t -> TyList <$> f t
    TyTable n rows ->
      TyTable n <$> traverse (traverseRowTy f) rows
    TyInterface n rows ->
      TyInterface n <$> traverse (traverseRowTy f) rows
    TyForall ns ty ->
      TyForall ns <$> f ty



substInTy :: Ord n => Map.Map n (Type n) -> Type n -> Type n
substInTy m = transform (subst m)
  where
  subst m' = \case
    TyVar n -> fromMaybe (TyVar n) $ m' ^. at n
    TyForall ns ty ->
      let m'' = Map.union m' $ Map.fromList [(n', TyVar n') | n' <- ns]
      in TyForall ns (substInTy m'' ty)
    x -> x

instance (Ord n) => Eq (Type n) where
  (TyVar n) == (TyVar n') = n == n'
  (TyPrim p) == (TyPrim p') = p == p'
  (TyFun l r) == (TyFun l' r') =
    l == l' && r == r'
  (TyRow row') == (TyRow row) =
    and $ zipWith (==) row row'
  (TyList n) == (TyList n') = n == n'
  (TyTable _ row) == (TyTable _ row') =
    and $ zipWith (==) row row'
  (TyInterface n row) == (TyInterface n' row') =
    n == n' && row == row'
  (TyForall ns ty) == (TyForall ns' ty') =
    let n = Map.fromList $ zipWith (\a b -> (b, TyVar a)) ns ns'
    in ty == substInTy n ty'
  _ == _ = False
