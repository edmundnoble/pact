{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell #-}


-- |
-- Module      :  Pact.Core.IR.Typecheck
-- Copyright   :  (C) 2016 Stuart Popejoy
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Stuart Popejoy <stuart@kadena.io>
--
-- Typechecker using heeren's algorithm
--
module Pact.Core.IR.Typecheck where

import Control.Lens
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import Data.List(find, delete)
import Data.Maybe (fromJust)
import Control.Monad.Except
import Control.Monad.Reader
-- import Control.Monad.State.Strict
import Pact.Core.Type
import Pact.Core.Names
import Pact.Core.IR.Typecheck.Assumption (Assumption(..))
import qualified Pact.Core.IR.Typecheck.Assumption as AS
import Data.Text(Text)

data RowConstraint n =
  LacksField Text (RowVar n)
  deriving (Eq, Show)

data Rho n
  = Rho (RowConstraint n)
  | RhoType (Type n)
  deriving (Eq, Show)

data TyScheme n = TyScheme [n] (Type n)
  deriving (Eq, Show)


data TCEnv n builtin
  = TCEnv
  { _tcSupply :: Supply -- ^ Fresh name supply
  , _tcEnv :: Map.Map n (TyScheme n) -- ^ Typescheme environment
  , _tcNonGen :: Set.Set n -- ^ Monomorphic set to not generalize
  , _tcLiftName :: Unique -> n
  , _tcBuiltin :: Map.Map builtin (TyScheme n)
  }

makeLenses ''TCEnv

freshVar :: (MonadIO m, MonadReader (TCEnv n builtin) m) => m n
freshVar = do
  f <- view tcLiftName
  s <- view tcSupply
  f <$> liftIO (newUnique s)


data Constraint n
  = EqConst (Type n) (Type n)
  | ExpInstConst (Type n) (TyScheme n)
  | ImpInstConst (Type n) (Set.Set n) (Type n)
  deriving (Show, Eq)

type Subst n = Map.Map n (Type n)

class Substitutable p n | p -> n where
  subst :: Subst n -> p -> p

instance Ord n => Substitutable (Type n) n where
  subst = substInTy

instance Ord n => Substitutable (TyScheme n) n where
  subst m (TyScheme ns ty) =
    let m' = Map.union m $ Map.fromList [(n', TyVar n') | n' <- ns]
    in TyScheme ns (subst m' ty)

instance Ord n => Substitutable (Constraint n) n where
   subst s (EqConst t1 t2) = EqConst (subst s t1) (subst s t2)
   subst s (ExpInstConst t sc) = ExpInstConst (subst s t) (subst s sc)
   subst s (ImpInstConst t1 ms t2) = ImpInstConst (subst s t1) (Set.map setSubst ms) (subst s t2)
    where
    setSubst n = case s ^. at n of
      Just (TyVar n') -> n'
      _ -> n

class FTV p n | p -> n where
  ftv :: p -> Set.Set n

instance Ord n => FTV (Map.Map n (Type n)) n where
  ftv = foldMap ftv

instance Ord n => FTV (Type n) n where
  ftv = \case
    TyVar n -> Set.singleton n
    TyPrim _ -> mempty
    TyFun l r -> Set.union (ftv l) (ftv r)
    TyRow rows -> ftv rows
    TyList t -> ftv t
    -- TyTable _ rows -> ftv rows
    -- TyInterface _ rows -> ftv rows
    TyForall ns typ -> ftv typ `Set.difference` Set.fromList ns

instance Ord n => FTV (Row n) n where
  ftv = \case
    RowTy m n -> ftv m `Set.union` maybe mempty (Set.singleton . _rowVar) n
    RowTyVar (RowVar n) -> Set.singleton n

instance Ord n => FTV (TyScheme n) n where
  ftv (TyScheme ns typ) =
    ftv typ `Set.difference` Set.fromList ns

class ActiveTypeVars p n | p -> n where
  atv :: p -> Set.Set n

instance Ord n => ActiveTypeVars (Constraint n) n where
  atv (EqConst t1 t2) = ftv t1 `Set.union` ftv t2
  atv (ImpInstConst t1 ms t2) = ftv t1 `Set.union` (ms `Set.intersection` ftv t2)
  atv (ExpInstConst t s) = ftv t `Set.union` ftv s

compose :: Ord n => Subst n -> Subst n -> Subst n
compose m1 m2 = (subst m1 <$> m2) `Map.union` m1

-- Occurs checking
bind :: (Ord k, MonadError [Char] f) => k -> Type k -> f (Map.Map k (Type k))
bind n t | t == TyVar n = pure mempty
         | occursCheck n t = throwError ""
         | otherwise = pure (Map.singleton n t)

occursCheck :: (Ord n, FTV f n) => n -> f -> Bool
occursCheck n t = Set.member n (ftv t)

unifyRows :: (Ord n, MonadError [Char] f) => Row n -> Row n -> f (Map.Map n (Type n))
unifyRows (RowTyVar n) t =  _rowVar n `bind` (TyRow t)
unifyRows t (RowTyVar n)  =  _rowVar n `bind` (TyRow t)
unifyRows _ _ = undefined

-- note: For IR we currently don't unify against
-- `TyForall`, we don't allow rankN despite it showing up in
-- our type language.
unifies :: (Ord n, MonadError String f) => Type n -> Type n -> f (Subst n)
unifies t1 t2 | t1 == t2 = pure mempty
unifies (TyVar n) t2 = n `bind` t2
unifies t1 (TyVar n) = n `bind` t1
unifies (TyFun l r) (TyFun l' r') = do
  s1 <- unifies l l'
  s2 <- unifies (subst s1 r) (subst s1 r')
  pure (s2 `compose` s1)
unifies (TyRow l) (TyRow r) = unifyRows l r
unifies _ _ = error "reee"

generalize :: Ord n => Set.Set n -> Type n -> TyScheme n
generalize free t  = TyScheme as t
  where
  as = Set.toList $ ftv t `Set.difference` free

instantiate :: (MonadIO m, MonadReader (TCEnv n builtin) m, Ord n) => TyScheme n -> m (Type n)
instantiate (TyScheme as t) = do
    as' <- traverse (const freshVar) as
    let s = Map.fromList $ zip as (TyVar <$> as')
    return $ subst s t

nextSolvable :: Ord a => [Constraint a] -> (Constraint a, [Constraint a])
nextSolvable xs = fromJust (find solvable (chooseOne xs))
  where
    chooseOne xss = [(x, ys) | x <- xss, let ys = delete x xss]
    solvable (EqConst{}, _) = True
    solvable (ExpInstConst{}, _) = True
    solvable (ImpInstConst _ ms t2, cs) = Set.null ((ftv t2 `Set.difference` ms) `Set.intersection` foldMap atv cs)

solve :: (Ord a, MonadError String m, MonadIO m, MonadReader (TCEnv a builtin) m) => [Constraint a] -> m (Subst a)
solve [] = return mempty
solve cs = solve' (nextSolvable cs)

solve' :: (Ord a, MonadError String m, MonadIO m, MonadReader (TCEnv a builtin) m) => (Constraint a, [Constraint a]) -> m (Subst a)
solve' (EqConst t1 t2, cs) = do
  su1 <- unifies t1 t2
  su2 <- solve (fmap (subst su1) cs)
  return (su2 `compose` su1)
solve' (ImpInstConst t1 ms t2, cs) =
  solve (ExpInstConst t1 (generalize ms t2) : cs)
solve' (ExpInstConst t s, cs) = do
  s' <- instantiate s
  solve (EqConst t s' : cs)
