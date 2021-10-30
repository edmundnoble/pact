{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}

module Pact.Core.IR.Typecheck where

import Control.Lens
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import Control.Monad.Except
import Pact.Core.Type

data TyScheme n = TyScheme [n] (Type n)
  deriving (Eq, Show)

data Constraint n
  = EqConst (Type n) (Type n)
  | ExpInstConst (Type n) (TyScheme n)
  | ImpInstConst (Type n) (Set.Set n) (Type n)
  deriving (Show, Eq)

type Subst n = Map.Map n (Type n)

class Substitutable f where
  subst :: Ord n => Subst n -> f n -> f n

instance Substitutable Type where
  subst = substInTy

instance Substitutable TyScheme where
  subst m (TyScheme ns ty) =
    let m' = Map.union m $ Map.fromList [(n', TyVar n') | n' <- ns]
    in TyScheme ns (subst m' ty)

instance Substitutable Constraint where
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
    TyTable _ rows -> ftv rows
    TyInterface _ rows -> ftv rows
    TyForall ns typ -> ftv typ `Set.difference` (Set.fromList ns)

instance Ord n => FTV (TyRow n) n where
  ftv = \case
    ClosedRow tv -> ftv tv
    OpenRow tv -> ftv tv

instance Ord n => FTV (TyScheme n) n where
  ftv (TyScheme ns typ) =
    ftv typ `Set.difference` (Set.fromList ns)

class ActiveTypeVars f where
  atv :: Ord n => f n -> Set.Set n

instance ActiveTypeVars Constraint where
  atv (EqConst t1 t2) = ftv t1 `Set.union` ftv t2
  atv (ImpInstConst t1 ms t2) = ftv t1 `Set.union` (ms `Set.intersection` ftv t2)
  atv (ExpInstConst t s) = ftv t `Set.union` ftv s

compose :: Ord n => Subst n -> Subst n -> Subst n
compose m1 m2 = (subst m1 <$> m2) `Map.union` m1

bind :: (Ord k, MonadError [Char] f) => k -> Type k -> f (Map.Map k (Type k))
bind n t | t == TyVar n = pure mempty
         | occursCheck n t = throwError ""
         | otherwise = pure (Map.singleton n t)

occursCheck :: (Ord n, FTV f n) => n -> f -> Bool
occursCheck n t = Set.member n (ftv t)

unifyRows l r = undefined

unifies t1 t2 | t1 == t2 = pure mempty
unifies (TyVar n) t2 = n `bind` t2
unifies t1 (TyVar n) = n `bind` t1
unifies (TyFun l r) (TyFun l' r') = do
  s1 <- unifies l l'
  s2 <- unifies (subst s1 r) (subst s1 r')
  pure (s2 `compose` s1)
unifies (TyRow l) (TyRow r) = unifyRows l r

