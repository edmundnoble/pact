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
import Data.Set(Set)
import Data.Foldable(fold)
import Data.Map(Map)
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import Data.List(find)
import Data.Maybe (fromJust, fromMaybe)
import Control.Monad.Except
import Control.Monad.Reader
-- import Control.Monad.State.Strict
import Pact.Core.Type
import Pact.Core.Names
import Pact.Core.IR.Term
import Pact.Core.IR.Typecheck.Assumption (Assumption(..))
import qualified Pact.Core.IR.Typecheck.Assumption as AS

data TyScheme n = TyScheme [n] [n] (Type n)
  deriving (Eq, Show)

data TCEnv name tyname builtin
  = TCEnv
  { _tcSupply :: Supply -- ^ Fresh name supply
  , _tcEnv :: Map.Map name (TyScheme tyname) -- ^ Typescheme environment
  , _tcNonGen :: Set.Set tyname -- ^ Monomorphic set to not generalize
  , _tcLiftName :: Unique -> tyname
  , _tcBuiltin :: Map.Map builtin (TyScheme tyname) }

makeLenses ''TCEnv

freshVar :: (MonadIO m, MonadReader (TCEnv name tyname builtin) m) => m tyname
freshVar = do
  f <- view tcLiftName
  s <- view tcSupply
  f <$> liftIO (newUnique s)


data Constraint n
  = EqConst (Type n) (Type n)
  | ExpInstConst (Type n) (TyScheme n)
  | ImpInstConst (Type n) (Set.Set n) (Type n)
  deriving (Eq, Show)


-- type Subst n = Map.Map n (Type n)
data Subst n
  = Subst
  { _stypes :: Map n (Type n)
  , _srows :: Map n (Row n)
  } deriving (Eq, Show)

data FreeTyVars n
  = FreeTyVars
  { _ftvTy :: Set n
  , _ftvRow :: Set n
  } deriving (Eq, Show)

makeLenses ''Subst
makeLenses ''FreeTyVars

ftvIntersection :: Ord n => FreeTyVars n -> FreeTyVars n -> FreeTyVars n
ftvIntersection (FreeTyVars l r) (FreeTyVars l' r') =
  FreeTyVars (Set.intersection l l') (Set.intersection r r')

instance Ord n => Semigroup (Subst n) where
  (Subst l r) <> (Subst l' r') = Subst (l <> l') (r <> r')

instance Ord n => Monoid (Subst n) where
  mempty = Subst mempty mempty

instance Ord n => Semigroup (FreeTyVars n) where
  (FreeTyVars l r) <> (FreeTyVars l' r') = FreeTyVars (l <> l') (r <> r')

instance Ord n => Monoid (FreeTyVars n) where
  mempty = FreeTyVars mempty mempty

class Substitutable p n | p -> n where
  subst :: Subst n -> p -> p

-- instance Ord n => Substitutable (Rho n) n where
--   subst s@(Subst _ rows) = \case
--     RhoPredicate preds ty ->
--       RhoPredicate (foldr f [] preds) (subst s ty)
--     where
--     f (WithoutField var field) li = case rows ^. at var of
--       Nothing -> WithoutField var field:li
--       Just row -> case row of
--         RowTy  _ _-> li
--         RowVar n -> WithoutField n field : li
--         EmptyRow -> li


instance Ord n => Substitutable (Row n) n where
  subst s@(Subst _ rows) = \case
    RowVar r -> fromMaybe (RowVar r) $ rows ^. at r
    EmptyRow -> EmptyRow
    RowTy fields mv ->
      case mv of
        Nothing -> RowTy (subst s <$> fields) Nothing
        Just rv -> case rows ^. at rv of
          Just (RowVar rv') -> subst s (RowTy fields (Just rv'))
          Just (RowTy fields' rv') -> subst s (RowTy (Map.union fields fields') rv')
          Just EmptyRow -> RowTy (subst s <$> fields) Nothing
          _ -> RowTy (subst s <$> fields) mv

instance Ord n => Substitutable (Type n) n where
  subst s@(Subst tys rows) = \case
    TyVar n -> fromMaybe (TyVar n) $ tys ^. at n
    TyPrim p -> TyPrim p
    TyList ty -> TyList (subst s ty)
    TyRow r -> TyRow $ subst s r
    TyFun l r -> TyFun (subst s l) (subst s r)
    TyForall ns rs ty ->
      let tys' = Map.fromList [(n', TyVar n') | n' <- ns] `Map.union` tys
          rows' = Map.fromList [(r', RowVar r') | r' <- rs] `Map.union` rows
      in TyForall ns rs (subst (Subst tys' rows') ty)

instance Ord n => Substitutable (TyScheme n) n where
  subst m (TyScheme ns rs ty) =
    let m' = m  <> Subst (Map.fromList [(n', TyVar n') | n' <- ns]) (Map.fromList [(r', RowVar r') | r' <- rs])
    in TyScheme ns rs (subst m' ty)

instance Ord n => Substitutable (Constraint n) n where
   subst s (EqConst t1 t2) = EqConst (subst s t1) (subst s t2)
   subst s (ExpInstConst t sc) = ExpInstConst (subst s t) (subst s sc)
   subst s (ImpInstConst t1 ms t2) = ImpInstConst (subst s t1) (Set.map setSubst ms) (subst s t2)
    where
    setSubst n = case _stypes s ^. at n of
      Just (TyVar n') -> n'
      _ -> n

class FTV p n | p -> n where
  ftv :: p -> FreeTyVars n

instance Ord n => FTV (Map.Map n (Type n)) n where
  ftv = foldMap ftv

instance Ord n => FTV (Type n) n where
  ftv = \case
    TyVar n -> FreeTyVars (Set.singleton n) mempty
    TyPrim _ -> mempty
    TyFun l r -> ftv l <> ftv r
    TyRow rows -> ftv rows
    TyList t -> ftv t
    -- TyTable _ rows -> ftv rows
    -- TyInterface _ rows -> ftv rows
    TyForall ns rs typ ->
      let (FreeTyVars fts frs) = ftv typ
      in FreeTyVars (fts `Set.difference` Set.fromList ns) (frs `Set.difference` Set.fromList rs)

instance Ord n => FTV (Row n) n where
  ftv = \case
    RowTy m n -> ftv m <> maybe mempty (FreeTyVars mempty . Set.singleton) n
    RowVar n -> FreeTyVars mempty (Set.singleton n)
    EmptyRow -> mempty

instance Ord n => FTV (TyScheme n) n where
  ftv (TyScheme ns rs typ) =
    let (FreeTyVars tys rows) = ftv typ
    in FreeTyVars (tys `Set.difference` Set.fromList ns) (rows `Set.difference` Set.fromList rs)

class ActiveTypeVars p n | p -> n where
  atv :: p -> FreeTyVars n

instance Ord n => ActiveTypeVars (Constraint n) n where
  atv (EqConst t1 t2) = ftv t1 <> ftv t2
  atv (ImpInstConst t1 ms t2) = ftv t1 <> (FreeTyVars ms mempty `ftvIntersection` ftv t2)
  atv (ExpInstConst t s) = ftv t <> ftv s

compose :: Ord n => Subst n -> Subst n -> Subst n
compose m1 m2 =
  let m2' = m2 & stypes . mapped %~ subst m1 & srows . mapped %~ subst m1
  in m2' <> m1

-- Occurs checking
bind :: (Ord tyname, MonadError [Char] f) => tyname -> Type tyname -> f (Subst tyname)
bind n t | t == TyVar n = pure mempty
         | occursCheck n t = throwError ""
         | otherwise = pure $ Subst (Map.singleton n t) mempty

-- todo: occurs check for rows.
bindRow :: (Ord tyname, MonadError [Char] f) => tyname -> Row tyname -> f (Subst tyname)
bindRow n t | t == RowVar n = pure mempty
            | otherwise = pure $ Subst mempty (Map.singleton n t)

occursCheck :: (Ord n, FTV f n) => n -> f -> Bool
occursCheck n t = Set.member n $ _ftvTy (ftv t)

unifyRows ::
  ( Ord n, MonadError [Char] m
  , MonadIO m
  , MonadReader (TCEnv name n builtin) m) =>
  Row n -> Row n -> m (Subst n)
unifyRows (RowVar n) t =  n `bindRow` t
unifyRows t (RowVar n)  =  n `bindRow` t
-- Unify labels present in both m and m'
-- Labels not present: unify with row variable.
unifyRows (RowTy m mrv) (RowTy m' mrv') =
  case (mrv, mrv') of
    -- Two open rows
    (Just rv, Just rv') -> do
      unif <- fold <$> traverse (uncurry unifies) (Map.intersectionWith (,) m m')
      leftVar <- freshVar
      rightVar <- freshVar
      let notInR = Map.difference m m'
          notInRSubst = (rv,) $ if Map.null notInR then RowVar leftVar else RowTy notInR (Just leftVar)
          notInL = Map.difference m' m
          notInLSubst = (rv',) $ if Map.null notInL then RowVar rightVar else RowTy notInR (Just rightVar)
      pure $ unif <> Subst mempty (Map.fromList [notInRSubst, notInLSubst])
    -- Right closed
    -- Means Keys(l) <= Keys(r)
    (Just rv, Nothing) -> do
      if all (`Map.member` m') (Map.keys m) then do
        unif <- fold <$> traverse (uncurry unifies) (Map.intersectionWith (,) m m')
        let diff = Map.difference m' m
            s = if Map.null diff then EmptyRow else RowTy diff Nothing
        pure $ unif <> Subst mempty (Map.singleton rv s)
      else throwError "Row does not unify"
    -- Left closed
    (Nothing, Just rv) -> do
      if all (`Map.member` m) (Map.keys m') then do
        unif <- fold <$> traverse (uncurry unifies) (Map.intersectionWith (,) m m')
        let diff = Map.difference m m'
            s = if Map.null diff then EmptyRow else RowTy diff Nothing
        pure $ unif <> Subst mempty (Map.singleton rv s)
      else throwError "Row does not unify"
    (Nothing, Nothing) ->
      if Map.keys m == Map.keys m' then
        fold <$> traverse (uncurry unifies) (Map.intersectionWith (,) m m')
      else throwError "Row does not unify"
unifyRows EmptyRow EmptyRow = pure mempty
unifyRows _ _ = throwError "row unif mismatch"


-- note: For IR we currently don't unify against
-- `TyForall`, we don't allow rankN despite it showing up in
-- our type language.
unifies ::
  ( Ord tyname
  , MonadError String m
  , MonadIO m
  , MonadReader (TCEnv name tyname builtin) m)
  => Type tyname
  -> Type tyname
  -> m (Subst tyname)
unifies t1 t2 | t1 == t2 = pure mempty
unifies (TyVar n) t2 = n `bind` t2
unifies t1 (TyVar n) = n `bind` t1
unifies (TyFun l r) (TyFun l' r') = do
  s1 <- unifies l l'
  s2 <- unifies (subst s1 r) (subst s1 r')
  pure (s2 `compose` s1)
unifies (TyRow l) (TyRow r) = unifyRows l r
unifies _ _ = error "reee"

generalize :: Ord n => FreeTyVars n -> Type n -> TyScheme n
generalize (FreeTyVars freetys freerows) t  = TyScheme as rs t
  where
  (FreeTyVars ftys frows) = ftv t
  as = Set.toList $ ftys`Set.difference` freetys
  rs = Set.toList $ frows `Set.difference` freerows

instantiate :: (MonadIO m, MonadReader (TCEnv name tyname builtin) m, Ord tyname) => TyScheme tyname -> m (Type tyname)
instantiate (TyScheme as rs t) = do
    as' <- traverse (const freshVar) as
    rs' <- traverse (const freshVar) rs
    let tyS = Map.fromList $ zip as (TyVar <$> as')
        rowS = Map.fromList $ zip rs (RowVar <$> rs')
    return $ subst (Subst tyS rowS) t

-- todo: propagate infos for better errors.
inferExpr :: (Ord tyname, Ord builtin, Ord name, MonadReader (TCEnv name tyname builtin) m, MonadIO m)
      => Term name builtin info
      -> m (Assumption name tyname, [Constraint tyname], Type tyname)
inferExpr = \case
  Constant l _ ->
    pure (AS.empty, [], typeOfLit l)
  Var n _ -> do
    tv <- TyVar <$> freshVar
    pure (AS.singleton n tv, [], tv)
  Lam n body _ -> do
    rawTv <- freshVar
    let tv = TyVar rawTv
    (as, cs, t) <- locally tcNonGen (Set.insert rawTv) (inferExpr body)
    pure (AS.remove as n, cs ++ [EqConst t' tv | t' <- AS.lookup n as], TyFun tv t)
  -- I suspect this incorrectly quantifies row vars.
  -- I'm not yet sure how to have principled row quantification with constraints.
  -- the issue is a row variable in `e1` will most likely be quantified over since it's not included
  -- in `monoSet`. In general: introduction of row variables is strange and likely can't be done without
  -- predicate quantification, which I've yet to add.
  Let n e1 e2 _ -> do
    (as1, cs1, t1) <- inferExpr e1
    (as2, cs2, t2) <- inferExpr e2
    monoSet <- view tcNonGen
    pure
      ( AS.remove (AS.merge as1 as2) n
      , cs1 ++ cs2 ++ [ImpInstConst t' monoSet t1 | t' <- AS.lookup n as2]
      , t2)
  App e1 e2 _ -> do
    tv <- TyVar <$> freshVar
    (as1, cs1, t1) <- inferExpr e1
    (as2, cs2, t2) <- inferExpr e2
    pure ( as1 `AS.merge` as2
         , cs1 ++ cs2 ++ [EqConst t1 (TyFun t2 tv)]
         , tv )
  Sequence e1 e2 _ -> do
    -- Will we require that the lhs of sequenced statements be unit?
    -- likely yes, it doesn't make sense to otherwise discard value results without binding them in a clause.
    -- for now, no.
    (as1, cs1, _) <- inferExpr e1
    (as2, cs2, t2) <- inferExpr e2
    pure (as1 `AS.merge` as2, cs1 ++ cs2, t2)
  Error _ _ -> do
    tv <- TyVar <$> freshVar
    pure (AS.empty, [], tv)
  DynAccess _ _ -> undefined
  Builtin b _ -> do
    benv <- view tcBuiltin
    bty <- instantiate $ benv Map.! b
    pure (AS.empty, [], bty)

----------------------------
-- Constraint solving
----------------------------

nextSolvable :: Ord a => [Constraint a] -> (Constraint a, [Constraint a])
nextSolvable xs = fromJust (find solvable (chooseOne xs))
  where
    -- todo: this is using EQ instance for constraint.
    -- [(x, ys) | x <- xss, let ys = delete x xss]
    --
    chooseOne xss = chooseOne' [] xss
    chooseOne' acc = \case
      x:xs' -> (x, reverse acc ++ xs'): chooseOne' (x:acc) xs'
      [] -> []
    solvable (EqConst{}, _) = True
    solvable (ExpInstConst{}, _) = True
    solvable (ImpInstConst _ ms t2, cs) =
      let FreeTyVars atvs _ = foldMap atv cs
          FreeTyVars t2' _ = ftv t2
      in  Set.null ((t2' `Set.difference` ms) `Set.intersection` atvs)

solve :: (Ord tyname, MonadError String m, MonadIO m, MonadReader (TCEnv name tyname builtin) m) => [Constraint tyname] -> m (Subst tyname)
solve [] = return mempty
solve cs = solve' (nextSolvable cs)

solve' ::
  ( Ord tyname
  , MonadError String m
  , MonadIO m
  , MonadReader (TCEnv name tyname builtin) m)
  => (Constraint tyname, [Constraint tyname])
  -> m (Subst tyname)
solve' (EqConst t1 t2, cs) = do
  su1 <- unifies t1 t2
  su2 <- solve (fmap (subst su1) cs)
  return (su2 `compose` su1)
solve' (ImpInstConst t1 ms t2, cs) =
  solve (ExpInstConst t1 (generalize (FreeTyVars ms mempty) t2) : cs)
solve' (ExpInstConst t s, cs) = do
  s' <- instantiate s
  solve (EqConst t s' : cs)
