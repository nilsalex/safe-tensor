{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}

-----------------------------------------------------------------------------
{-|
Module      : Math.Tensor
Description : Existentially quantified wrapper for Math.Tensor.Safe.
Copyright   : (c) Nils Alex, 2020
License     : MIT
Maintainer  : nils.alex@fau.de
Stability   : experimental

Existentially quantified wrapper around the safe interface from 'Math.Tensor.Safe'.
In contrast to the safe interface, all tensor operations are fair game, but potentially
unsafe operations take place in the Error monad 'Control.Monad.Except' and may fail
with an error message.
-}
-----------------------------------------------------------------------------
module Math.Tensor
  ( -- * Existentially quantified around 'Tensor'
    T(..)
    -- * Fundamental operations
  , rankT
  , scalar
  , zero
    -- * Conversion from and to lists
  , toListT
  , fromListT
  , removeZerosT
    -- * Tensor algebra
  , (.*)
  , (.+)
  , (.-)
  , (#.)
    -- * Tensor operations
  , contractT
  , transposeT
  , transposeMultT
  , relabelT
  , -- * Constructing ranks
    conRank
  , covRank
  , conCovRank
  ) where

import Math.Tensor.Safe
import Math.Tensor.Safe.TH

import Data.Kind (Type)

import Data.Singletons
import Data.Singletons.Prelude
import Data.Singletons.Prelude.Maybe
import Data.Singletons.Decide
import Data.Singletons.TypeLits

import Data.Bifunctor (first)

import Data.List.NonEmpty (NonEmpty(..),sort)

import Control.Monad.Except

-- |'T' wraps around 'Tensor' and exposes only the value type @v@.
data T :: Type -> Type where
  T :: forall (r :: Rank) v. SingI r => Tensor r v -> T v

deriving instance Show v => Show (T v)

instance Functor T where
  fmap f (T t) = T $ fmap f t

-- |Produces a 'Scalar' of given value. Result is pure
-- because there is only one possible rank: @'[]@
scalar :: Num v => v -> T v
scalar v = T $ Scalar v

-- |Produces a 'ZeroTensor' of given rank @r@. Throws an
-- error if @'Sane' r ~ ''False'@.
zero :: (Num v, MonadError String m) => Demote Rank -> m (T v)
zero dr =
  withSomeSing dr $ \sr ->
  case sSane sr %~ STrue of
    Proved Refl ->
      case sr of
        (sing :: Sing r) -> withSingI sr $ return $ T (ZeroTensor :: Tensor r v)
    Disproved _ -> throwError $ "Illegal index list for zero : " ++ show dr

vecToList :: Vec n a -> [a]
vecToList VNil = []
vecToList (x `VCons` xs) = x : vecToList xs

vecFromList :: forall (n :: N) a m.
               MonadError String m => Sing n -> [a] -> m (Vec n a)
vecFromList SZ [] = return VNil
vecFromList (SS sn) [] = throwError "List provided for vector reconstruction is too short."
vecFromList SZ (_:_)   = throwError "List provided for vector reconstruction is too long."
vecFromList (SS sn) (x:xs) = do
  xs' <- vecFromList sn xs
  return $ x `VCons` xs'

-- |Pure function removing all zeros from a tensor. Wraps around 'removeZeros'.
removeZerosT :: (Eq v, Num v) => T v -> T v
removeZerosT o =
  case o of
    T t -> T $ removeZeros t

-- |Tensor product. Returns an error if ranks overlap, i.e.
-- @MergeR r1 r2 ~ 'Nothing@. Wraps around '(&*)'.
(.*) :: (Num v, MonadError String m) => T v -> T v -> m (T v)
(.*) o1 o2 =
  case o1 of
    T (t1 :: Tensor r1 v) ->
      case o2 of
        T (t2 :: Tensor r2 v) ->
          let sr1 = sing :: Sing r1
              sr2 = sing :: Sing r2
          in case sMergeR sr1 sr2 of
               SNothing  -> throwError "Tensors have overlapping indices. Cannot multiply."
               SJust sr' -> withSingI sr' $ return $ T (t1 &* t2)
infixl 7 .*

-- |Scalar multiplication of a tensor.
(#.) :: Num v => v -> T v -> T v
(#.) s = fmap (*s)

infixl 7 #.

-- |Tensor addition. Returns an error if summand ranks do not coincide. Wraps around '(&+)'.
(.+) :: (Eq v, Num v, MonadError String m) => T v -> T v -> m (T v)
(.+) o1 o2 =
  case o1 of
    T (t1 :: Tensor r1 v) ->
      case o2 of
        T (t2 :: Tensor r2 v) ->
          let sr1 = sing :: Sing r1
              sr2 = sing :: Sing r2
          in case sr1 %~ sr2 of
               Proved Refl -> case sSane sr1 %~ STrue of
                                Proved Refl -> return $ T (t1 &+ t2)
               Disproved _ -> throwError "Generalized tensor ranks do not match. Cannot add."
infixl 6 .+

-- |Tensor subtraction. Returns an error if summand ranks do not coincide. Wraps around '(&-)'.
(.-) :: (Eq v, Num v, MonadError String m) => T v -> T v -> m (T v)
(.-) o1 o2 =
  case o1 of
    T (t1 :: Tensor r1 v) ->
      case o2 of
        T (t2 :: Tensor r2 v) ->
          let sr1 = sing :: Sing r1
              sr2 = sing :: Sing r2
          in case sr1 %~ sr2 of
               Proved Refl -> case sSane sr1 %~ STrue of
                                Proved Refl -> return $ T (t1 &- t2)
               Disproved _ -> throwError "Generalized tensor ranks do not match. Cannot add."

-- |Tensor contraction. Pure function, because a tensor of any rank can be contracted.
-- Wraps around 'contract'.
contractT :: (Num v, Eq v) => T v -> T v
contractT o =
  case o of
    T (t :: Tensor r v) ->
      let sr = sing :: Sing r
          sr' = sContractR sr
      in withSingI sr' $ T $ contract t

-- |Tensor transposition. Returns an error if given indices cannot be transposed.
-- Wraps around 'transpose'.
transposeT :: MonadError String m =>
              Demote (VSpace Symbol Nat) -> Demote (Ix Symbol) -> Demote (Ix Symbol) ->
              T v -> m (T v)
transposeT v ia ib o = 
  case o of
    T (t :: Tensor r v) ->
      let sr = sing :: Sing r
      in withSingI sr $
         withSomeSing v $ \sv ->
         withSomeSing ia $ \sia ->
         withSomeSing ib $ \sib ->
         case sCanTranspose sv sia sib sr of
           STrue  -> return $ T $ transpose sv sia sib t
           SFalse -> throwError $ "Cannot transpose indices " ++ show v ++ " " ++ show ia ++ " " ++ show ib ++ "!"

-- |Transposition of multiple indices. Returns an error if given indices cannot be transposed.
-- Wraps around 'transposeMult'.
transposeMultT :: MonadError String m =>
                  Demote (VSpace Symbol Nat) -> Demote [(Symbol,Symbol)] -> Demote [(Symbol,Symbol)] -> T v -> m (T v)
transposeMultT _ [] [] _ = throwError $ "Empty lists for transpositions!"
transposeMultT v (con:cons) [] o =
  case o of
    T (t :: Tensor r v) ->
      let sr = sing :: Sing r
          cons' = sort $ con :| cons
          tr = (\xs ys -> TransCon xs ys) (fmap fst cons') (fmap snd cons')
      in withSingI sr $
         withSomeSing v $ \sv ->
         withSomeSing tr $ \str ->
         case sIsJust (sTranspositions sv str sr) %~ STrue of
           Proved Refl -> return $ T $ transposeMult sv str t
           Disproved _ -> throwError $ "Cannot transpose indices " ++ show v ++ " " ++ show tr ++ "!"
transposeMultT v [] (cov:covs) o =
  case o of
    T (t :: Tensor r v) ->
      let sr = sing :: Sing r
          covs' = sort $ cov :| covs
          tr = (\xs ys -> TransCov xs ys) (fmap fst covs') (fmap snd covs')
      in withSingI sr $
         withSomeSing v $ \sv ->
         withSomeSing tr $ \str ->
         case sIsJust (sTranspositions sv str sr) %~ STrue of
           Proved Refl -> return $ T $ transposeMult sv str t
           Disproved _ -> throwError $ "Cannot transpose indices " ++ show v ++ " " ++ show tr ++ "!"
transposeMultT _ _ _ _ = throwError $ "Simultaneous transposition of contravariant and covariant indices not yet supported!"

-- |Relabelling of tensor indices. Returns an error if given relabellings are not allowed.
-- Wraps around 'relabel'.
relabelT :: MonadError String m =>
            Demote (VSpace Symbol Nat) -> Demote [(Symbol,Symbol)] -> T v -> m (T v)
relabelT _ [] _ = throwError $ "Empty list for relabelling!"
relabelT v (r:rs) o =
  case o of
    T (t :: Tensor r v) ->
      let sr = sing :: Sing r
          rr = sort $ r :| rs
      in withSingI sr $
         withSomeSing v $ \sv ->
         withSomeSing rr $ \srr ->
         case sRelabelR sv srr sr of
           SJust sr' ->
             withSingI sr' $
             case sSane sr' %~ STrue of
               Proved Refl -> return $ T $ relabel sv srr t
               Disproved _ -> throwError $ "Cannot relabel indices " ++ show v ++ " " ++ show rr ++ "!"
           _ -> throwError $ "Cannot relabel indices " ++ show v ++ " " ++ show rr ++ "!"

-- |Exposes the hidden rank over which 'T' quantifies. Possible because of the @'SingI' r@ constraint.
rankT :: T v -> Demote Rank
rankT o =
  case o of
    T (t :: Tensor r v) ->
      let sr = sing :: Sing r
      in fromSing sr

-- |Assocs list of the tensor.
toListT :: T v -> [([Int], v)]
toListT o =
  case o of
    T (t :: Tensor r v) -> let sr = sing :: Sing r 
                               sn = sLengthR sr
                           in withSingI sn $
                              first vecToList <$> toList t

-- |Constructs a tensor from a rank and an assocs list. Returns an error for illegal ranks
-- or incompatible assocs lists.
fromListT :: MonadError String m => Demote Rank -> [([Int], v)] -> m (T v)
fromListT r xs =
  withSomeSing r $ \sr ->
  withSingI sr $
  let sn = sLengthR sr
  in case sSane sr %~ STrue of
    Proved Refl -> T . fromList' sr <$> 
                   mapM (\(vec, val) -> do
                                         vec' <- vecFromList sn vec
                                         return (vec', val)) xs

-- |Lifts sanity check of ranks into the error monad.
saneRank :: (Ord s, Ord n, MonadError String m) => GRank s n -> m (GRank s n)
saneRank r
    | sane r = pure r
    | otherwise = throwError "Index lists must be strictly ascending."

-- |Creates contravariant rank from vector space labe, vector space dimension,
-- and list of index labels. Returns an error for illegal ranks.
conRank :: (MonadError String m, Integral a, Ord s, Ord n, Num n) =>
           s -> a -> [s] -> m (GRank s n)
conRank _ _ [] = throwError "Generalized rank must have non-vanishing index list!"
conRank v d (i:is) = saneRank $ [(VSpace v (fromIntegral d), Con (i :| is))]

-- |Creates covariant rank from vector space labe, vector space dimension,
-- and list of index labels. Returns an error for illegal ranks.
covRank :: (MonadError String m, Integral a, Ord s, Ord n, Num n) =>
           s -> a -> [s] -> m (GRank s n)
covRank _ _ [] = throwError "Generalized rank must have non-vanishing index list!"
covRank v d (i:is) = saneRank $ [(VSpace v (fromIntegral d), Cov (i :| is))]

-- |Creates mixed rank from vector space label, vector space dimension,
-- and lists of index labels. Returns an error for illegal ranks.
conCovRank :: (MonadError String m, Integral a, Ord s, Ord n, Num n) =>
              s -> a -> [s] -> [s] -> m (GRank s n)
conCovRank _ _ _ [] = throwError "Generalized rank must have non-vanishing index list!"
conCovRank _ _ [] _ = throwError "Generalized rank must have non-vanishing index list!"
conCovRank v d (i:is) (j:js) = saneRank $ [(VSpace v (fromIntegral d), ConCov (i :| is) (j :| js))]
