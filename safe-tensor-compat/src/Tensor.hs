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

module Tensor where

import Safe
import TH

import Data.Kind (Type)

import Data.Singletons
import Data.Singletons.Prelude
import Data.Singletons.Prelude.Maybe
import Data.Singletons.Decide
import Data.Singletons.TypeLits

import Data.Bifunctor (first)

import Data.List.NonEmpty (NonEmpty(..),sort)

import Control.Monad.Except

type Label = Demote Symbol

data T :: Type -> Type where
  T :: SingI l => Tensor l v -> T v

deriving instance Show v => Show (T v)

instance Functor T where
  fmap f (T t) = T $ fmap f t

scalar :: Num v => v -> T v
scalar v = T $ Scalar v

zero :: (Num v, MonadError String m) => Demote ILists -> m (T v)
zero il =
  withSomeSing il $ \sil ->
  case sSane sil %~ STrue of
    Proved Refl ->
      case sil of
        (sing :: Sing l) -> withSingI sil $ return $ T (ZeroTensor :: Tensor l v)
    Disproved _ -> throwError $ "Illegal index list for zero : " ++ show il

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

removeZerosT :: (Eq v, Num v) => T v -> T v
removeZerosT o =
  case o of
    T t -> T $ removeZeros t

(.*) :: (Num v, MonadError String m) => T v -> T v -> m (T v)
(.*) o1 o2 =
  case o1 of
    T (t1 :: Tensor l1 v) ->
      case o2 of
        T (t2 :: Tensor l2 v) ->
          let sl1 = sing :: Sing l1
              sl2 = sing :: Sing l2
          in case sMergeILs sl1 sl2 of
               SNothing  -> throwError "Tensors have overlapping indices. Cannot multiply."
               SJust sl' -> withSingI sl' $ return $ T (mult sl1 sl2 t1 t2)
infixl 7 .*

(#.) :: Num v => v -> T v -> T v
(#.) s = fmap (*s)

infixl 7 #.

(.+) :: (Eq v, Num v, MonadError String m) => T v -> T v -> m (T v)
(.+) o1 o2 =
  case o1 of
    T (t1 :: Tensor l1 v) ->
      case o2 of
        T (t2 :: Tensor l2 v) ->
          let sl1 = sing :: Sing l1
              sl2 = sing :: Sing l2
          in case sl1 %~ sl2 of
               Proved Refl -> case sSane sl1 %~ STrue of
                                Proved Refl -> return $ T (t1 &+ t2)
               Disproved _ -> throwError "Generalized tensor ranks do not match. Cannot add."
infixl 6 .+

(.-) :: (Eq v, Num v, MonadError String m) => T v -> T v -> m (T v)
(.-) o1 o2 =
  case o1 of
    T (t1 :: Tensor l1 v) ->
      case o2 of
        T (t2 :: Tensor l2 v) ->
          let sl1 = sing :: Sing l1
              sl2 = sing :: Sing l2
          in case sl1 %~ sl2 of
               Proved Refl -> case sSane sl1 %~ STrue of
                                Proved Refl -> return $ T (t1 &- t2)
               Disproved _ -> throwError "Generalized tensor ranks do not match. Cannot add."

contractT :: (Num v, Eq v) => T v -> T v
contractT o =
  case o of
    T (t :: Tensor l v) ->
      let sl = sing :: Sing l
          sl' = sContractL sl
      in withSingI sl' $ T $ contract' sl t

transposeT :: MonadError String m =>
              Demote (VSpace Symbol Nat) -> Demote (Ix Symbol) -> Demote (Ix Symbol) ->
              T v -> m (T v)
transposeT v ia ib o = 
  case o of
    T (t :: Tensor l v) ->
      let sl = sing :: Sing l
      in withSingI sl $
         withSomeSing v $ \sv ->
         withSomeSing ia $ \sia ->
         withSomeSing ib $ \sib ->
         case sCanTranspose sv sia sib sl of
           STrue  -> return $ T $ transpose sv sia sib t
           SFalse -> throwError $ "Cannot transpose indices " ++ show v ++ " " ++ show ia ++ " " ++ show ib ++ "!"

transposeMultT :: MonadError String m =>
                  Demote (VSpace Symbol Nat) -> Demote [(Symbol,Symbol)] -> Demote [(Symbol,Symbol)] -> T v -> m (T v)
transposeMultT _ [] [] _ = throwError $ "Empty lists for transpositions!"
transposeMultT v (con:cons) [] o =
  case o of
    T (t :: Tensor l v) ->
      let sl = sing :: Sing l
          cons' = sort $ con :| cons
          tl = (\xs ys -> TransCon xs ys) (fmap fst cons') (fmap snd cons')
      in withSingI sl $
         withSomeSing v $ \sv ->
         withSomeSing tl $ \stl ->
         case sIsJust (sTranspositions sv stl sl) %~ STrue of
           Proved Refl -> return $ T $ transposeMult sv stl t
           Disproved _ -> throwError $ "Cannot transpose indices " ++ show v ++ " " ++ show tl ++ "!"
transposeMultT v [] (cov:covs) o =
  case o of
    T (t :: Tensor l v) ->
      let sl = sing :: Sing l
          covs' = sort $ cov :| covs
          tl = (\xs ys -> TransCov xs ys) (fmap fst covs') (fmap snd covs')
      in withSingI sl $
         withSomeSing v $ \sv ->
         withSomeSing tl $ \stl ->
         case sIsJust (sTranspositions sv stl sl) %~ STrue of
           Proved Refl -> return $ T $ transposeMult sv stl t
           Disproved _ -> throwError $ "Cannot transpose indices " ++ show v ++ " " ++ show tl ++ "!"
transposeMultT _ _ _ _ = throwError $ "Simultaneous transposition of contravariant and covariant indices not yet supported!"

relabelT :: MonadError String m =>
            Demote (VSpace Symbol Nat) -> Demote [(Symbol,Symbol)] -> T v -> m (T v)
relabelT _ [] _ = throwError $ "Empty list for relabelling!"
relabelT v (r:rs) o =
  case o of
    T (t :: Tensor l v) ->
      let sl = sing :: Sing l
          rl = sort $ r :| rs
      in withSingI sl $
         withSomeSing v $ \sv ->
         withSomeSing rl $ \srl ->
         case sRelabelILs sv srl sl of
           SJust sl' ->
             withSingI sl' $
             case sSane sl' %~ STrue of
               Proved Refl -> return $ T $ relabel sv srl t
               Disproved _ -> throwError $ "Cannot relabel indices " ++ show v ++ " " ++ show rl ++ "!"
           _ -> throwError $ "Cannot relabel indices " ++ show v ++ " " ++ show rl ++ "!"

rankT :: T v -> Demote ILists
rankT o =
  case o of
    T (t :: Tensor l v) ->
      let sl = sing :: Sing l
      in fromSing sl

toListT :: T v -> [([Int], v)]
toListT o =
  case o of
    T (t :: Tensor l v) -> let sl = sing :: Sing l
                               sn = sLengthILs sl
                           in withSingI sn $
                              first vecToList <$> toList t

fromListT :: MonadError String m => Demote ILists -> [([Int], v)] -> m (T v)
fromListT ils xs =
  withSomeSing ils $ \sils ->
  withSingI sils $
  let sn = sLengthILs sils
  in case sSane sils %~ STrue of
    Proved Refl -> T . fromList' sils <$> 
                   mapM (\(vec, val) -> do
                                         vec' <- vecFromList sn vec
                                         return (vec', val)) xs

type GenRank = Demote ILists

saneRank :: MonadError String m => GenRank -> m GenRank
saneRank r
    | sane r = pure r
    | otherwise = throwError "Index lists must be strictly ascending."

conRank :: (MonadError String m, Integral a) => Label -> a -> [Label] -> m GenRank
conRank _ _ [] = throwError "Generalized rank must have non-vanishing index list!"
conRank v d (i:is) = saneRank $ [(VSpace v (fromIntegral d), Con (i :| is))]

covRank :: (MonadError String m, Integral a) => Label -> a -> [Label] -> m GenRank
covRank _ _ [] = throwError "Generalized rank must have non-vanishing index list!"
covRank v d (i:is) = saneRank $ [(VSpace v (fromIntegral d), Cov (i :| is))]

conCovRank :: (MonadError String m, Integral a) => Label -> a -> [Label] -> [Label] -> m GenRank
conCovRank _ _ _ [] = throwError "Generalized rank must have non-vanishing index list!"
conCovRank _ _ [] _ = throwError "Generalized rank must have non-vanishing index list!"
conCovRank v d (i:is) (j:js) = saneRank $ [(VSpace v (fromIntegral d), ConCov (i :| is) (j :| js))]
