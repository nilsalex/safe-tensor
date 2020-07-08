{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}

-----------------------------------------------------------------------------
{-|
Module      : Math.Tensor
Description : Existentially quantified wrapper for Math.Tensor.Safe.
Copyright   : (c) Nils Alex, 2020
License     : MIT
Maintainer  : nils.alex@fau.de

Existentially quantified wrapper around the safe interface from "Math.Tensor.Safe".
In contrast to the safe interface, all tensor operations are fair game, but potentially
illegal operations take place in the Error monad "Control.Monad.Except" and may fail
with an error message.

For usage examples, see <https://github.com/nilsalex/safe-tensor/#readme>.

For the documentation on generalized tensor ranks, see "Math.Tensor.Safe".
-}
-----------------------------------------------------------------------------
module Math.Tensor
  ( -- * Existentially quantified tensor
    -- |Wrapping a @'Tensor' r v@ in a @'T' v@ allows to define tensor operations like
    -- additions or multiplications without any constraints on the generalized ranks
    -- of the operands.
    T(..)
  , -- * Unrefined rank types
    -- |These unrefined versions of the types used to parameterise generalized tensor
    -- ranks are used in functions producing or manipulating existentially quantified
    -- tensors.
    Label
  , Dimension
  , RankT
    -- * Tensor operations
    -- |The existentially quantified versions of tensor operations from "Math.Tensor.Safe".
    -- Some operations are always safe and therefore pure. The unsafe operations take place
    -- in the Error monad "Control.Monad.Except".
  , rankT
    -- ** Special tensors
  , scalarT
  , zeroT
    -- ** Conversion from and to lists
  , toListT
  , fromListT
  , removeZerosT
    -- ** Tensor algebra
  , (.*)
  , (.+)
  , (.-)
  , (.°)
    -- ** Other operations
  , contractT
  , transposeT
  , transposeMultT
  , relabelT
  , -- * Rank construction
    conRank
  , covRank
  , conCovRank
  ) where

import Math.Tensor.Safe
import Math.Tensor.Safe.TH

import Data.Kind (Type)

import Data.Singletons
  ( Sing, SingI (sing), Demote
  , withSomeSing, withSingI
  , fromSing
  )
import Data.Singletons.Prelude
import Data.Singletons.Prelude.Maybe
  ( sIsJust
  )
import Data.Singletons.Decide
  ( Decision(Proved, Disproved)
  , (:~:) (Refl), (%~)
  )
import Data.Singletons.TypeLits
  ( Nat
  , Symbol
  )

import Data.Bifunctor (first)

import Data.List.NonEmpty (NonEmpty((:|)),sort)

import Control.Monad.Except (MonadError, throwError)

-- |'T' wraps around 'Tensor' and exposes only the value type @v@.
data T :: Type -> Type where
  T :: forall (r :: Rank) v. SingI r => Tensor r v -> T v

deriving instance Show v => Show (T v)

instance Functor T where
  fmap f (T t) = T $ fmap f t

-- |The unrefined type of labels.
--
-- @ Demote Symbol ~ 'Data.Text.Text' @
type Label     = Demote Symbol

-- |The unrefined type of dimensions.
--
-- @ Demote Nat ~ 'GHC.Natural.Natural' @
type Dimension = Demote Nat

-- |The unrefined type of generalized tensor ranks.
--
-- @ 'Demote' 'Rank' ~ 'GRank' 'Label' 'Dimension' ~ [('VSpace' 'Label' 'Dimension', 'IList' 'Dimension')] @
type RankT     = Demote Rank

-- |'Scalar' of given value. Result is pure
-- because there is only one possible rank: @'[]@
scalarT :: v -> T v
scalarT v = T $ Scalar v

-- |'ZeroTensor' of given rank @r@. Throws an
-- error if @'Sane' r ~ ''False'@.
zeroT :: MonadError String m => RankT -> m (T v)
zeroT dr =
  withSomeSing dr $ \sr ->
  case sSane sr %~ STrue of
    Proved Refl ->
      case sr of
        (_ :: Sing r) -> withSingI sr $ return $ T (ZeroTensor :: Tensor r v)
    Disproved _ -> throwError $ "Illegal index list for zero : " ++ show dr

vecToList :: Vec n a -> [a]
vecToList VNil = []
vecToList (x `VCons` xs) = x : vecToList xs

vecFromList :: forall (n :: N) a m.
               MonadError String m => Sing n -> [a] -> m (Vec n a)
vecFromList SZ [] = return VNil
vecFromList (SS _) [] = throwError "List provided for vector reconstruction is too short."
vecFromList SZ (_:_)   = throwError "List provided for vector reconstruction is too long."
vecFromList (SS sn) (x:xs) = do
  xs' <- vecFromList sn xs
  return $ x `VCons` xs'

-- |Pure function removing all zeros from a tensor. Wraps around 'removeZeros'.
removeZerosT :: (Eq v, Num v) => T v -> T v
removeZerosT o =
  case o of
    T t -> T $ removeZeros t

-- |Tensor product. Throws an error if ranks overlap, i.e.
-- @'MergeR' r1 r2 ~ ''Nothing'@. Wraps around '(&*)'.
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
(.°) :: Num v => v -> T v -> T v
(.°) s = fmap (*s)

infixl 7 .°

-- |Tensor addition. Throws an error if summand ranks do not coincide. Wraps around '(&+)'.
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
                                Disproved _ -> throwError "Rank of summands is not sane."
               Disproved _ -> throwError "Generalized tensor ranks do not match. Cannot add."
infixl 6 .+

-- |Tensor subtraction. Throws an error if summand ranks do not coincide. Wraps around '(&-)'.
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
                                Disproved _ -> throwError "Rank of operands is not sane."
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

-- |Tensor transposition. Throws an error if given indices cannot be transposed.
-- Wraps around 'transpose'.
transposeT :: MonadError String m =>
              VSpace Label Dimension -> Ix Label -> Ix Label ->
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

-- |Transposition of multiple indices. Throws an error if given indices cannot be transposed.
-- Wraps around 'transposeMult'.
transposeMultT :: MonadError String m =>
                  VSpace Label Dimension -> [(Label,Label)] -> [(Label,Label)] -> T v -> m (T v)
transposeMultT _ [] [] _ = throwError "Empty lists for transpositions!"
transposeMultT v (con:cons) [] o =
  case o of
    T (t :: Tensor r v) ->
      let sr = sing :: Sing r
          cons' = sort $ con :| cons
          tr = TransCon (fmap fst cons') (fmap snd cons')
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
          tr = TransCov (fmap fst covs') (fmap snd covs')
      in withSingI sr $
         withSomeSing v $ \sv ->
         withSomeSing tr $ \str ->
         case sIsJust (sTranspositions sv str sr) %~ STrue of
           Proved Refl -> return $ T $ transposeMult sv str t
           Disproved _ -> throwError $ "Cannot transpose indices " ++ show v ++ " " ++ show tr ++ "!"
transposeMultT _ _ _ _ = throwError "Simultaneous transposition of contravariant and covariant indices not yet supported!"

-- |Relabelling of tensor indices. Throws an error if given relabellings are not allowed.
-- Wraps around 'relabel'.
relabelT :: MonadError String m =>
            VSpace Label Dimension -> [(Label,Label)] -> T v -> m (T v)
relabelT _ [] _ = throwError "Empty list for relabelling!"
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

-- |Hidden rank over which 'T' quantifies. Possible because of the @'SingI' r@ constraint.
rankT :: T v -> RankT
rankT o =
  case o of
    T (_ :: Tensor r v) ->
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

-- |Constructs a tensor from a rank and an assocs list. Throws an error for illegal ranks
-- or incompatible assocs lists.
fromListT :: MonadError String m => RankT -> [([Int], v)] -> m (T v)
fromListT r xs =
  withSomeSing r $ \sr ->
  withSingI sr $
  let sn = sLengthR sr
  in case sSane sr %~ STrue of
    Proved Refl -> T . fromList' sr <$> 
                   mapM (\(vec, val) -> do
                                         vec' <- vecFromList sn vec
                                         return (vec', val)) xs
    Disproved _ -> throwError $ "Insane tensor rank : " <> show r

-- |Lifts sanity check of ranks into the error monad.
saneRank :: (Ord s, Ord n, MonadError String m) => GRank s n -> m (GRank s n)
saneRank r
    | sane r = pure r
    | otherwise = throwError "Index lists must be strictly ascending."

-- |Contravariant rank from vector space label, vector space dimension,
-- and list of index labels. Throws an error for illegal ranks.
conRank :: (MonadError String m, Integral a, Ord s, Ord n, Num n) =>
           s -> a -> [s] -> m (GRank s n)
conRank _ _ [] = throwError "Generalized rank must have non-vanishing index list!"
conRank v d (i:is) = saneRank [(VSpace v (fromIntegral d), Con (i :| is))]

-- |Covariant rank from vector space label, vector space dimension,
-- and list of index labels. Throws an error for illegal ranks.
covRank :: (MonadError String m, Integral a, Ord s, Ord n, Num n) =>
           s -> a -> [s] -> m (GRank s n)
covRank _ _ [] = throwError "Generalized rank must have non-vanishing index list!"
covRank v d (i:is) = saneRank [(VSpace v (fromIntegral d), Cov (i :| is))]

-- |Mixed rank from vector space label, vector space dimension,
-- and lists of index labels. Throws an error for illegal ranks.
conCovRank :: (MonadError String m, Integral a, Ord s, Ord n, Num n) =>
              s -> a -> [s] -> [s] -> m (GRank s n)
conCovRank _ _ _ [] = throwError "Generalized rank must have non-vanishing index list!"
conCovRank _ _ [] _ = throwError "Generalized rank must have non-vanishing index list!"
conCovRank v d (i:is) (j:js) = saneRank [(VSpace v (fromIntegral d), ConCov (i :| is) (j :| js))]
