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
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverloadedStrings #-}

-----------------------------------------------------------------------------
{-|
Module      : Math.Tensor.Basic.Epsilon
Description : Definitions of epsilon tensor densities.
Copyright   : (c) Nils Alex, 2020
License     : MIT
Maintainer  : nils.alex@fau.de
Stability   : experimental

Definitions of covariant and contravariant epsilon tensor densities
like \(\epsilon_{abc}\).
-}
-----------------------------------------------------------------------------
module Math.Tensor.Basic.Epsilon
  ( -- * Epsilon tensor densities
    epsilon'
  , someEpsilon
  , epsilonInv'
  , someEpsilonInv
  , -- * Internals
    permSign
  ) where

import Math.Tensor
import Math.Tensor.Safe
import Math.Tensor.Safe.TH
import Math.Tensor.Basic.TH

import Data.Singletons
import Data.Singletons.Prelude
import Data.Singletons.Decide
import Data.Singletons.TypeLits

import Data.List (sort,permutations)
import qualified Data.List.NonEmpty as NE (NonEmpty(..),sort)

import Control.Monad.Except

-- |Sign of a permutation:
--
-- @
--   permSign [1,2,3] = 1
--   permSign [2,1,3] = -1
-- @
permSign :: (Num v, Ord a) => [a] -> v
permSign (x:xs)
    | even (length defects) = permSign xs
    | odd (length defects)  = (-1) * permSign xs
  where
    defects = filter (<x) xs
permSign _ = 1

-- |Totally antisymmetric covariant tensor density of weight -1
-- such that
--
-- \[ \epsilon_{12\dots n} = 1. \]
--
-- Vector space label, vector space dimension and index labels
-- are passed as singletons.
epsilon' :: forall (id :: Symbol) (n :: Nat) (is :: NE.NonEmpty Symbol) (r :: Rank) v.
              (
               KnownNat n,
               Num v,
               EpsilonRank id n is ~ 'Just r,
               SingI r
              ) =>
              Sing id -> Sing n -> Sing is -> Tensor r v
epsilon' sid sn sis =
    case sLengthR sr %~ sn' of
      Proved Refl ->
        case sSane sr %~ STrue of
          Proved Refl -> fromList xs
  where
    sr = sing :: Sing r
    sn' = sFromNat sn
    n = fromSing sn
    perms = sort $ permutations $ take (fromIntegral n) [(0 :: Int)..]
    xs = fmap (\p -> (vecFromListUnsafe sn' p, fromIntegral (permSign p) :: v)) perms

-- |Totally antisymmetric contravariant tensor density of weight +1
-- such that
--
-- \[ \epsilon^{12\dots n} = 1. \]
--
-- Vector space label, vector space dimension and index labels
-- are passed as singletons.
epsilonInv' :: forall (id :: Symbol) (n :: Nat) (is :: NE.NonEmpty Symbol) (r :: Rank) v.
              (
               KnownNat n,
               Num v,
               EpsilonInvRank id n is ~ 'Just r,
               SingI r
              ) =>
              Sing id -> Sing n -> Sing is -> Tensor r v
epsilonInv' sid sn sis =
    case sLengthR sr %~ sn' of
      Proved Refl ->
        case sSane sr %~ STrue of
          Proved Refl -> fromList xs
  where
    sr = sing :: Sing r
    sn' = sFromNat sn
    n = fromSing sn
    perms = sort $ permutations $ take (fromIntegral n) [(0 :: Int)..]
    xs = fmap (\p -> (vecFromListUnsafe sn' p, fromIntegral (permSign p) :: v)) perms

-- |Totally antisymmetric covariant tensor density of weight -1
-- such that
--
-- \[ \epsilon_{12\dots n} = 1. \]
--
-- Vector space label, vector space dimension and index labels
-- are passed as values. Result is existentially quantified.
someEpsilon :: forall v m.(Num v, MonadError String m) =>
               Demote Symbol -> Demote Nat -> [Demote Symbol] ->
               m (T v)
someEpsilon _ _ [] = throwError "Empty index list!"
someEpsilon vid vdim (i:is) =
  let sign = permSign (i:is) :: v
  in withSomeSing vid $ \svid ->
     withSomeSing vdim $ \svdim ->
     withSomeSing (NE.sort (i NE.:| is)) $ \sis ->
     withKnownNat svdim $
     case sEpsilonRank svid svdim sis of
       SJust sr ->
         withSingI sr $
         return $ T $ (* sign) <$> epsilon' svid svdim sis
       SNothing -> throwError $ "Illegal index list " ++ show (i:is) ++ "!"

-- |Totally antisymmetric contravariant tensor density of weight +1
-- such that
--
-- \[ \epsilon^{12\dots n} = 1. \]
--
-- Vector space label, vector space dimension and index labels
-- are passed as values. Result is existentially quantified.
someEpsilonInv :: forall v m.(Num v, MonadError String m) =>
                  Demote Symbol -> Demote Nat -> [Demote Symbol] ->
                  m (T v)
someEpsilonInv _ _ [] = throwError "Empty index list!"
someEpsilonInv vid vdim (i:is) =
  let sign = permSign (i:is) :: v
  in withSomeSing vid $ \svid ->
     withSomeSing vdim $ \svdim ->
     withSomeSing (NE.sort (i NE.:| is)) $ \sis ->
     withKnownNat svdim $
     case sEpsilonInvRank svid svdim sis of
       SJust sr ->
         withSingI sr $
         return $ T $ (* sign) <$> epsilonInv' svid svdim sis
       SNothing -> throwError $ "Illegal index list " ++ show (i:is) ++ "!"
