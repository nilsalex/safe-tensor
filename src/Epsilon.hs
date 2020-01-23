{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE OverloadedStrings #-}

module Epsilon where

import TH
import Safe
import Tensor

import Data.Singletons
import Data.Singletons.Prelude
import Data.Singletons.Decide
import Data.Singletons.TypeLits

import Data.List (sort,permutations)
import Data.List.NonEmpty (NonEmpty(..))

import Control.Monad.Except

permSign [] = 1
permSign (_:[]) = 1
permSign (x:xs)
    | even (length defects) = permSign xs
    | odd (length defects)  = (-1) * permSign xs
  where
    defects = filter (<x) xs

epsilon' :: forall (id :: Symbol) (n :: Nat) (is :: NonEmpty Symbol) (l :: ILists) v.
              (
               KnownNat n,
               Num v,
               EpsilonILists id n is ~ 'Just l,
               SingI l
              ) =>
              Sing id -> Sing n -> Sing is -> Tensor l v
epsilon' sid sn sis =
    case sLengthILs sl %~ sn' of
      Proved Refl ->
        case sSane sl %~ STrue of
          Proved Refl -> fromList xs
  where
    sl = sing :: Sing l
    sn' = sFromNat sn
    n = fromSing sn
    perms = sort $ permutations $ take (fromIntegral n) [(0 :: Int)..]
    xs = fmap (\p -> (vecFromListUnsafe sn' p, (fromIntegral (permSign p) :: v))) perms

epsilonInv' :: forall (id :: Symbol) (n :: Nat) (is :: NonEmpty Symbol) (l :: ILists) v.
              (
               KnownNat n,
               Num v,
               EpsilonInvILists id n is ~ 'Just l,
               SingI l
              ) =>
              Sing id -> Sing n -> Sing is -> Tensor l v
epsilonInv' sid sn sis =
    case sLengthILs sl %~ sn' of
      Proved Refl ->
        case sSane sl %~ STrue of
          Proved Refl -> fromList xs
  where
    sl = sing :: Sing l
    sn' = sFromNat sn
    n = fromSing sn
    perms = sort $ permutations $ take (fromIntegral n) [(0 :: Int)..]
    xs = fmap (\p -> (vecFromListUnsafe sn' p, (fromIntegral (permSign p) :: v))) perms

someEpsilon :: (Num v, MonadError String m) =>
                  Demote Symbol -> Demote Nat -> [Demote Symbol] ->
                  m (T v)
someEpsilon _ _ [] = throwError "Empty index list!"
someEpsilon vid vdim (i:is) =
  withSomeSing vid $ \svid ->
  withSomeSing vdim $ \svdim ->
  withSomeSing (i :| is) $ \sis ->
  withKnownNat svdim $
  case sEpsilonILists svid svdim sis of
    SJust sl ->
      withSingI sl $
      return $ T $ epsilon' svid svdim sis
    SNothing -> throwError $ "Illegal index list " ++ show (i:is) ++ "!"

someEpsilonInv :: (Num v, MonadError String m) =>
                  Demote Symbol -> Demote Nat -> [Demote Symbol] ->
                  m (T v)
someEpsilonInv _ _ [] = throwError "Empty index list!"
someEpsilonInv vid vdim (i:is) =
  withSomeSing vid $ \svid ->
  withSomeSing vdim $ \svdim ->
  withSomeSing (i :| is) $ \sis ->
  withKnownNat svdim $
  case sEpsilonInvILists svid svdim sis of
    SJust sl ->
      withSingI sl $
      return $ T $ epsilonInv' svid svdim sis
    SNothing -> throwError $ "Illegal index list " ++ show (i:is) ++ "!"

