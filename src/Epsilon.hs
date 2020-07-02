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
import qualified Data.List.NonEmpty as NE (NonEmpty(..),sort)

import Control.Monad.Except

permSign :: Num v => Ord a => [a] -> v
permSign (x:xs)
    | even (length defects) = permSign xs
    | odd (length defects)  = (-1) * permSign xs
  where
    defects = filter (<x) xs
permSign _ = 1

epsilon' :: forall (id :: Symbol) (n :: Nat) (is :: NE.NonEmpty Symbol) (l :: ILists) v.
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
    xs = fmap (\p -> (vecFromListUnsafe sn' p, fromIntegral (permSign p) :: v)) perms

epsilonInv' :: forall (id :: Symbol) (n :: Nat) (is :: NE.NonEmpty Symbol) (l :: ILists) v.
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
    xs = fmap (\p -> (vecFromListUnsafe sn' p, fromIntegral (permSign p) :: v)) perms

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
     case sEpsilonILists svid svdim sis of
       SJust sl ->
         withSingI sl $
         return $ T $ (* sign) <$> epsilon' svid svdim sis
       SNothing -> throwError $ "Illegal index list " ++ show (i:is) ++ "!"

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
     case sEpsilonInvILists svid svdim sis of
       SJust sl ->
         withSingI sl $
         return $ T $ (* sign) <$> epsilonInv' svid svdim sis
       SNothing -> throwError $ "Illegal index list " ++ show (i:is) ++ "!"

