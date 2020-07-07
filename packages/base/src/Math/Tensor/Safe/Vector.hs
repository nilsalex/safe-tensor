{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingStrategies #-}

{-# OPTIONS_GHC -Wall -Werror #-}

-----------------------------------------------------------------------------
{-|
Module      : Math.Tensor.Safe.Vector
Description : Length-typed vector.
Copyright   : (c) Nils Alex, 2020
License     : MIT
Maintainer  : nils.alex@fau.de
Stability   : experimental

Length-typed vector.
-}
-----------------------------------------------------------------------------
module Math.Tensor.Safe.Vector
  ( Vec(..)
  , vecFromListUnsafe
  ) where

import Math.Tensor.Safe.TH

import Data.Kind (Type)
import Data.Singletons (Sing)

data Vec :: N -> Type -> Type where
    VNil :: Vec 'Z a
    VCons :: a -> Vec n a -> Vec ('S n) a

deriving stock instance Show a => Show (Vec n a)

instance Eq a => Eq (Vec n a) where
  VNil           == VNil           = True
  (x `VCons` xs) == (y `VCons` ys) = x == y && xs == ys

instance Ord a => Ord (Vec n a) where
  VNil `compare` VNil = EQ
  (x `VCons` xs) `compare` (y `VCons` ys) =
    case x `compare` y of
      LT -> LT
      EQ -> xs `compare` ys
      GT -> GT

vecFromListUnsafe :: forall (n :: N) a.
                     Sing n -> [a] -> Vec n a
vecFromListUnsafe SZ [] = VNil
vecFromListUnsafe (SS sn) (x:xs) =
    let xs' = vecFromListUnsafe sn xs
    in  x `VCons` xs'
vecFromListUnsafe _ _ = error "cannot reconstruct vector from list: incompatible lengths"
