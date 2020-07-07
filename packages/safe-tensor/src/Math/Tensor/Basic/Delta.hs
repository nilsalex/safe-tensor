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

{-# OPTIONS_GHC
    -Wall
    -Werror
    -Weverything
    -Wno-prepositive-qualified-module
    -Wno-missing-deriving-strategies
    -Wno-implicit-prelude
    -Wno-missing-import-lists
    -Wno-missing-safe-haskell-mode
    -Wno-unsafe
    -Wno-incomplete-patterns
    #-}

-----------------------------------------------------------------------------
{-|
Module      : Math.Tensor.Basic.Delta
Description : Definitions of Kronecker deltas.
Copyright   : (c) Nils Alex, 2020
License     : MIT
Maintainer  : nils.alex@fau.de
Stability   : experimental

Definitions of Kronecker deltas \(\delta^{a}_{\hphantom ab}\)
(identity automorphisms) for arbitrary vector spaces.
-}
-----------------------------------------------------------------------------
module Math.Tensor.Basic.Delta
  ( -- * Kronecker delta
    delta
  , delta'
  , someDelta
  ) where

import Math.Tensor
import Math.Tensor.Safe
import Math.Tensor.Safe.TH
import Math.Tensor.Basic.TH

import Data.Singletons
  ( Sing
  , SingI (sing)
  , Demote
  , withSomeSing
  )
import Data.Singletons.Prelude
  ( SList (SNil)
  , SBool (STrue)
  )
import Data.Singletons.Decide
  ( (:~:) (Refl)
  , Decision (Proved)
  , (%~)
  )
import Data.Singletons.TypeLits
  ( Symbol
  , Nat
  , KnownNat
  , withKnownNat
  , natVal
  , withKnownSymbol
  )

import Data.List.NonEmpty (NonEmpty ((:|)))

-- |The Kronecker delta \(\delta^a_{\hphantom ab} \) for a given
-- @'VSpace' id n@ with contravariant
-- index label @a@ and covariant index label @b@. Labels and dimension
-- are passed explicitly as singletons.
delta' :: forall (id :: Symbol) (n :: Nat) (a :: Symbol) (b :: Symbol) (r :: Rank) v.
          (
           KnownNat n,
           Num v,
           '[ '( 'VSpace id n, 'ConCov (a ':| '[]) (b ':| '[])) ] ~ r,
           Tail' (Tail' r) ~ '[],
           Sane (Tail' r) ~ 'True
          ) =>
          Sing id -> Sing n -> Sing a -> Sing b ->
          Tensor r v
delta' _ _ _ _ = delta

-- |The Kronecker delta \(\delta^a_{\hphantom ab} \) for a given
-- @'VSpace' id n@ with contravariant
-- index label @a@ and covariant index label @b@.
delta :: forall (id :: Symbol) (n :: Nat) (a :: Symbol) (b :: Symbol) (r :: Rank) v.
         (
          '[ '( 'VSpace id n, 'ConCov (a ':| '[]) (b ':| '[]))] ~ r,
          Tail' (Tail' r) ~ '[],
          Sane (Tail' r) ~ 'True,
          SingI n,
          Num v
         ) => Tensor r v
delta = case (sing :: Sing n) of
          sn -> let x = fromIntegral $ withKnownNat sn $ natVal sn
                in Tensor (f x)
  where
    f :: Int -> [(Int, Tensor (Tail' r) v)]
    f x = map (\i -> (i, Tensor [(i, Scalar 1)])) [0..x - 1]

-- |The Kronecker delta \(\delta^a_{\hphantom ab} \) for a given
-- @'VSpace' id n@ with contravariant
-- index label @a@ and covariant index label @b@. Labels and dimension
-- are passed as values. Result is existentially quantified.
someDelta :: Num v =>
             Demote Symbol -> Demote Nat -> Demote Symbol -> Demote Symbol ->
             T v
someDelta vid vdim a b =
  withSomeSing vid $ \svid ->
  withSomeSing vdim $ \svdim ->
  withSomeSing a $ \sa ->
  withSomeSing b $ \sb ->
  withKnownNat svdim $
  withKnownSymbol svid $
  withKnownSymbol sa $
  withKnownSymbol sb $
  let sl = sDeltaRank svid svdim sa sb
  in  case sTail' (sTail' sl) of
        SNil -> case sSane (sTail' sl) %~ STrue of
                  Proved Refl -> T $ delta' svid svdim sa sb
