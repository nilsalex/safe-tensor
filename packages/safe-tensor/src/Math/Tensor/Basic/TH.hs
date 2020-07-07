{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
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

{-# LANGUAGE CPP #-}
#if MIN_VERSION_base(4,14,0)
{-# LANGUAGE StandaloneKindSignatures #-}
#endif

-----------------------------------------------------------------------------
{-|
Module      : Math.Tensor.Basic.TH
Description : Template Haskell for Math.Tensor.Basic
Copyright   : (c) Nils Alex, 2020
License     : MIT
Maintainer  : nils.alex@fau.de
Stability   : experimental

Template Haskell for 'Math.Tensor.Basic'.
-}
-----------------------------------------------------------------------------
module Math.Tensor.Basic.TH where

import Math.Tensor.Safe.TH

import Data.Singletons.Prelude
import Data.Singletons.Prelude.Enum
import Data.Singletons.Prelude.List.NonEmpty hiding (sLength)
import Data.Singletons.TH
import Data.Singletons.TypeLits

import Data.List.NonEmpty (NonEmpty((:|)))

$(singletons [d|

  -- #############
  -- ### delta ###
  -- #############
  deltaRank :: Symbol -> Nat -> Symbol -> Symbol -> Rank
  deltaRank vid vdim a b = [(VSpace vid vdim, ConCov (a :| []) (b :| []))]

  -- ###############
  -- ### epsilon ###
  -- ###############
  epsilonRank :: Symbol -> Nat -> NonEmpty Symbol -> Maybe Rank
  epsilonRank vid vdim is =
      case isLengthNE is vdim of
        True  ->
          case isAscendingNE is of
            True -> Just [(VSpace vid vdim, Cov is)]
            False -> Nothing
        False -> Nothing

  epsilonInvRank :: Symbol -> Nat -> NonEmpty Symbol -> Maybe Rank
  epsilonInvRank vid vdim is =
      case isLengthNE is vdim of
        True  ->
          case isAscendingNE is of
            True -> Just [(VSpace vid vdim, Con is)]
            False -> Nothing
        False -> Nothing

  -- ############
  -- ### sym2 ###
  -- ############
  sym2Dim :: Nat -> Nat
  sym2Dim = go 0
    where
      go :: Nat -> Nat -> Nat
      go acc n = case n == 0 of
                   True  -> acc
                   False -> go (acc + n) (pred n)

  injSym2ConRank :: Symbol -> Nat -> Symbol -> Symbol -> Symbol -> Maybe Rank
  injSym2ConRank vid vdim a b i =
      let r = [(VSpace vid vdim, Con (a :| [b])), (VSpace (vid <> "Sym2") (sym2Dim vdim), Cov (i :| []))]
      in case sane r of
           True -> Just r
           False -> Nothing

  injSym2CovRank :: Symbol -> Nat -> Symbol -> Symbol -> Symbol -> Maybe Rank
  injSym2CovRank vid vdim a b i =
      let r = [(VSpace vid vdim, Cov (a :| [b])), (VSpace (vid <> "Sym2") (sym2Dim vdim), Con (i :| []))]
      in case sane r of
           True -> Just r
           False -> Nothing

  surjSym2ConRank :: Symbol -> Nat -> Symbol -> Symbol -> Symbol -> Maybe Rank
  surjSym2ConRank = injSym2CovRank

  surjSym2CovRank :: Symbol -> Nat -> Symbol -> Symbol -> Symbol -> Maybe Rank
  surjSym2CovRank = injSym2ConRank

  -- ############
  -- ### Area ###
  -- ############
  injAreaConRank :: Symbol -> Symbol -> Symbol -> Symbol -> Symbol -> Symbol -> Maybe Rank
  injAreaConRank vid a b c d i =
    let r = [(VSpace vid (4 :: Nat), Con (a :| [b,c,d])), (VSpace (vid <> "Area") (21 :: Nat), Cov (i :| []))]
    in case sane r of
         True -> Just r
         False -> Nothing

  injAreaCovRank :: Symbol -> Symbol -> Symbol -> Symbol -> Symbol -> Symbol -> Maybe Rank
  injAreaCovRank vid a b c d i =
    let r = [(VSpace vid (4 :: Nat), Cov (a :| [b,c,d])), (VSpace (vid <> "Area") (21 :: Nat), Con (i :| []))]
    in case sane r of
         True -> Just r
         False -> Nothing

  surjAreaConRank :: Symbol -> Symbol -> Symbol -> Symbol -> Symbol -> Symbol -> Maybe Rank
  surjAreaConRank vid a b c d i =
    let r = [(VSpace vid (4 :: Nat), Cov (a :| [b,c,d])), (VSpace (vid <> "Area") (21 :: Nat), Con (i :| []))]
    in case sane r of
         True -> Just r
         False -> Nothing

  surjAreaCovRank :: Symbol -> Symbol -> Symbol -> Symbol -> Symbol -> Symbol -> Maybe Rank
  surjAreaCovRank vid a b c d i =
    let r = [(VSpace vid (4 :: Nat), Con (a :| [b,c,d])), (VSpace (vid <> "Area") (21 :: Nat), Cov (i :| []))]
    in case sane r of
         True -> Just r
         False -> Nothing

  |])
