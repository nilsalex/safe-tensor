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
Module      : Math.Tensor.SparseTensor.Ansaetze.TH
Description : Template Haskell for sparse-tensor ansaetze.
Copyright   : (c) Nils Alex, 2020
License     : MIT
Maintainer  : nils.alex@fau.de
Stability   : experimental

Template Haskell for sparse-tensor ansaetze.
-}
-----------------------------------------------------------------------------
module Math.Tensor.SparseTensor.Ansaetze.TH where

import Math.Tensor.Safe.TH

import Data.Singletons.Prelude
import Data.Singletons.Prelude.List.NonEmpty hiding (sLength)
import Data.Singletons.TH
import Data.Singletons.TypeLits

import Data.List.NonEmpty (NonEmpty((:|)),sort)

$(singletons [d|

  ans4Rank :: Symbol -> Symbol -> Rank
  ans4Rank vid a = [(VSpace (vid <> "Area") 21, Cov (a :| []))]

  ans6Rank :: Symbol -> Symbol -> Symbol -> Rank
  ans6Rank vid a i = [(VSpace (vid <> "Area") 21, Cov (a :| [])), (VSpace (vid <> "Sym2") 10, Con (i :| []))]

  ans8Rank :: Symbol -> Symbol -> Symbol -> Maybe Rank
  ans8Rank vid a b =
    case a `compare` b of
      LT -> Just [(VSpace (vid <> "Area") (21 :: Nat), Cov (a :| [b]))]
      EQ -> Nothing
      GT -> Just [(VSpace (vid <> "Area") (21 :: Nat), Cov (b :| [a]))]

  ans10_1Rank :: Symbol -> Symbol -> Symbol -> Symbol -> Maybe Rank
  ans10_1Rank vid a b i =
    case a `compare` b of
      LT -> Just [(VSpace (vid <> "Area") (21 :: Nat), Cov (a :| [b])), (VSpace (vid <> "Sym2") (10 :: Nat), Con (i :| []))]
      EQ -> Nothing
      GT -> Nothing

  ans10_2Rank :: Symbol -> Symbol -> Symbol -> Symbol -> Symbol -> Maybe Rank
  ans10_2Rank vid a b p q =
    case a `compare` b of
      LT ->
        case p `compare` q of
          LT -> Just [(VSpace vid (4 :: Nat), Con (p :| [q])), (VSpace (vid <> "Area") (21 :: Nat), Cov (a :| [b]))]
          EQ -> Nothing
          GT -> Nothing
      EQ -> Nothing
      GT -> Nothing

  ans12Rank :: Symbol -> Symbol -> Symbol -> Symbol -> Maybe Rank
  ans12Rank vid a b c =
    case sort (a :| [b,c]) of
      a' :| [b',c'] ->
        case a' == b' || b' == c' of
          True -> Nothing
          False -> Just [(VSpace (vid <> "Area") (21 :: Nat), Cov (a' :| [b',c']))]

  ans14_1Rank :: Symbol -> Symbol -> Symbol -> Symbol -> Symbol -> Maybe Rank
  ans14_1Rank vid a b c i =
    case a `compare` b of
      LT ->
        case b `compare` c of
          LT -> Just [(VSpace (vid <> "Area") (21 :: Nat), Cov (a :| [b,c])), (VSpace (vid <> "Sym2") (10 :: Nat), Con (i :| []))]
          EQ -> Nothing
          GT -> Nothing
      EQ -> Nothing
      GT -> Nothing

  ans14_2Rank :: Symbol -> Symbol -> Symbol -> Symbol -> Symbol -> Symbol -> Maybe Rank
  ans14_2Rank vid a b c p q =
    case a `compare` b of
      LT ->
        case b `compare` c of
          LT ->
            case p `compare` q of
              LT -> Just [(VSpace vid 4, Con (p :| [q])), (VSpace (vid <> "Area") (21 :: Nat), Cov (a :| [b,c]))]
              EQ -> Nothing
              GT -> Nothing
          EQ -> Nothing
          GT -> Nothing
      EQ -> Nothing
      GT -> Nothing

  |])
