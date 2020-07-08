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

-----------------------------------------------------------------------------
{-|
Module      : Math.Tensor.Safe.Proofs
Description : Identities for functions on generalized tensor ranks.
Copyright   : (c) Nils Alex, 2020
License     : MIT
Maintainer  : nils.alex@fau.de
Stability   : experimental

Identities for functions on generalized tensor ranks.
-}
-----------------------------------------------------------------------------
module Math.Tensor.Safe.Proofs
  ( -- * Tails of sane ranks are sane
    saneTailRProof
  , singITailRProof
  , -- * Properties of merged ranks
    saneMergeRProof
  , proofMergeLT
  , proofMergeGT
  , proofMergeIxNotEQ
  , proofMergeIxLT
  , proofMergeIxGT
  , -- * Properties of contractions
    saneContractProof
  , singletonContractProof
  , contractTailDiffVProof
  , contractTailSameVNoConProof
  , contractTailSameVNoCovProof
  , contractTailSameVDiffIProof
  , contractTailSameVSameIProof
  ) where

import Math.Tensor.Safe.TH

import Data.Constraint
  ( Dict (Dict)
  , (:-) (Sub)
  )
import Unsafe.Coerce (unsafeCoerce)

import Data.Singletons.Prelude
  ( Sing, SingI
  , PEq ((==))
  , Symbol
  , Fst, Snd, Compare
  )

-- |The 'TailR' of a sane rank type is sane.
{-# INLINE saneTailRProof #-}
saneTailRProof :: forall (r :: Rank).Sing r -> (Sane r ~ 'True) :- (Sane (TailR r) ~ 'True)
saneTailRProof _ = Sub axiom
  where
    axiom :: Sane r ~ 'True => Dict (Sane (TailR r) ~ 'True)
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))

-- |If a rank type has a 'SingI' instance, the tail has a 'SingI' instance.
{-# INLINE singITailRProof #-}
singITailRProof :: forall (r :: Rank).Sing r -> SingI r :- SingI (TailR r)
singITailRProof _ = Sub axiom
  where
    axiom :: SingI r => Dict (SingI (TailR r))
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))

-- |Successfully merging two sane rank types (result is not @Nothing@) yields a sane rank type.
{-# INLINE saneMergeRProof #-}
saneMergeRProof :: forall (r :: Rank) (r' :: Rank) (r'' :: Rank).
                     Sing r -> Sing r' ->
                     (Sane r ~ 'True, Sane r' ~ 'True, MergeR r r' ~ 'Just r'') :- (Sane r'' ~ 'True)
saneMergeRProof _ _ = Sub axiom
  where
    axiom :: (Sane r ~ 'True, Sane r' ~ 'True, MergeR r r' ~ 'Just r'') =>
             Dict (Sane r'' ~ 'True)
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))

-- |If two rank types can be merged and the first 'VSpace' of the first rank type is less than
-- the first 'VSpace' of the second rank type, the 'TailR' of the merged rank type is equal to
-- the tail of the first rank type merged with the second rank type.
{-# INLINE proofMergeLT #-}
proofMergeLT :: forall (r :: Rank) (r' :: Rank) (r'' :: Rank).
                Sing r -> Sing r' ->
                (Sane r ~ 'True, Sane r' ~ 'True, MergeR r r' ~ 'Just r'',
                 Compare (Fst (HeadR r)) (Fst (HeadR r')) ~ 'LT)
                :- (MergeR (TailR r) r' ~ 'Just (TailR r''))
proofMergeLT _ _ = Sub axiom
  where
    axiom :: (Sane r ~ 'True, Sane r' ~ 'True, MergeR r r' ~ 'Just r'',
              Compare (Fst (HeadR r)) (Fst (HeadR r')) ~ 'LT)
             => Dict (MergeR (TailR r) r' ~ 'Just (TailR r''))
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))

-- |If two rank types can be merged and the first 'VSpace' of the first rank type coincides with
-- the first 'VSpace' of the second rank type, the first index of the first rank type cannot
-- equal the first index of the second rank type.
{-# INLINE proofMergeIxNotEQ #-}
proofMergeIxNotEQ :: forall (r :: Rank) (r' :: Rank) (r'' :: Rank).
                     Sing r -> Sing r' ->
                     (Sane r ~ 'True, Sane r' ~ 'True, MergeR r r' ~ 'Just r'',
                      Compare (Fst (HeadR r)) (Fst (HeadR r')) ~ 'EQ)
                     :- ((IxCompare (Snd (HeadR r)) (Snd (HeadR r')) == 'EQ) ~ 'False)
proofMergeIxNotEQ _ _ = Sub axiom
  where
    axiom :: (Sane r ~ 'True, Sane r' ~ 'True, MergeR r r' ~ 'Just r'',
             Compare (Fst (HeadR r)) (Fst (HeadR r')) ~ 'EQ)
             => Dict ((IxCompare (Snd (HeadR r)) (Snd (HeadR r')) == 'EQ) ~ 'False)
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))

-- |If two rank types can be merged and the first 'VSpace' of the first rank type coincides with
-- the first 'VSpace' of the second rank type and the first index of the first rank type compares
-- less than the first index of the second rank type, the 'TailR' of the merged rank type is equal
-- to the tail of the first rank type merged with the second rank type.
{-# INLINE proofMergeIxLT #-}
proofMergeIxLT :: forall (r :: Rank) (r' :: Rank) (r'' :: Rank).
                  Sing r -> Sing r' ->
                  (Sane r ~ 'True, Sane r' ~ 'True, MergeR r r' ~ 'Just r'',
                   Compare (Fst (HeadR r)) (Fst (HeadR r')) ~ 'EQ,
                   IxCompare (Snd (HeadR r)) (Snd (HeadR r')) ~ 'LT)
                  :- (MergeR (TailR r) r' ~ 'Just (TailR r''))
proofMergeIxLT _ _ = Sub axiom
  where
    axiom :: (Sane r ~ 'True, Sane r' ~ 'True, MergeR r r' ~ 'Just r'',
              Compare (Fst (HeadR r)) (Fst (HeadR r')) ~ 'EQ,
              IxCompare (Snd (HeadR r)) (Snd (HeadR r')) ~ 'LT)
             => Dict (MergeR (TailR r) r' ~ 'Just (TailR r''))
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))

-- |If two rank types can be merged and the first 'VSpace' of the first rank type is greater than
-- the first 'VSpace' of the second rank type, the 'TailR' of the merged rank type is equal to
-- the first rank type merged with the tail of the second rank type.
{-# INLINE proofMergeGT #-}
proofMergeGT :: forall (r :: Rank) (r' :: Rank) (r'' :: Rank).
                Sing r -> Sing r' ->
                (Sane r ~ 'True, Sane r' ~ 'True, MergeR r r' ~ 'Just r'',
                 Compare (Fst (HeadR r)) (Fst (HeadR r')) ~ 'GT)
                :- (MergeR r (TailR r') ~ 'Just (TailR r''))
proofMergeGT _ _ = Sub axiom
  where
    axiom :: (Sane r ~ 'True, Sane r' ~ 'True, MergeR r r' ~ 'Just r'',
              Compare (Fst (HeadR r)) (Fst (HeadR r')) ~ 'GT)
             => Dict (MergeR r (TailR r') ~ 'Just (TailR r''))
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))

-- |If two rank types can be merged and the first 'VSpace' of the first rank type coincides with
-- the first 'VSpace' of the second rank type and the first index of the first rank type compares
-- greater than the first index of the second rank type, the 'TailR' of the merged rank type is equal
-- to the first rank type merged with the tail of the second rank type.
{-# INLINE proofMergeIxGT #-}
proofMergeIxGT :: forall (r :: Rank) (r' :: Rank) (r'' :: Rank).
                  Sing r -> Sing r' ->
                  (Sane r ~ 'True, Sane r' ~ 'True, MergeR r r' ~ 'Just r'',
                   Compare (Fst (HeadR r)) (Fst (HeadR r')) ~ 'EQ,
                   IxCompare (Snd (HeadR r)) (Snd (HeadR r')) ~ 'GT)
                  :- (MergeR r (TailR r') ~ 'Just (TailR r''))
proofMergeIxGT _ _ = Sub axiom
  where
    axiom :: (Sane r ~ 'True, Sane r' ~ 'True, MergeR r r' ~ 'Just r'',
              Compare (Fst (HeadR r)) (Fst (HeadR r')) ~ 'EQ,
              IxCompare (Snd (HeadR r)) (Snd (HeadR r')) ~ 'GT)
             => Dict (MergeR r (TailR r') ~ 'Just (TailR r''))
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))

-- |If a rank type is sane, its contraction is also sane.
{-# INLINE saneContractProof #-}
saneContractProof :: forall (r :: Rank).Sing r -> (Sane r ~ 'True) :- (Sane (ContractR r) ~ 'True)
saneContractProof _ = Sub axiom
  where
    axiom :: Sane r ~ 'True => Dict (Sane (ContractR r) ~ 'True)
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))

-- |The contraction of the empty rank type is the empty rank type.
{-# INLINE singletonContractProof #-}
singletonContractProof :: forall (r :: Rank).
                          Sing r -> (TailR r ~ '[]) :- (ContractR r ~ r)
singletonContractProof _ = Sub axiom
  where
    axiom :: TailR r ~ '[] => Dict (ContractR r ~ r)
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))

-- |If the first two labels of a rank type cannot be contracted because they belong to
-- different 'VSpace's, the 'TailR' of the contracted rank type is equal to the contraction
-- of the 'TailR' of the rank type.
{-# INLINE contractTailDiffVProof #-}
contractTailDiffVProof :: forall (r :: Rank) (t :: Rank) (t' :: Rank).
                          Sing r ->
                          (t ~ TailR r, t' ~ TailR t, (Fst (HeadR r) == Fst (HeadR t)) ~ 'False)
                          :- (TailR (ContractR r) ~ ContractR t)
contractTailDiffVProof _ = Sub axiom
  where
    axiom :: (t ~ TailR r, t' ~ TailR t, (Fst (HeadR r) == Fst (HeadR t)) ~ 'False)
             => Dict (TailR (ContractR r) ~ ContractR t)
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))


-- |If the first two labels of a rank type cannot be contracted because the first label is
-- covariant, the 'TailR' of the contracted rank type is equal to the contraction
-- of the 'TailR' of the rank type.
{-# INLINE contractTailSameVNoConProof #-}
contractTailSameVNoConProof :: forall (r :: Rank) (t :: Rank) (t' :: Rank) (i :: Symbol).
                               Sing r ->
                               (t ~ TailR r, t' ~ TailR t, (Fst (HeadR r) == Fst (HeadR t)) ~ 'True,
                                Snd (HeadR r) ~ 'ICov i)
                               :- (TailR (ContractR r) ~ ContractR t)
contractTailSameVNoConProof _ = Sub axiom
  where
    axiom :: (t ~ TailR r, t' ~ TailR t, (Fst (HeadR r) == Fst (HeadR t)) ~ 'True,
              Snd (HeadR r) ~ 'ICov i)
             => Dict (TailR (ContractR r) ~ ContractR t)
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))

-- |If the first two labels of a rank type cannot be contracted because the second label is
-- covariant, the 'TailR' of the contracted rank type is equal to the contraction
-- of the 'TailR' of the rank type.
{-# INLINE contractTailSameVNoCovProof #-}
contractTailSameVNoCovProof :: forall (r :: Rank) (t :: Rank) (t' :: Rank) (i :: Symbol).
                               Sing r ->
                               (t ~ TailR r, t' ~ TailR t, (Fst (HeadR r) == Fst (HeadR t)) ~ 'True,
                                Snd (HeadR t) ~ 'ICon i)
                               :- (TailR (ContractR r) ~ ContractR t)
contractTailSameVNoCovProof _ = Sub axiom
  where
    axiom :: (t ~ TailR r, t' ~ TailR t, (Fst (HeadR r) == Fst (HeadR t)) ~ 'True,
              Snd (HeadR t) ~ 'ICon i)
             => Dict (TailR (ContractR r) ~ ContractR t)
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))

-- |If the first two labels of a rank type cannot be contracted because they differ,
-- the 'TailR' of the contracted rank type is equal to the contraction of the 'TailR' of the rank type.
{-# INLINE contractTailSameVDiffIProof #-}
contractTailSameVDiffIProof :: forall (r :: Rank) (t :: Rank) (t' :: Rank) (i :: Symbol) (j :: Symbol).
                               Sing r ->
                               (t ~ TailR r, t' ~ TailR t, (Fst (HeadR r) == Fst (HeadR t)) ~ 'True,
                                Snd (HeadR r) ~ 'ICon i, Snd (HeadR t) ~ 'ICov j, (i == j) ~ 'False)
                               :- (TailR (ContractR r) ~ ContractR t)
contractTailSameVDiffIProof _ = Sub axiom
  where
    axiom :: (t ~ TailR r, t' ~ TailR t, (Fst (HeadR r) == Fst (HeadR t)) ~ 'True,
              Snd (HeadR r) ~ 'ICon i, Snd (HeadR t) ~ 'ICov j, (i == j) ~ 'False)
             => Dict (TailR (ContractR r) ~ ContractR t)
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))

-- |If the first two labels of a rank type can be contracted, the contracted rank type is equal
-- to the contraction of the tail.
{-# INLINE contractTailSameVSameIProof #-}
contractTailSameVSameIProof :: forall (r :: Rank) (t :: Rank) (t' :: Rank) (i :: Symbol) (j :: Symbol).
                               Sing r ->
                               (t ~ TailR r, t' ~ TailR t, (Fst (HeadR r) == Fst (HeadR t)) ~ 'True,
                                Snd (HeadR r) ~ 'ICon i, Snd (HeadR t) ~ 'ICov j, (i == j) ~ 'True)
                               :- (ContractR t' ~ ContractR r)
contractTailSameVSameIProof _ = Sub axiom
  where
    axiom :: (t ~ TailR r, t' ~ TailR t, (Fst (HeadR r) == Fst (HeadR t)) ~ 'True,
              Snd (HeadR r) ~ 'ICon i, Snd (HeadR t) ~ 'ICov j, (i == j) ~ 'True)
             => Dict (ContractR t' ~ ContractR r)
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))
