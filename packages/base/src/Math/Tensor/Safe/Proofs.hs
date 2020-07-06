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
    saneTail'Proof
  , singITail'Proof
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
import Unsafe.Coerce (unsafeCoerce)

import Data.Singletons
import Data.Singletons.Prelude

-- |The 'Tail'' of a sane rank type is sane.
{-# INLINE saneTail'Proof #-}
saneTail'Proof :: forall (r :: Rank).Sing r -> (Sane r ~ 'True) :- (Sane (Tail' r) ~ 'True)
saneTail'Proof _ = Sub axiom
  where
    axiom :: Sane r ~ 'True => Dict (Sane (Tail' r) ~ 'True)
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))

-- |If a rank type has a 'SingI' instance, the tail has a 'SingI' instance.
{-# INLINE singITail'Proof #-}
singITail'Proof :: forall (r :: Rank).Sing r -> SingI r :- SingI (Tail' r)
singITail'Proof _ = Sub axiom
  where
    axiom :: SingI r => Dict (SingI (Tail' r))
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
-- the first 'VSpace' of the second rank type, the 'Tail'' of the merged rank type is equal to
-- the tail of the first rank type merged with the second rank type.
{-# INLINE proofMergeLT #-}
proofMergeLT :: forall (r :: Rank) (r' :: Rank) (r'' :: Rank).
                Sing r -> Sing r' ->
                (Sane r ~ 'True, Sane r' ~ 'True, MergeR r r' ~ 'Just r'',
                 Compare (Fst (Head' r)) (Fst (Head' r')) ~ 'LT)
                :- (MergeR (Tail' r) r' ~ Just (Tail' r''))
proofMergeLT _ _ = Sub axiom
  where
    axiom :: (Sane r ~ 'True, Sane r' ~ 'True, MergeR r r' ~ 'Just r'',
              Compare (Fst (Head' r)) (Fst (Head' r')) ~ 'LT)
             => Dict (MergeR (Tail' r) r' ~ 'Just (Tail' r''))
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))

-- |If two rank types can be merged and the first 'VSpace' of the first rank type coincides with
-- the first 'VSpace' of the second rank type, the first index of the first rank type cannot
-- equal the first index of the second rank type.
{-# INLINE proofMergeIxNotEQ #-}
proofMergeIxNotEQ :: forall (r :: Rank) (r' :: Rank) (r'' :: Rank).
                     Sing r -> Sing r' ->
                     (Sane r ~ 'True, Sane r' ~ 'True, MergeR r r' ~ 'Just r'',
                      Compare (Fst (Head' r)) (Fst (Head' r')) ~ 'EQ)
                     :- ((IxCompare (Snd (Head' r)) (Snd (Head' r')) == 'EQ) ~ 'False)
proofMergeIxNotEQ _ _ = Sub axiom
  where
    axiom :: (Sane r ~ 'True, Sane r' ~ 'True, MergeR r r' ~ 'Just r'',
             Compare (Fst (Head' r)) (Fst (Head' r')) ~ 'EQ)
             => Dict ((IxCompare (Snd (Head' r)) (Snd (Head' r')) == 'EQ) ~ 'False)
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))

-- |If two rank types can be merged and the first 'VSpace' of the first rank type coincides with
-- the first 'VSpace' of the second rank type and the first index of the first rank type compares
-- less than the first index of the second rank type, the 'Tail'' of the merged rank type is equal
-- to the tail of the first rank type merged with the second rank type.
{-# INLINE proofMergeIxLT #-}
proofMergeIxLT :: forall (r :: Rank) (r' :: Rank) (r'' :: Rank).
                  Sing r -> Sing r' ->
                  (Sane r ~ 'True, Sane r' ~ 'True, MergeR r r' ~ 'Just r'',
                   Compare (Fst (Head' r)) (Fst (Head' r')) ~ 'EQ,
                   IxCompare (Snd (Head' r)) (Snd (Head' r')) ~ 'LT)
                  :- (MergeR (Tail' r) r' ~ Just (Tail' r''))
proofMergeIxLT _ _ = Sub axiom
  where
    axiom :: (Sane r ~ 'True, Sane r' ~ 'True, MergeR r r' ~ 'Just r'',
              Compare (Fst (Head' r)) (Fst (Head' r')) ~ 'EQ,
              IxCompare (Snd (Head' r)) (Snd (Head' r')) ~ LT)
             => Dict (MergeR (Tail' r) r' ~ 'Just (Tail' r''))
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))

-- |If two rank types can be merged and the first 'VSpace' of the first rank type is greater than
-- the first 'VSpace' of the second rank type, the 'Tail'' of the merged rank type is equal to
-- the first rank type merged with the tail of the second rank type.
{-# INLINE proofMergeGT #-}
proofMergeGT :: forall (r :: Rank) (r' :: Rank) (r'' :: Rank).
                Sing r -> Sing r' ->
                (Sane r ~ 'True, Sane r' ~ 'True, MergeR r r' ~ 'Just r'',
                 Compare (Fst (Head' r)) (Fst (Head' r')) ~ 'GT)
                :- (MergeR r (Tail' r') ~ Just (Tail' r''))
proofMergeGT _ _ = Sub axiom
  where
    axiom :: (Sane r ~ 'True, Sane r' ~ 'True, MergeR r r' ~ 'Just r'',
              Compare (Fst (Head' r)) (Fst (Head' r')) ~ 'GT)
             => Dict (MergeR r (Tail' r') ~ 'Just (Tail' r''))
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))

-- |If two rank types can be merged and the first 'VSpace' of the first rank type coincides with
-- the first 'VSpace' of the second rank type and the first index of the first rank type compares
-- greater than the first index of the second rank type, the 'Tail'' of the merged rank type is equal
-- to the first rank type merged with the tail of the second rank type.
{-# INLINE proofMergeIxGT #-}
proofMergeIxGT :: forall (r :: Rank) (r' :: Rank) (r'' :: Rank).
                  Sing r -> Sing r' ->
                  (Sane r ~ 'True, Sane r' ~ 'True, MergeR r r' ~ 'Just r'',
                   Compare (Fst (Head' r)) (Fst (Head' r')) ~ 'EQ,
                   IxCompare (Snd (Head' r)) (Snd (Head' r')) ~ 'GT)
                  :- (MergeR r (Tail' r') ~ Just (Tail' r''))
proofMergeIxGT _ _ = Sub axiom
  where
    axiom :: (Sane r ~ 'True, Sane r' ~ 'True, MergeR r r' ~ 'Just r'',
              Compare (Fst (Head' r)) (Fst (Head' r')) ~ 'EQ,
              IxCompare (Snd (Head' r)) (Snd (Head' r')) ~ GT)
             => Dict (MergeR r (Tail' r') ~ 'Just (Tail' r''))
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
                          Sing r -> (Tail' r ~ '[]) :- (ContractR r ~ r)
singletonContractProof _ = Sub axiom
  where
    axiom :: Tail' r ~ '[] => Dict (ContractR r ~ r)
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))

-- |If the first two labels of a rank type cannot be contracted because they belong to
-- different 'VSpace's, the 'Tail'' of the contracted rank type is equal to the contraction
-- of the 'Tail'' of the rank type.
{-# INLINE contractTailDiffVProof #-}
contractTailDiffVProof :: forall (r :: Rank) (t :: Rank) (t' :: Rank).
                          Sing r ->
                          (t ~ Tail' r, t' ~ Tail' t, (Fst (Head' r) == Fst (Head' t)) ~ 'False)
                          :- (Tail' (ContractR r) ~ ContractR t)
contractTailDiffVProof _ = Sub axiom
  where
    axiom :: (t ~ Tail' r, t' ~ Tail' t, (Fst (Head' r) == Fst (Head' t)) ~ 'False)
             => Dict (Tail' (ContractR r) ~ ContractR t)
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))


-- |If the first two labels of a rank type cannot be contracted because the first label is
-- covariant, the 'Tail'' of the contracted rank type is equal to the contraction
-- of the 'Tail'' of the rank type.
{-# INLINE contractTailSameVNoConProof #-}
contractTailSameVNoConProof :: forall (r :: Rank) (t :: Rank) (t' :: Rank) (i :: Symbol).
                               Sing r ->
                               (t ~ Tail' r, t' ~ Tail' t, (Fst (Head' r) == Fst (Head' t)) ~ 'True,
                                Snd (Head' r) ~ 'ICov i)
                               :- (Tail' (ContractR r) ~ ContractR t)
contractTailSameVNoConProof _ = Sub axiom
  where
    axiom :: (t ~ Tail' r, t' ~ Tail' t, (Fst (Head' r) == Fst (Head' t)) ~ 'True,
              Snd (Head' r) ~ 'ICov i)
             => Dict (Tail' (ContractR r) ~ ContractR t)
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))

-- |If the first two labels of a rank type cannot be contracted because the second label is
-- covariant, the 'Tail'' of the contracted rank type is equal to the contraction
-- of the 'Tail'' of the rank type.
{-# INLINE contractTailSameVNoCovProof #-}
contractTailSameVNoCovProof :: forall (r :: Rank) (t :: Rank) (t' :: Rank) (i :: Symbol).
                               Sing r ->
                               (t ~ Tail' r, t' ~ Tail' t, (Fst (Head' r) == Fst (Head' t)) ~ 'True,
                                Snd (Head' t) ~ 'ICon i)
                               :- (Tail' (ContractR r) ~ ContractR t)
contractTailSameVNoCovProof _ = Sub axiom
  where
    axiom :: (t ~ Tail' r, t' ~ Tail' t, (Fst (Head' r) == Fst (Head' t)) ~ 'True,
              Snd (Head' t) ~ 'ICon i)
             => Dict (Tail' (ContractR r) ~ ContractR t)
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))

-- |If the first two labels of a rank type cannot be contracted because they differ,
-- the 'Tail'' of the contracted rank type is equal to the contraction of the 'Tail'' of the rank type.
{-# INLINE contractTailSameVDiffIProof #-}
contractTailSameVDiffIProof :: forall (r :: Rank) (t :: Rank) (t' :: Rank) (i :: Symbol) (j :: Symbol).
                               Sing r ->
                               (t ~ Tail' r, t' ~ Tail' t, (Fst (Head' r) == Fst (Head' t)) ~ 'True,
                                Snd (Head' r) ~ 'ICon i, Snd (Head' t) ~ 'ICov j, (i == j) ~ 'False)
                               :- (Tail' (ContractR r) ~ ContractR t)
contractTailSameVDiffIProof _ = Sub axiom
  where
    axiom :: (t ~ Tail' r, t' ~ Tail' t, (Fst (Head' r) == Fst (Head' t)) ~ 'True,
              Snd (Head' r) ~ 'ICon i, Snd (Head' t) ~ 'ICov j, (i == j) ~ 'False)
             => Dict (Tail' (ContractR r) ~ ContractR t)
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))

-- |If the first two labels of a rank type can be contracted, the contracted rank type is equal
-- to the contraction of the tail.
{-# INLINE contractTailSameVSameIProof #-}
contractTailSameVSameIProof :: forall (r :: Rank) (t :: Rank) (t' :: Rank) (i :: Symbol) (j :: Symbol).
                               Sing r ->
                               (t ~ Tail' r, t' ~ Tail' t, (Fst (Head' r) == Fst (Head' t)) ~ 'True,
                                Snd (Head' r) ~ 'ICon i, Snd (Head' t) ~ 'ICov j, (i == j) ~ 'True)
                               :- (ContractR t' ~ ContractR r)
contractTailSameVSameIProof _ = Sub axiom
  where
    axiom :: (t ~ Tail' r, t' ~ Tail' t, (Fst (Head' r) == Fst (Head' t)) ~ 'True,
              Snd (Head' r) ~ 'ICon i, Snd (Head' t) ~ 'ICov j, (i == j) ~ 'True)
             => Dict (ContractR t' ~ ContractR r)
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))
