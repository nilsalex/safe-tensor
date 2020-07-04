{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}

-----------------------------------------------------------------------------
{-|
Module      : Tensor.Safe.Proofs
Description : Identities for functions on generalized tensor ranks.
Copyright   : (c) Nils Alex, 2020
License     : MIT
Maintainer  : nils.alex@fau.de
Stability   : experimental

Identities for functions on generalized tensor ranks.
-}
-----------------------------------------------------------------------------
module Tensor.Safe.Proofs
  ( -- * Tails of sane ranks are sane
    saneTail'Proof
  , singITail'Proof
  , -- * Properties of merged ranks
    saneMergeILsProof
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

import Tensor.Safe.TH

import Data.Constraint
import Unsafe.Coerce (unsafeCoerce)

import Data.Singletons
import Data.Singletons.Prelude

-- |The 'Tail'' of a sane rank type is sane.
{-# INLINE saneTail'Proof #-}
saneTail'Proof :: forall (l :: ILists).Sing l -> (Sane l ~ 'True) :- (Sane (Tail' l) ~ 'True)
saneTail'Proof _ = Sub axiom
  where
    axiom :: Sane l ~ 'True => Dict (Sane (Tail' l) ~ 'True)
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))

-- |If a rank type has a 'SingI' instance, the tail has a 'SingI' instance.
{-# INLINE singITail'Proof #-}
singITail'Proof :: forall (l :: ILists).Sing l -> SingI l :- SingI (Tail' l)
singITail'Proof _ = Sub axiom
  where
    axiom :: SingI l => Dict (SingI (Tail' l))
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))

-- |Successfully merging two sane rank types (result is not @Nothing@) yields a sane rank type.
{-# INLINE saneMergeILsProof #-}
saneMergeILsProof :: forall (l :: ILists) (l' :: ILists) (l'' :: ILists).
                     Sing l -> Sing l' ->
                     (Sane l ~ 'True, Sane l' ~ 'True, MergeILs l l' ~ 'Just l'') :- (Sane l'' ~ 'True)
saneMergeILsProof _ _ = Sub axiom
  where
    axiom :: (Sane l ~ 'True, Sane l' ~ 'True, MergeILs l l' ~ 'Just l'') =>
             Dict (Sane l'' ~ 'True)
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))

-- |If two rank types can be merged and the first 'VSpace' of the first rank type is less than
-- the first 'VSpace' of the second rank type, the 'Tail'' of the merged rank type is equal to
-- the tail of the first rank type merged with the second rank type.
{-# INLINE proofMergeLT #-}
proofMergeLT :: forall (l :: ILists) (l' :: ILists) (l'' :: ILists).
                Sing l -> Sing l' ->
                (Sane l ~ 'True, Sane l' ~ 'True, MergeILs l l' ~ 'Just l'',
                 Compare (Fst (Head' l)) (Fst (Head' l')) ~ 'LT)
                :- (MergeILs (Tail' l) l' ~ Just (Tail' l''))
proofMergeLT _ _ = Sub axiom
  where
    axiom :: (Sane l ~ 'True, Sane l' ~ 'True, MergeILs l l' ~ 'Just l'',
              Compare (Fst (Head' l)) (Fst (Head' l')) ~ 'LT)
             => Dict (MergeILs (Tail' l) l' ~ 'Just (Tail' l''))
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))

-- |If two rank types can be merged and the first 'VSpace' of the first rank type coincides with
-- the first 'VSpace' of the second rank type, the first index of the first rank type cannot
-- equal the first index of the second rank type.
{-# INLINE proofMergeIxNotEQ #-}
proofMergeIxNotEQ :: forall (l :: ILists) (l' :: ILists) (l'' :: ILists).
                     Sing l -> Sing l' ->
                     (Sane l ~ 'True, Sane l' ~ 'True, MergeILs l l' ~ 'Just l'',
                      Compare (Fst (Head' l)) (Fst (Head' l')) ~ 'EQ)
                     :- ((IxCompare (Snd (Head' l)) (Snd (Head' l')) == 'EQ) ~ 'False)
proofMergeIxNotEQ _ _ = Sub axiom
  where
    axiom :: (Sane l ~ 'True, Sane l' ~ 'True, MergeILs l l' ~ 'Just l'',
             Compare (Fst (Head' l)) (Fst (Head' l')) ~ 'EQ)
             => Dict ((IxCompare (Snd (Head' l)) (Snd (Head' l')) == 'EQ) ~ 'False)
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))

-- |If two rank types can be merged and the first 'VSpace' of the first rank type coincides with
-- the first 'VSpace' of the second rank type and the first index of the first rank type compares
-- less than the first index of the second rank type, the 'Tail'' of the merged rank type is equal
-- to the tail of the first rank type merged with the second rank type.
{-# INLINE proofMergeIxLT #-}
proofMergeIxLT :: forall (l :: ILists) (l' :: ILists) (l'' :: ILists).
                  Sing l -> Sing l' ->
                  (Sane l ~ 'True, Sane l' ~ 'True, MergeILs l l' ~ 'Just l'',
                   Compare (Fst (Head' l)) (Fst (Head' l')) ~ 'EQ,
                   IxCompare (Snd (Head' l)) (Snd (Head' l')) ~ 'LT)
                  :- (MergeILs (Tail' l) l' ~ Just (Tail' l''))
proofMergeIxLT _ _ = Sub axiom
  where
    axiom :: (Sane l ~ 'True, Sane l' ~ 'True, MergeILs l l' ~ 'Just l'',
              Compare (Fst (Head' l)) (Fst (Head' l')) ~ 'EQ,
              IxCompare (Snd (Head' l)) (Snd (Head' l')) ~ LT)
             => Dict (MergeILs (Tail' l) l' ~ 'Just (Tail' l''))
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))

-- |If two rank types can be merged and the first 'VSpace' of the first rank type is greater than
-- the first 'VSpace' of the second rank type, the 'Tail'' of the merged rank type is equal to
-- the first rank type merged with the tail of the second rank type.
{-# INLINE proofMergeGT #-}
proofMergeGT :: forall (l :: ILists) (l' :: ILists) (l'' :: ILists).
                Sing l -> Sing l' ->
                (Sane l ~ 'True, Sane l' ~ 'True, MergeILs l l' ~ 'Just l'',
                 Compare (Fst (Head' l)) (Fst (Head' l')) ~ 'GT)
                :- (MergeILs l (Tail' l') ~ Just (Tail' l''))
proofMergeGT _ _ = Sub axiom
  where
    axiom :: (Sane l ~ 'True, Sane l' ~ 'True, MergeILs l l' ~ 'Just l'',
              Compare (Fst (Head' l)) (Fst (Head' l')) ~ 'GT)
             => Dict (MergeILs l (Tail' l') ~ 'Just (Tail' l''))
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))

-- |If two rank types can be merged and the first 'VSpace' of the first rank type coincides with
-- the first 'VSpace' of the second rank type and the first index of the first rank type compares
-- greater than the first index of the second rank type, the 'Tail'' of the merged rank type is equal
-- to the first rank type merged with the tail of the second rank type.
{-# INLINE proofMergeIxGT #-}
proofMergeIxGT :: forall (l :: ILists) (l' :: ILists) (l'' :: ILists).
                  Sing l -> Sing l' ->
                  (Sane l ~ 'True, Sane l' ~ 'True, MergeILs l l' ~ 'Just l'',
                   Compare (Fst (Head' l)) (Fst (Head' l')) ~ 'EQ,
                   IxCompare (Snd (Head' l)) (Snd (Head' l')) ~ 'GT)
                  :- (MergeILs l (Tail' l') ~ Just (Tail' l''))
proofMergeIxGT _ _ = Sub axiom
  where
    axiom :: (Sane l ~ 'True, Sane l' ~ 'True, MergeILs l l' ~ 'Just l'',
              Compare (Fst (Head' l)) (Fst (Head' l')) ~ 'EQ,
              IxCompare (Snd (Head' l)) (Snd (Head' l')) ~ GT)
             => Dict (MergeILs l (Tail' l') ~ 'Just (Tail' l''))
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))

-- |If a rank type is sane, its contraction is also sane.
{-# INLINE saneContractProof #-}
saneContractProof :: forall (l :: ILists).Sing l -> (Sane l ~ 'True) :- (Sane (ContractL l) ~ 'True)
saneContractProof _ = Sub axiom
  where
    axiom :: Sane l ~ 'True => Dict (Sane (ContractL l) ~ 'True)
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))

-- |The contraction of the empty rank type is the empty rank type.
{-# INLINE singletonContractProof #-}
singletonContractProof :: forall (l :: ILists).
                          Sing l -> (Tail' l ~ '[]) :- (ContractL l ~ l)
singletonContractProof _ = Sub axiom
  where
    axiom :: Tail' l ~ '[] => Dict (ContractL l ~ l)
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))

-- |If the first two labels of a rank type cannot be contracted because they belong to
-- different 'VSpace's, the 'Tail'' of the contracted rank type is equal to the contraction
-- of the 'Tail'' of the rank type.
{-# INLINE contractTailDiffVProof #-}
contractTailDiffVProof :: forall (l :: ILists) (t :: ILists) (t' :: ILists).
                          Sing l ->
                          (t ~ Tail' l, t' ~ Tail' t, (Fst (Head' l) == Fst (Head' t)) ~ 'False)
                          :- (Tail' (ContractL l) ~ ContractL t)
contractTailDiffVProof _ = Sub axiom
  where
    axiom :: (t ~ Tail' l, t' ~ Tail' t, (Fst (Head' l) == Fst (Head' t)) ~ 'False)
             => Dict (Tail' (ContractL l) ~ ContractL t)
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))


-- |If the first two labels of a rank type cannot be contracted because the first label is
-- covariant, the 'Tail'' of the contracted rank type is equal to the contraction
-- of the 'Tail'' of the rank type.
{-# INLINE contractTailSameVNoConProof #-}
contractTailSameVNoConProof :: forall (l :: ILists) (t :: ILists) (t' :: ILists) (i :: Symbol).
                               Sing l ->
                               (t ~ Tail' l, t' ~ Tail' t, (Fst (Head' l) == Fst (Head' t)) ~ 'True,
                                Snd (Head' l) ~ 'ICov i)
                               :- (Tail' (ContractL l) ~ ContractL t)
contractTailSameVNoConProof _ = Sub axiom
  where
    axiom :: (t ~ Tail' l, t' ~ Tail' t, (Fst (Head' l) == Fst (Head' t)) ~ 'True,
              Snd (Head' l) ~ 'ICov i)
             => Dict (Tail' (ContractL l) ~ ContractL t)
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))

-- |If the first two labels of a rank type cannot be contracted because the second label is
-- covariant, the 'Tail'' of the contracted rank type is equal to the contraction
-- of the 'Tail'' of the rank type.
{-# INLINE contractTailSameVNoCovProof #-}
contractTailSameVNoCovProof :: forall (l :: ILists) (t :: ILists) (t' :: ILists) (i :: Symbol).
                               Sing l ->
                               (t ~ Tail' l, t' ~ Tail' t, (Fst (Head' l) == Fst (Head' t)) ~ 'True,
                                Snd (Head' t) ~ 'ICon i)
                               :- (Tail' (ContractL l) ~ ContractL t)
contractTailSameVNoCovProof _ = Sub axiom
  where
    axiom :: (t ~ Tail' l, t' ~ Tail' t, (Fst (Head' l) == Fst (Head' t)) ~ 'True,
              Snd (Head' t) ~ 'ICon i)
             => Dict (Tail' (ContractL l) ~ ContractL t)
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))

-- |If the first two labels of a rank type cannot be contracted because they differ,
-- the 'Tail'' of the contracted rank type is equal to the contraction of the 'Tail'' of the rank type.
{-# INLINE contractTailSameVDiffIProof #-}
contractTailSameVDiffIProof :: forall (l :: ILists) (t :: ILists) (t' :: ILists) (i :: Symbol) (j :: Symbol).
                               Sing l ->
                               (t ~ Tail' l, t' ~ Tail' t, (Fst (Head' l) == Fst (Head' t)) ~ 'True,
                                Snd (Head' l) ~ 'ICon i, Snd (Head' t) ~ 'ICov j, (i == j) ~ 'False)
                               :- (Tail' (ContractL l) ~ ContractL t)
contractTailSameVDiffIProof _ = Sub axiom
  where
    axiom :: (t ~ Tail' l, t' ~ Tail' t, (Fst (Head' l) == Fst (Head' t)) ~ 'True,
              Snd (Head' l) ~ 'ICon i, Snd (Head' t) ~ 'ICov j, (i == j) ~ 'False)
             => Dict (Tail' (ContractL l) ~ ContractL t)
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))

-- |If the first two labels of a rank type can be contracted, the contracted rank type is equal
-- to the contraction of the tail.
{-# INLINE contractTailSameVSameIProof #-}
contractTailSameVSameIProof :: forall (l :: ILists) (t :: ILists) (t' :: ILists) (i :: Symbol) (j :: Symbol).
                               Sing l ->
                               (t ~ Tail' l, t' ~ Tail' t, (Fst (Head' l) == Fst (Head' t)) ~ 'True,
                                Snd (Head' l) ~ 'ICon i, Snd (Head' t) ~ 'ICov j, (i == j) ~ 'True)
                               :- (ContractL t' ~ ContractL l)
contractTailSameVSameIProof _ = Sub axiom
  where
    axiom :: (t ~ Tail' l, t' ~ Tail' t, (Fst (Head' l) == Fst (Head' t)) ~ 'True,
              Snd (Head' l) ~ 'ICon i, Snd (Head' t) ~ 'ICov j, (i == j) ~ 'True)
             => Dict (ContractL t' ~ ContractL l)
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))
