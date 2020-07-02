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

module Proofs where

import TH

import Data.Constraint
import Unsafe.Coerce (unsafeCoerce)

import Data.Singletons
import Data.Singletons.Prelude

{-# INLINE saneTail'Proof #-}
saneTail'Proof :: forall (l :: ILists).Sing l -> (Sane l ~ 'True) :- (Sane (Tail' l) ~ 'True)
saneTail'Proof _ = Sub axiom
  where
    axiom :: Sane l ~ 'True => Dict (Sane (Tail' l) ~ 'True)
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))

{-# INLINE singITail'Proof #-}
singITail'Proof :: forall (l :: ILists).Sing l -> SingI l :- SingI (Tail' l)
singITail'Proof _ = Sub axiom
  where
    axiom :: SingI l => Dict (SingI (Tail' l))
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))

{-# INLINE saneMergeILsProof #-}
saneMergeILsProof :: forall (l :: ILists) (l' :: ILists) (l'' :: ILists).
                     Sing l -> Sing l' ->
                     (Sane l ~ 'True, Sane l' ~ 'True, MergeILs l l' ~ 'Just l'') :- (Sane l'' ~ 'True)
saneMergeILsProof _ _ = Sub axiom
  where
    axiom :: (Sane l ~ 'True, Sane l' ~ 'True, MergeILs l l' ~ 'Just l'') =>
             Dict (Sane l'' ~ 'True)
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))

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

{-# INLINE saneContractProof #-}
saneContractProof :: forall (l :: ILists).Sing l -> (Sane l ~ 'True) :- (Sane (ContractL l) ~ 'True)
saneContractProof _ = Sub axiom
  where
    axiom :: Sane l ~ 'True => Dict (Sane (ContractL l) ~ 'True)
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))

{-# INLINE singletonContractProof #-}
singletonContractProof :: forall (l :: ILists).
                          Sing l -> (Tail' l ~ '[]) :- (ContractL l ~ l)
singletonContractProof _ = Sub axiom
  where
    axiom :: Tail' l ~ '[] => Dict (ContractL l ~ l)
    axiom = unsafeCoerce (Dict :: Dict (a ~ a))

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
