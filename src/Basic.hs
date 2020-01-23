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

module Basic where

import TH
import Internal
import Safe
import Tensor

import Data.Singletons
import Data.Singletons.Prelude
import Data.Singletons.Decide
import Data.Singletons.TypeLits

import Data.List (sort,permutations)
import Data.List.NonEmpty (NonEmpty(..))

import Control.Monad.Except

epsilon :: forall (id :: Symbol) (n :: Nat) (is :: NonEmpty Symbol) (l :: ILists) v.
              (
               KnownNat n,
               Num v,
               EpsilonILists id n is ~ 'Just l,
               SingI l
              ) =>
              Sing id -> Sing n -> Sing is -> Tensor l v
epsilon sid sn sis =
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

epsilonInv :: forall (id :: Symbol) (n :: Nat) (is :: NonEmpty Symbol) (l :: ILists) v.
              (
               KnownNat n,
               Num v,
               EpsilonInvILists id n is ~ 'Just l,
               SingI l
              ) =>
              Sing id -> Sing n -> Sing is -> Tensor l v
epsilonInv sid sn sis =
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

delta' :: forall (id :: Symbol) (n :: Nat) (a :: Symbol) (b :: Symbol) (l :: ILists) v.
          (
           KnownNat n,
           Num v,
           '[ '( 'VSpace id n, 'ConCov (a :| '[]) (b :| '[])) ] ~ l,
           Tail' (Tail' l) ~ '[],
           Sane (Tail' l) ~ 'True
          ) =>
          Sing id -> Sing n -> Sing a -> Sing b ->
          Tensor l v
delta' _ _ _ _ = delta

delta :: forall (id :: Symbol) (n :: Nat) (a :: Symbol) (b :: Symbol) (l :: ILists) v.
         (
          '[ '( 'VSpace id n, 'ConCov (a :| '[]) (b :| '[]))] ~ l,
          Tail' (Tail' l) ~ '[],
          Sane (Tail' l) ~ 'True,
          SingI n,
          Num v
         ) => Tensor l v
delta = case (sing :: Sing n) of
          sn -> let x = fromIntegral $ withKnownNat sn $ natVal sn
                in Tensor (f x)
  where
    f x = map (\i -> (i, Tensor [(i, Scalar 1)])) [0..x - 1]

eta' :: forall (id :: Symbol) (n :: Nat) (a :: Symbol) (b :: Symbol) (l :: ILists) v.
        (
         '[ '( 'VSpace id n, 'Cov (a :| '[b])) ] ~ l,
         (a < b) ~ 'True,
         SingI n,
         Num v
        ) =>
        Sing id -> Sing n -> Sing a -> Sing b ->
        Tensor l v
eta' _ _ _ _ = eta

eta :: forall (id :: Symbol) (n :: Nat) (a :: Symbol) (b :: Symbol) (l :: ILists) v.
       (
        '[ '( 'VSpace id n, 'Cov (a :| '[b])) ] ~ l,
        (a < b) ~ 'True,
        SingI n,
        Num v
       ) => Tensor l v
eta = case (sing :: Sing n) of
        sn -> let x = fromIntegral $ withKnownNat sn $ natVal sn
              in Tensor (f x)
  where
    f x = map (\i -> (i, Tensor [(i, Scalar (if i == 0 then 1 else -1))])) [0..x - 1]

etaInv' :: forall (id :: Symbol) (n :: Nat) (a :: Symbol) (b :: Symbol) (l :: ILists) v.
        (
         '[ '( 'VSpace id n, 'Con (a :| '[b])) ] ~ l,
         (a < b) ~ 'True,
         SingI n,
         Num v
        ) =>
        Sing id -> Sing n -> Sing a -> Sing b ->
        Tensor l v
etaInv' _ _ _ _ = etaInv

etaInv :: forall (id :: Symbol) (n :: Nat) (a :: Symbol) (b :: Symbol) (l :: ILists) v.
       (
        '[ '( 'VSpace id n, 'Con (a :| '[b])) ] ~ l,
        (a < b) ~ 'True,
        SingI n,
        Num v
       ) => Tensor l v
etaInv = case (sing :: Sing n) of
        sn -> let x = fromIntegral $ withKnownNat sn $ natVal sn
              in Tensor (f x)
  where
    f x = map (\i -> (i, Tensor [(i, Scalar (if i == 0 then 1 else -1))])) [0..x - 1]

asym :: forall (id :: Symbol) (n :: Nat) (a :: Symbol) (b :: Symbol) (l :: ILists) v.
       (
        '[ '( 'VSpace id n, 'Con (a :| '[b])) ] ~ l,
        (a < b) ~ 'True,
        SingI n,
        Num v
       ) => Tensor l v
asym = case (sing :: Sing n) of
        sn -> let x = fromIntegral $ withKnownNat sn $ natVal sn
              in Tensor (f x)
  where
    f x = fmap (\i -> (i, Tensor $
            fmap (\j -> (j, Scalar (case i `compare` j of
                                      LT -> 1
                                      EQ -> 0
                                      GT -> -1))) [0..x-1])) [0..x-1]

surjSym2Con :: forall (id :: Symbol) (n :: Nat) (a :: Symbol) (b :: Symbol)
                      (i :: Symbol) (l :: ILists) v.
               (

               ) => Tensor l v
surjSym2Con

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
  let sl = sDeltaILists svid svdim sa sb
  in  case sTail' (sTail' sl) of
        SNil -> case sSane (sTail' sl) %~ STrue of
                  Proved Refl -> T $ delta' svid svdim sa sb

someEta :: (Num v, MonadError String m) =>
           Demote Symbol -> Demote Nat -> Demote Symbol -> Demote Symbol ->
           m (T v)
someEta vid vdim a b =
  withSomeSing vid $ \svid ->
  withSomeSing vdim $ \svdim ->
  withSomeSing a $ \sa ->
  withSomeSing b $ \sb ->
  withKnownNat svdim $
  withKnownSymbol svid $
  withKnownSymbol sa $
  withKnownSymbol sb $
  case sCompare sa sb of
    SLT -> return $ T $ eta' svid svdim sa sb
    _   -> throwError $ "cannot construct eta with indices " ++ show vid ++ " " ++ show vdim ++ " " ++ show a ++ " " ++ show b

someEtaInv :: (Num v, MonadError String m) =>
           Demote Symbol -> Demote Nat -> Demote Symbol -> Demote Symbol ->
           m (T v)
someEtaInv vid vdim a b =
  withSomeSing vid $ \svid ->
  withSomeSing vdim $ \svdim ->
  withSomeSing a $ \sa ->
  withSomeSing b $ \sb ->
  withKnownNat svdim $
  withKnownSymbol svid $
  withKnownSymbol sa $
  withKnownSymbol sb $
  case sCompare sa sb of
    SLT -> return $ T $ etaInv' svid svdim sa sb
    _   -> throwError $ "cannot construct eta with indices " ++ show vid ++ " " ++ show vdim ++ " " ++ show a ++ " " ++ show b

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
      return $ T $ epsilon svid svdim sis
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
      return $ T $ epsilonInv svid svdim sis
    SNothing -> throwError $ "Illegal index list " ++ show (i:is) ++ "!"

type V4 = 'VSpace "Spacetime" 4
type Up2 a b = 'Con (a :| '[b])
type UpDown a b = 'ConCov (a :| '[]) (b :| '[])

d_ap :: Tensor '[ '(V4, UpDown "p" "a") ] Rational
d_ap = delta

e_ab :: Tensor '[ '(V4, Up2 "a" "b") ] Rational
e_ab = etaInv

as_ab :: Tensor '[ '(V4, Up2 "a" "b") ] Rational
as_ab = asym
