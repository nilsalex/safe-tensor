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

import Data.Maybe (catMaybes)

import qualified Data.Map.Strict as Map

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

injSym2Con :: forall (id :: Symbol) (n :: Nat) (a :: Symbol) (b :: Symbol)
                      (i :: Symbol) (l :: ILists) v.
               (
                InjSym2ConILists id n a b i ~ l,
                (a < b) ~ 'True,
                KnownNat n,
                SingI l,
                Num v
               ) => Tensor l v
injSym2Con =
        case sSane sl %~ STrue of
          Proved Refl -> fromList assocs
  where
    sl = sing :: Sing l
    sn = sing :: Sing n
    n  = withKnownNat sn (natVal sn)
    tm = trianMapSym2 n
    maxInd = fromIntegral n - (1 :: Int)
    assocs = (\a b -> let v = vec a b
                      in case Map.lookup v tm of
                           Just i -> (a `VCons` (b `VCons` (i `VCons` VNil)), (1 :: v))
                           _      -> error $ "indices " ++ show (min a b, max a b) ++
                                             " not present in triangle map " ++ show tm)
             <$> [0..maxInd] <*> [0..maxInd]

    vec a b = min a b `VCons` (max a b `VCons` VNil)

injSym2Cov :: forall (id :: Symbol) (n :: Nat) (a :: Symbol) (b :: Symbol)
                      (i :: Symbol) (l :: ILists) v.
               (
                InjSym2CovILists id n a b i ~ l,
                (a < b) ~ 'True,
                KnownNat n,
                SingI l,
                Num v
               ) => Tensor l v
injSym2Cov =
        case sSane sl %~ STrue of
          Proved Refl -> fromList assocs
  where
    sl = sing :: Sing l
    sn = sing :: Sing n
    n  = withKnownNat sn (natVal sn)
    tm = trianMapSym2 n
    maxInd = fromIntegral n - (1 :: Int)
    assocs = (\a b -> let v = vec a b
                      in case Map.lookup v tm of
                           Just i -> (a `VCons` (b `VCons` (i `VCons` VNil)), (1 :: v))
                           _      -> error $ "indices " ++ show (min a b, max a b) ++
                                             " not present in triangle map " ++ show tm)
             <$> [0..maxInd] <*> [0..maxInd]

    vec a b = min a b `VCons` (max a b `VCons` VNil)

surjSym2Con :: forall (id :: Symbol) (n :: Nat) (a :: Symbol) (b :: Symbol)
                      (i :: Symbol) (l :: ILists) v.
               (
                SurjSym2ConILists id n a b i ~ l,
                (a < b) ~ 'True,
                KnownNat n,
                SingI l,
                Fractional v
               ) => Tensor l v
surjSym2Con =
        case sSane sl %~ STrue of
          Proved Refl -> fromList assocs
  where
    sl = sing :: Sing l
    sn = sing :: Sing n
    n  = withKnownNat sn (natVal sn)
    tm = trianMapSym2 n
    fm = facMapSym2 n
    maxInd = fromIntegral (withKnownNat sn (natVal sn)) - (1 :: Int)
    assocs = (\a b -> case
                        (do
                           let v = vec a b
                           i <- Map.lookup v tm
                           f <- Map.lookup v fm
                           return (a `VCons` (b `VCons` (i `VCons` VNil)), (1 / f :: v))) of
                        Just x -> x
                        Nothing -> error "")
             <$> [0..maxInd] <*> [0..maxInd]

    vec a b = min a b `VCons` (max a b `VCons` VNil)

surjSym2Cov :: forall (id :: Symbol) (n :: Nat) (a :: Symbol) (b :: Symbol)
                      (i :: Symbol) (l :: ILists) v.
               (
                SurjSym2CovILists id n a b i ~ l,
                (a < b) ~ 'True,
                KnownNat n,
                SingI l,
                Fractional v
               ) => Tensor l v
surjSym2Cov =
        case sSane sl %~ STrue of
          Proved Refl -> fromList assocs
  where
    sl = sing :: Sing l
    sn = sing :: Sing n
    n  = withKnownNat sn (natVal sn)
    tm = trianMapSym2 n
    fm = facMapSym2 n
    maxInd = fromIntegral (withKnownNat sn (natVal sn)) - (1 :: Int)
    assocs = (\a b -> case
                        (do
                           let v = vec a b
                           i <- Map.lookup v tm
                           f <- Map.lookup v fm
                           return (a `VCons` (b `VCons` (i `VCons` VNil)), (1 / f :: v))) of
                        Just x -> x
                        Nothing -> error "")
             <$> [0..maxInd] <*> [0..maxInd]

    vec a b = min a b `VCons` (max a b `VCons` VNil)

injAreaCon :: forall (id :: Symbol) (a :: Symbol) (b :: Symbol) ( c :: Symbol) (d :: Symbol)
                     (i :: Symbol) (l :: ILists) v.
               (
                InjAreaConILists id a b c d i ~ l,
                (a < b) ~ 'True,
                (b < c) ~ 'True,
                (c < d) ~ 'True,
                SingI l,
                Num v
               ) => Tensor l v
injAreaCon =
        case sSane sl %~ STrue of
          Proved Refl -> fromList assocs
  where
    sl = sing :: Sing l
    tm = trianMapArea
    assocs = catMaybes $
             (\a b c d ->
                  do
                     s <- areaSign a b c d 
                     let v = sortArea a b c d
                     i <- Map.lookup v tm
                     return (a `VCons` (b `VCons` (c `VCons` (d `VCons` (i `VCons` VNil)))), (s :: v)))
             <$> [0..3] <*> [0..3] <*> [0..3] <*> [0..3] 

    areaSign a b c d
      | a == b = Nothing
      | c == d = Nothing
      | a > b  = fmap ((-1) *) $ areaSign b a c d
      | c > d  = fmap ((-1) *) $ areaSign a b d c
      | otherwise = Just 1

    sortArea a b c d
      | a > b = sortArea b a c d
      | c > d = sortArea a b d c
      | (a,b) > (c,d) = sortArea c d a b
      | otherwise = a `VCons` (b `VCons` (c `VCons` (d `VCons` VNil)))

injAreaCov :: forall (id :: Symbol) (a :: Symbol) (b :: Symbol) ( c :: Symbol) (d :: Symbol)
                     (i :: Symbol) (l :: ILists) v.
               (
                InjAreaCovILists id a b c d i ~ l,
                (a < b) ~ 'True,
                (b < c) ~ 'True,
                (c < d) ~ 'True,
                SingI l,
                Num v
               ) => Tensor l v
injAreaCov =
        case sSane sl %~ STrue of
          Proved Refl -> fromList assocs
  where
    sl = sing :: Sing l
    tm = trianMapArea
    assocs = catMaybes $
             (\a b c d ->
                  do
                     s <- areaSign a b c d 
                     let v = sortArea a b c d
                     i <- Map.lookup v tm
                     return (a `VCons` (b `VCons` (c `VCons` (d `VCons` (i `VCons` VNil)))), (s :: v)))
             <$> [0..3] <*> [0..3] <*> [0..3] <*> [0..3] 

    areaSign a b c d
      | a == b = Nothing
      | c == d = Nothing
      | a > b  = fmap ((-1) *) $ areaSign b a c d
      | c > d  = fmap ((-1) *) $ areaSign a b d c
      | otherwise = Just 1

    sortArea a b c d
      | a > b = sortArea b a c d
      | c > d = sortArea a b d c
      | (a,b) > (c,d) = sortArea c d a b
      | otherwise = a `VCons` (b `VCons` (c `VCons` (d `VCons` VNil)))

surjAreaCon :: forall (id :: Symbol) (a :: Symbol) (b :: Symbol) ( c :: Symbol) (d :: Symbol)
                     (i :: Symbol) (l :: ILists) v.
               (
                SurjAreaConILists id a b c d i ~ l,
                (a < b) ~ 'True,
                (b < c) ~ 'True,
                (c < d) ~ 'True,
                SingI l,
                Fractional v
               ) => Tensor l v
surjAreaCon =
        case sSane sl %~ STrue of
          Proved Refl -> fromList (assocs :: [(Vec (S (S (S (S (S Z))))) Int, v)])
  where
    sl = sing :: Sing l
    tm = trianMapArea
    fm = facMapArea
    assocs = catMaybes $
             (\a b c d ->
                  do
                     s <- areaSign a b c d 
                     let v = sortArea a b c d
                     i <- Map.lookup v tm
                     f <- Map.lookup v fm
                     return (a `VCons` (b `VCons` (c `VCons` (d `VCons` (i `VCons` VNil)))), (s/f :: v)))
             <$> [0..3] <*> [0..3] <*> [0..3] <*> [0..3] 

    areaSign a b c d
      | a == b = Nothing
      | c == d = Nothing
      | a > b  = fmap ((-1) *) $ areaSign b a c d
      | c > d  = fmap ((-1) *) $ areaSign a b d c
      | otherwise = Just 1

    sortArea a b c d
      | a > b = sortArea b a c d
      | c > d = sortArea a b d c
      | (a,b) > (c,d) = sortArea c d a b
      | otherwise = a `VCons` (b `VCons` (c `VCons` (d `VCons` VNil)))

surjAreaCov :: forall (id :: Symbol) (a :: Symbol) (b :: Symbol) ( c :: Symbol) (d :: Symbol)
                     (i :: Symbol) (l :: ILists) v.
               (
                SurjAreaCovILists id a b c d i ~ l,
                (a < b) ~ 'True,
                (b < c) ~ 'True,
                (c < d) ~ 'True,
                SingI l,
                Fractional v
               ) => Tensor l v
surjAreaCov =
        case sSane sl %~ STrue of
          Proved Refl -> fromList (assocs :: [(Vec (S (S (S (S (S Z))))) Int, v)])
  where
    sl = sing :: Sing l
    tm = trianMapArea
    fm = facMapArea
    assocs = catMaybes $
             (\a b c d ->
                  do
                     s <- areaSign a b c d 
                     let v = sortArea a b c d
                     i <- Map.lookup v tm
                     f <- Map.lookup v fm
                     return (a `VCons` (b `VCons` (c `VCons` (d `VCons` (i `VCons` VNil)))), (s/f :: v)))
             <$> [0..3] <*> [0..3] <*> [0..3] <*> [0..3] 

    areaSign a b c d
      | a == b = Nothing
      | c == d = Nothing
      | a > b  = fmap ((-1) *) $ areaSign b a c d
      | c > d  = fmap ((-1) *) $ areaSign a b d c
      | otherwise = Just 1

    sortArea a b c d
      | a > b = sortArea b a c d
      | c > d = sortArea a b d c
      | (a,b) > (c,d) = sortArea c d a b
      | otherwise = a `VCons` (b `VCons` (c `VCons` (d `VCons` VNil)))

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
