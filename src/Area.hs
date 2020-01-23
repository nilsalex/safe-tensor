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
{-# LANGUAGE OverloadedStrings #-}

module Area where

import TH
import Safe
import Tensor

import Data.Singletons
import Data.Singletons.Prelude
import Data.Singletons.Decide

import Data.Maybe (catMaybes)

import Data.Ratio

import qualified Data.Map.Strict as Map

import Control.Monad.Except

trianMapArea :: Map.Map (Vec (S (S (S (S Z)))) Int) Int
trianMapArea = Map.fromList $ zip indices4 indices1
  where
    indices1 = [0..]
    indices4 = [a `VCons` (b `VCons` (c `VCons` (d `VCons` VNil))) |
                  a <- [0..2],
                  b <- [a+1..3],
                  c <- [a..2],
                  d <- [c+1..3],
                  not (a == c && b > d) ]

facMapArea :: Num b => Map.Map (Vec (S (S (S (S Z)))) Int) b
facMapArea = Map.fromList $ [(a `VCons` (b `VCons` (c `VCons` (d `VCons` VNil))), fac a b c d) |
                                a <- [0..2],
                                b <- [a+1..3],
                                c <- [a..2],
                                d <- [c+1..3],
                                not (a == c && b > d)]
  where
    fac a b c d
      | a == c && b == d = 4
      | otherwise        = 8

injAreaCon' :: forall (id :: Symbol) (a :: Symbol) (b :: Symbol) ( c :: Symbol) (d :: Symbol)
                     (i :: Symbol) (l :: ILists) v.
               (
                InjAreaConILists id a b c d i ~ 'Just l,
                SingI l,
                Num v
               ) => Sing id -> Sing a -> Sing b -> Sing c -> Sing d -> Sing i -> Tensor l v
injAreaCon' sid sa sb sc sd si =
    case sLengthILs sl of
      SS (SS (SS (SS (SS SZ)))) ->
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

injAreaCov' :: forall (id :: Symbol) (a :: Symbol) (b :: Symbol) ( c :: Symbol) (d :: Symbol)
                     (i :: Symbol) (l :: ILists) v.
               (
                InjAreaCovILists id a b c d i ~ 'Just l,
                SingI l,
                Num v
               ) => Sing id -> Sing a -> Sing b -> Sing c -> Sing d -> Sing i -> Tensor l v
injAreaCov' sid sa sb sc sd si =
    case sLengthILs sl of
      SS (SS (SS (SS (SS SZ)))) ->
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

surjAreaCon' :: forall (id :: Symbol) (a :: Symbol) (b :: Symbol) ( c :: Symbol) (d :: Symbol)
                     (i :: Symbol) (l :: ILists) v.
               (
                SurjAreaConILists id a b c d i ~ 'Just l,
                SingI l,
                Fractional v
               ) => Sing id -> Sing a -> Sing b -> Sing c -> Sing d -> Sing i -> Tensor l v
surjAreaCon' sid sa sb sc sd si =
    case sLengthILs sl of
      SS (SS (SS (SS (SS SZ)))) ->
        case sSane sl %~ STrue of
          Proved Refl -> fromList assocs
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

surjAreaCov' :: forall (id :: Symbol) (a :: Symbol) (b :: Symbol) ( c :: Symbol) (d :: Symbol)
                     (i :: Symbol) (l :: ILists) v.
               (
                SurjAreaCovILists id a b c d i ~ 'Just l,
                SingI l,
                Fractional v
               ) => Sing id -> Sing a -> Sing b -> Sing c -> Sing d -> Sing i -> Tensor l v
surjAreaCov' sid sa sb sc sd si =
    case sLengthILs sl of
      SS (SS (SS (SS (SS SZ)))) ->
        case sSane sl %~ STrue of
          Proved Refl -> fromList assocs
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

someInjAreaCon :: (Num v, MonadError String m) =>
                  Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol ->
                  m (T v)
someInjAreaCon vid a b c d i =
  withSomeSing vid $ \svid ->
  withSomeSing a   $ \sa ->
  withSomeSing b   $ \sb ->
  withSomeSing c   $ \sc ->
  withSomeSing d   $ \sd ->
  withSomeSing i   $ \si ->
  case sInjAreaConILists svid sa sb sc sd si of
    SJust sl ->
      withSingI sl $
      case sSane sl %~ STrue of
        Proved Refl -> return $ T $ injAreaCon' svid sa sb sc sd si

someSurjAreaCon :: (Fractional v, MonadError String m) =>
                  Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol ->
                  m (T v)
someSurjAreaCon vid a b c d i =
  withSomeSing vid $ \svid ->
  withSomeSing a   $ \sa ->
  withSomeSing b   $ \sb ->
  withSomeSing c   $ \sc ->
  withSomeSing d   $ \sd ->
  withSomeSing i   $ \si ->
  case sSurjAreaConILists svid sa sb sc sd si of
    SJust sl ->
      withSingI sl $
      case sSane sl %~ STrue of
        Proved Refl -> return $ T $ surjAreaCon' svid sa sb sc sd si

someInjAreaCov :: (Num v, MonadError String m) =>
                  Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol ->
                  m (T v)
someInjAreaCov vid a b c d i =
  withSomeSing vid $ \svid ->
  withSomeSing a   $ \sa ->
  withSomeSing b   $ \sb ->
  withSomeSing c   $ \sc ->
  withSomeSing d   $ \sd ->
  withSomeSing i   $ \si ->
  case sInjAreaCovILists svid sa sb sc sd si of
    SJust sl ->
      withSingI sl $
      case sSane sl %~ STrue of
        Proved Refl -> return $ T $ injAreaCov' svid sa sb sc sd si

someSurjAreaCov :: (Fractional v, MonadError String m) =>
                  Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol ->
                  m (T v)
someSurjAreaCov vid a b c d i =
  withSomeSing vid $ \svid ->
  withSomeSing a   $ \sa ->
  withSomeSing b   $ \sb ->
  withSomeSing c   $ \sc ->
  withSomeSing d   $ \sd ->
  withSomeSing i   $ \si ->
  case sSurjAreaCovILists svid sa sb sc sd si of
    SJust sl ->
      withSingI sl $
      case sSane sl %~ STrue of
        Proved Refl -> return $ T $ surjAreaCov' svid sa sb sc sd si

someInterAreaCon :: (Num v, MonadError String m) =>
                    Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol ->
                    m (T v)
someInterAreaCon vid m n a b =
  do
    (j :: T Rational) <- someSurjAreaCon vid " 1" " 2" " 3" n a
    (i :: T Rational) <- someInjAreaCon vid " 1" " 2" " 3" m b
    prod <- i .* j
    let res = contractT $ fmap (*(-4)) prod
    return $ fmap (\i -> if denominator i == 1
                         then fromIntegral (numerator i)
                         else error "") res

someInterAreaCov :: (Num v, MonadError String m) =>
                    Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol ->
                    m (T v)
someInterAreaCov vid m n a b =
  do
    (j :: T Rational) <- someSurjAreaCov vid " 1" " 2" " 3" m a
    (i :: T Rational) <- someInjAreaCov vid " 1" " 2" " 3" n b
    prod <- i .* j
    let res = contractT $ fmap (*4) prod
    return $ fmap (\i -> if denominator i == 1
                         then fromIntegral (numerator i)
                         else error "") res
