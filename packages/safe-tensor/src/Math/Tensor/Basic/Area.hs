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
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

-----------------------------------------------------------------------------
{-|
Module      : Math.Tensor.Basic.Area
Description : Definitions of area-symmetric tensors.
Copyright   : (c) Nils Alex, 2020
License     : MIT
Maintainer  : nils.alex@fau.de

Definitions of area-symmetric tensors.
-}
-----------------------------------------------------------------------------
module Math.Tensor.Basic.Area
  ( -- * Area metric tensor induced from flat Lorentzian metric
    flatAreaCon
  , someFlatAreaCon
  ,  -- * Injections from \(AS(V)\) into \(V\times V\times V\times V\)
    injAreaCon'
  , injAreaCov'
  , someInjAreaCon
  , someInjAreaCov
  , -- * Surjections from \(V\times V\times V\times V\) onto \(AS(V)\)
    surjAreaCon'
  , surjAreaCov'
  , someSurjAreaCon
  , someSurjAreaCov
  , -- * Vertical coefficients for functions on \(AS(V)\)
    someInterAreaCon
  , someInterAreaCov
  , -- * Kronecker delta on \(AS(V)\)
    someDeltaArea
  , -- * Internals
    trianMapArea
  , facMapArea
  , areaSign
  , sortArea
  ) where

import Math.Tensor
import Math.Tensor.Safe
import Math.Tensor.Safe.TH
import Math.Tensor.Basic.TH
import Math.Tensor.Basic.Delta

import Data.Singletons
  ( Sing
  , SingI (sing)
  , Demote
  , withSomeSing
  , withSingI
  )
import Data.Singletons.Prelude
import Data.Singletons.Decide
  ( (:~:) (Refl)
  , Decision (Proved)
  , (%~)
  )
import Data.Singletons.TypeLits
  ( Symbol
  , withKnownSymbol
  )

import Data.Maybe (catMaybes)
import Data.Ratio (Ratio, numerator, denominator)
import qualified Data.Map.Strict as Map
  ( Map
  , lookup
  , fromList
  )
import Data.List.NonEmpty (NonEmpty((:|)))
import Control.Monad.Except
  ( MonadError
  , runExcept
  )

trianMapArea :: Map.Map (Vec ('S ('S ('S ('S 'Z)))) Int) Int
trianMapArea = Map.fromList $ zip indices4 indices1
  where
    indices1 :: [Int]
    indices1 = [0..]
    indices4 :: [Vec ('S ('S ('S ('S 'Z)))) Int]
    indices4 = [a `VCons` (b `VCons` (c `VCons` (d `VCons` VNil))) |
                  a <- [0..2],
                  b <- [a+1..3],
                  c <- [a..2],
                  d <- [c+1..3],
                  not (a == c && b > d) ]

facMapArea :: forall b.Num b => Map.Map (Vec ('S ('S ('S ('S 'Z)))) Int) b
facMapArea = Map.fromList $ [(a `VCons` (b `VCons` (c `VCons` (d `VCons` VNil))), fac a b c d) |
                                a <- [0..2],
                                b <- [a+1..3],
                                c <- [a..2],
                                d <- [c+1..3],
                                not (a == c && b > d)]
  where
    fac :: Int -> Int -> Int -> Int -> b
    fac a b c d
      | a == c && b == d = 4
      | otherwise        = 8

areaSign :: (Ord a, Num v) => a -> a -> a -> a -> Maybe v
areaSign a b c d
  | a == b = Nothing
  | c == d = Nothing
  | a > b  = ((-1) *) <$> areaSign b a c d
  | c > d  = ((-1) *) <$> areaSign a b d c
  | otherwise = Just 1

sortArea :: Ord a => a -> a -> a -> a -> Vec ('S ('S ('S ('S 'Z)))) a
sortArea a b c d
  | a > b = sortArea b a c d
  | c > d = sortArea a b d c
  | (a,b) > (c,d) = sortArea c d a b
  | otherwise = a `VCons` (b `VCons` (c `VCons` (d `VCons` VNil)))


injAreaCon' :: forall (id :: Symbol) (a :: Symbol) (b :: Symbol) ( c :: Symbol) (d :: Symbol)
                     (i :: Symbol) (r :: Rank) v.
               (
                InjAreaConRank id a b c d i ~ 'Just r,
                SingI r,
                Num v
               ) => Sing id -> Sing a -> Sing b -> Sing c -> Sing d -> Sing i -> Tensor r v
injAreaCon' _ _ _ _ _ _ =
    case sLengthR sr of
      SS (SS (SS (SS (SS SZ)))) ->
        case sSane sr %~ STrue of
          Proved Refl -> fromList assocs
  where
    sr = sing :: Sing r
    tm = trianMapArea
    assocs = catMaybes $
             (\a b c d ->
                  do
                     s <- areaSign a b c d
                     let v = sortArea a b c d
                     i <- Map.lookup v tm
                     return (a `VCons` (b `VCons` (c `VCons` (d `VCons` (i `VCons` VNil)))), s :: v))
             <$> [0..3] <*> [0..3] <*> [0..3] <*> [0..3]

injAreaCov' :: forall (id :: Symbol) (a :: Symbol) (b :: Symbol) ( c :: Symbol) (d :: Symbol)
                     (i :: Symbol) (r :: Rank) v.
               (
                InjAreaCovRank id a b c d i ~ 'Just r,
                SingI r,
                Num v
               ) => Sing id -> Sing a -> Sing b -> Sing c -> Sing d -> Sing i -> Tensor r v
injAreaCov' _ _ _ _ _ _ =
    case sLengthR sr of
      SS (SS (SS (SS (SS SZ)))) ->
        case sSane sr %~ STrue of
          Proved Refl -> fromList assocs
  where
    sr = sing :: Sing r
    tm = trianMapArea
    assocs = catMaybes $
             (\a b c d ->
                  do
                     s <- areaSign a b c d
                     let v = sortArea a b c d
                     i <- Map.lookup v tm
                     return (a `VCons` (b `VCons` (c `VCons` (d `VCons` (i `VCons` VNil)))), s :: v))
             <$> [0..3] <*> [0..3] <*> [0..3] <*> [0..3]

surjAreaCon' :: forall (id :: Symbol) (a :: Symbol) (b :: Symbol) ( c :: Symbol) (d :: Symbol)
                     (i :: Symbol) (r :: Rank) v.
               (
                SurjAreaConRank id a b c d i ~ 'Just r,
                SingI r,
                Fractional v
               ) => Sing id -> Sing a -> Sing b -> Sing c -> Sing d -> Sing i -> Tensor r v
surjAreaCon' _ _ _ _ _ _ =
    case sLengthR sr of
      SS (SS (SS (SS (SS SZ)))) ->
        case sSane sr %~ STrue of
          Proved Refl -> fromList assocs
  where
    sr = sing :: Sing r
    tm = trianMapArea
    fm = facMapArea @v
    assocs = catMaybes $
             (\a b c d ->
                  do
                     s <- areaSign a b c d
                     let v = sortArea a b c d
                     i <- Map.lookup v tm
                     f <- Map.lookup v fm
                     return (a `VCons` (b `VCons` (c `VCons` (d `VCons` (i `VCons` VNil)))), s/f :: v))
             <$> [0..3] <*> [0..3] <*> [0..3] <*> [0..3]

surjAreaCov' :: forall (id :: Symbol) (a :: Symbol) (b :: Symbol) ( c :: Symbol) (d :: Symbol)
                     (i :: Symbol) (r :: Rank) v.
               (
                SurjAreaCovRank id a b c d i ~ 'Just r,
                SingI r,
                Fractional v
               ) => Sing id -> Sing a -> Sing b -> Sing c -> Sing d -> Sing i -> Tensor r v
surjAreaCov' _ _ _ _ _ _ =
    case sLengthR sr of
      SS (SS (SS (SS (SS SZ)))) ->
        case sSane sr %~ STrue of
          Proved Refl -> fromList assocs
  where
    sr = sing :: Sing r
    tm = trianMapArea
    fm = facMapArea @v
    assocs = catMaybes $
             (\a b c d ->
                  do
                     s <- areaSign a b c d
                     let v = sortArea a b c d
                     i <- Map.lookup v tm
                     f <- Map.lookup v fm
                     return (a `VCons` (b `VCons` (c `VCons` (d `VCons` (i `VCons` VNil)))), s/f :: v))
             <$> [0..3] <*> [0..3] <*> [0..3] <*> [0..3]

_injAreaCon :: Num v => Demote Symbol -> Demote Symbol -> T v
_injAreaCon vid i =
  withSomeSing vid   $ \sid ->
  withSomeSing i     $ \si  ->
  withSomeSing " 01" $ \s01 ->
  withSomeSing " 02" $ \s02 ->
  withSomeSing " 03" $ \s03 ->
  withSomeSing " 04" $ \s04 ->
    case sInjAreaConRank sid s01 s02 s03 s04 si of
      SJust sr -> withSingI sr $ T $ injAreaCon' sid s01 s02 s03 s04 si

_injAreaCov :: Num v => Demote Symbol -> Demote Symbol -> T v
_injAreaCov vid i =
  withSomeSing vid   $ \sid ->
  withSomeSing i     $ \si  ->
  withSomeSing " 01" $ \s01 ->
  withSomeSing " 02" $ \s02 ->
  withSomeSing " 03" $ \s03 ->
  withSomeSing " 04" $ \s04 ->
    case sInjAreaCovRank sid s01 s02 s03 s04 si of
      SJust sr -> withSingI sr $ T $ injAreaCov' sid s01 s02 s03 s04 si

_surjAreaCon :: Fractional v => Demote Symbol -> Demote Symbol -> T v
_surjAreaCon vid i =
  withSomeSing vid   $ \sid ->
  withSomeSing i     $ \si  ->
  withSomeSing " 01" $ \s01 ->
  withSomeSing " 02" $ \s02 ->
  withSomeSing " 03" $ \s03 ->
  withSomeSing " 04" $ \s04 ->
    case sSurjAreaConRank sid s01 s02 s03 s04 si of
      SJust sr -> withSingI sr $ T $ surjAreaCon' sid s01 s02 s03 s04 si

_surjAreaCov :: Fractional v => Demote Symbol -> Demote Symbol -> T v
_surjAreaCov vid i =
  withSomeSing vid   $ \sid ->
  withSomeSing i     $ \si  ->
  withSomeSing " 01" $ \s01 ->
  withSomeSing " 02" $ \s02 ->
  withSomeSing " 03" $ \s03 ->
  withSomeSing " 04" $ \s04 ->
    case sSurjAreaCovRank sid s01 s02 s03 s04 si of
      SJust sr -> withSingI sr $ T $ surjAreaCov' sid s01 s02 s03 s04 si

someInjAreaCon :: forall v m.(Num v, MonadError String m) =>
                  Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol ->
                  m (T v)
someInjAreaCon vid a b c d i = relabelT (VSpace vid 4) [(" 01",a), (" 02",b), (" 03",c), (" 04",d)] t
  where
    t = _injAreaCon vid i :: T v

someInjAreaCov :: forall v m.(Num v, MonadError String m) =>
                  Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol ->
                  m (T v)
someInjAreaCov vid a b c d i = relabelT (VSpace vid 4) [(" 01",a), (" 02",b), (" 03",c), (" 04",d)] t
  where
    t = _injAreaCov vid i :: T v

someSurjAreaCon :: forall v m.(Fractional v, MonadError String m) =>
                  Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol ->
                  m (T v)
someSurjAreaCon vid a b c d i = relabelT (VSpace vid 4) [(" 01",a), (" 02",b), (" 03",c), (" 04",d)] t
  where
    t = _surjAreaCon vid i :: T v

someSurjAreaCov :: forall v m.(Fractional v, MonadError String m) =>
                  Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol ->
                  m (T v)
someSurjAreaCov vid a b c d i = relabelT (VSpace vid 4) [(" 01",a), (" 02",b), (" 03",c), (" 04",d)] t
  where
    t = _surjAreaCov vid i :: T v

someInterAreaCon :: Num v =>
                    Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol ->
                    T v
someInterAreaCon vid m n a b = t
  where
    Right t = runExcept $
      do
        j :: T (Ratio Int) <- someSurjAreaCon vid " 1" " 2" " 3" n a
        i :: T (Ratio Int) <- someInjAreaCon vid " 1" " 2" " 3" m b
        prod <- i .* j
        let res = contractT $ fmap (*(-4)) prod
        return $ fmap (\v -> if denominator v == 1
                             then fromIntegral (numerator v)
                             else error "someInterAreaCon is not fraction-free, as it should be!") res

someInterAreaCov :: Num v =>
                    Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol ->
                    T v
someInterAreaCov vid m n a b = t
  where
    Right t = runExcept $
      do
        j :: T (Ratio Int) <- someSurjAreaCov vid " 1" " 2" " 3" m a
        i :: T (Ratio Int) <- someInjAreaCov vid " 1" " 2" " 3" n b
        prod <- i .* j
        let res = contractT $ fmap (*4) prod
        return $ fmap (\v -> if denominator v == 1
                             then fromIntegral (numerator v)
                             else error "someInterAreaCov is not fraction-free, as it should be!") res

someDeltaArea :: Num v => Demote Symbol -> Demote Symbol -> Demote Symbol -> T v
someDeltaArea vid = someDelta (vid <> "Area") 21

flatAreaCon :: forall (id :: Symbol) (a :: Symbol) (r :: Rank) v.
               (
                '[ '( 'VSpace (id <> "Area") 21, 'Con (a ':| '[]))] ~ r,
                Num v
               ) => Sing id -> Sing a -> Tensor r v
flatAreaCon sid sa =
  withKnownSymbol (sid %<> (sing :: Sing "Area")) $
  withKnownSymbol sa $
  fromList [(0 `VCons` VNil, -1), (5 `VCons` VNil, 1),   --  0  1  2  3  4  5
            (6 `VCons` VNil, -1), (9 `VCons` VNil, -1),  --     6  7  8  9 10
            (11 `VCons` VNil, -1), (12 `VCons` VNil, 1), --       11 12 13 14
            (15 `VCons` VNil, 1),                        --          15 16 17
            (18 `VCons` VNil, 1),                        --             18 19
            (20 `VCons` VNil, 1)]                        --                20



someFlatAreaCon :: Num v => Demote Symbol -> Demote Symbol -> T v
someFlatAreaCon vid a =
  withSomeSing vid $ \sid ->
  withSomeSing a   $ \sa  ->
  withKnownSymbol (sid %<> (sing :: Sing "Area")) $
  withKnownSymbol sa $
  T $ flatAreaCon sid sa
