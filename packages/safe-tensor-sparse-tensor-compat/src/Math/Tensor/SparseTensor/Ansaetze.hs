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
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE TypeApplications #-}

-----------------------------------------------------------------------------
{-|
Module      : Math.Tensor.SparseTensor.Ansaetze
Description : Ansaetze from the sparse-tensor package.
Copyright   : (c) Nils Alex, 2020
License     : MIT
Maintainer  : nils.alex@fau.de
Stability   : experimental

Ansaetze from the @sparse-tensor@ module 'Math.Tensor.LorentzGenerator',
converted and exported for usage with @safe-tensor@.
-}
-----------------------------------------------------------------------------
module Math.Tensor.SparseTensor.Ansaetze
  ( sndOrderAnsaetze
  , makeVarsConsecutive
  , ans4
  , ans6
  , ans8
  , ans10_1
  , ans10_2
  , ans12
  , ans14_1
  , ans14_2
  , someAns4
  , someAns6
  , someAns8
  , someAns10_1
  , someAns10_2
  , someAns12
  , someAns14_1
  , someAns14_2
  ) where

import Math.Tensor.SparseTensor.Ansaetze.TH

import qualified "sparse-tensor" Math.Tensor.LorentzGenerator as LG
import qualified "sparse-tensor" Math.Tensor as T

import "safe-tensor" Math.Tensor
import "safe-tensor" Math.Tensor.Safe
import "safe-tensor" Math.Tensor.Safe.TH
import "safe-tensor" Math.Tensor.LinearAlgebra.Scalar

import Data.Singletons
import Data.Singletons.Decide
import Data.Singletons.Prelude

import Data.List (sortBy)
import Data.List.NonEmpty (NonEmpty(..))
import Control.Monad.Except
import qualified Data.IntMap.Strict as IM
import Data.Ratio (numerator, denominator)

polyFromAnsVarR :: Num a => T.AnsVarR -> Poly a
polyFromAnsVarR (T.AnsVar im)
  | IM.null im = Const 0
  | otherwise   = Affine 0 (Lin $ IM.map (\(T.SField x) -> if   denominator x == 1
                                                         then fromIntegral (numerator x)
                                                         else error "Cannot convert from rational.") im)

makeVarsConsecutive :: forall v.[T (Poly v)] -> [T (Poly v)]
makeVarsConsecutive = go 0
  where
    go :: Int -> [T (Poly v)] -> [T (Poly v)]
    go _ [] = []
    go n (a:as) = fmap (shiftVars n) a : as'
      where
        vars = concatMap (getVars . snd) $ toListT a
        as' = if null vars
              then go n as
              else go (n + maximum vars) as

sndOrderAnsaetze :: forall m v.(Num v, MonadError String m) => m [T (Poly v)]
sndOrderAnsaetze = do
  let a0 :: T (Poly v) = scalarT $ singletonPoly 0 1 1
  let a6 :: T (Poly v) = someAns6 "ST" "A" "I"
  a8 <- someAns8 "ST" "A" "B"
  a10_1 <- someAns10_1 "ST" "A" "B" "I"
  a10_2 <- someAns10_2 "ST" "A" "B" "p" "q"
  let as = makeVarsConsecutive [a0,a6,a8,a10_1,a10_2]
  z <- zeroT [(VSpace "STArea" 21, Cov ("A" :| []))]
  return $ z : as

mapSym2 :: Num v => Int -> (v -> v)
mapSym2 1 = negate
mapSym2 2 = negate
mapSym2 3 = negate
mapSym2 _ = id

map2ST :: Num v => Int -> Int -> (v -> v)
map2ST p q
  | p == q = id
  | p == 0 || q == 0 = negate
  | otherwise = id

ans4 :: forall (id :: Symbol) (a :: Symbol) v.
        Num v => Sing id -> Sing a -> Tensor (Ans4Rank id a) (Poly v)
ans4 sid sa = withSingI (sAns4Rank sid sa) $ fromList xs
  where
    (_,_,a4) = LG.mkAnsatzTensorFastAbs 4 LG.symList4 LG.areaList4 :: (LG.AnsatzForestEta, LG.AnsatzForestEpsilon, T.ATens 0 1 0 0 0 0 T.AnsVarR)
    xs = (\((_,i `T.Append` T.Empty,_,_,_,_),v) -> (T.indVal20 i `VCons` VNil,polyFromAnsVarR @v v)) <$> T.toListT6 a4

someAns4 :: Num v => Demote Symbol -> Demote Symbol -> T (Poly v)
someAns4 vid a =
  withSomeSing vid $ \sid ->
  withSomeSing a  $  \sa  ->
  withSingI (sAns4Rank sid sa) $
  T $ ans4 sid sa

ans6 :: forall (id :: Symbol) (a :: Symbol) (i :: Symbol) v.
        (
         Sane (Ans6Rank id a i) ~ 'True,
         Num v
        ) => Sing id -> Sing a -> Sing i -> Tensor (Ans6Rank id a i) (Poly v)
ans6 sid sa si = withSingI (sAns6Rank sid sa si) $ fromList xs
  where
    (_,_,a6) = LG.mkAnsatzTensorFastAbs 6 LG.symList6 LG.areaList6 :: (LG.AnsatzForestEta, LG.AnsatzForestEpsilon, T.ATens 0 1 0 1 0 0 T.AnsVarR)
    xs = (\((_,a `T.Append` T.Empty,_,i `T.Append` T.Empty,_,_),v) -> (T.indVal20 a `VCons` (T.indVal9 i `VCons` VNil),polyMap (mapSym2 (T.indVal9 i)) (polyFromAnsVarR @v v))) <$> T.toListT6 a6

someAns6 :: Num v => Demote Symbol -> Demote Symbol -> Demote Symbol -> T (Poly v)
someAns6 vid a i =
  withSomeSing vid $ \sid ->
  withSomeSing a  $  \sa  ->
  withSomeSing i  $  \si  ->
  let sl = sAns6Rank sid sa si
  in case sSane sl %~ STrue of
       Proved Refl -> withSingI sl $ T $ ans6 sid sa si

ans8 :: forall (id :: Symbol) (a :: Symbol) (b :: Symbol) (l :: Rank) v.
        (
         Ans8Rank id a b ~ 'Just l,
         Sane l ~ 'True,
         Num v
        ) => Sing id -> Sing a -> Sing b -> Tensor l (Poly v)
ans8 sid sa sb = case sAns8Rank sid sa sb of
                   SJust sl ->
                     case sLengthR sl of
                       SS (SS SZ) -> withSingI sl $ fromList xs
  where
    (_,_,a8) = LG.mkAnsatzTensorFastAbs 8 LG.symList8 LG.areaList8 :: (LG.AnsatzForestEta, LG.AnsatzForestEpsilon, T.ATens 0 2 0 0 0 0 T.AnsVarR)
    xs = (\((_,a `T.Append` (b `T.Append` T.Empty),_,_,_,_),v) -> (T.indVal20 a `VCons` (T.indVal20 b `VCons` VNil),polyFromAnsVarR @v v)) <$> T.toListT6 a8

someAns8 :: (MonadError String m, Num v) => Demote Symbol -> Demote Symbol -> Demote Symbol -> m (T (Poly v))
someAns8 vid a b =
  withSomeSing vid $ \sid ->
  withSomeSing a  $  \sa  ->
  withSomeSing b  $  \sb  ->
  case sAns8Rank sid sa sb of
         SJust sl ->
           case sSane sl %~ STrue of
             Proved Refl -> withSingI sl $ return $ T $ ans8 sid sa sb
         SNothing -> throwError $ "Illegal indices for ans8: " ++ show a ++ " " ++ show b ++ "!"

ans10_1 :: forall (id :: Symbol) (a :: Symbol) (b :: Symbol) (i :: Symbol) (l :: Rank) v.
           (
            Ans10_1Rank id a b i ~ 'Just l,
            Sane l ~ 'True,
            Num v
           ) => Sing id -> Sing a -> Sing b -> Sing i -> Tensor l (Poly v)
ans10_1 sid sa sb si = case sAns10_1Rank sid sa sb si of
                         SJust sl ->
                           case sLengthR sl of
                             SS (SS (SS SZ)) -> withSingI sl $ fromList xs
  where
    (_,_,a10_1) = LG.mkAnsatzTensorFastAbs 10 LG.symList10_2 LG.areaList10_2 :: (LG.AnsatzForestEta, LG.AnsatzForestEpsilon, T.ATens 0 2 0 1 0 0 T.AnsVarR)
    xs = (\((_,a `T.Append` (b `T.Append` T.Empty),_,i `T.Append` T.Empty,_,_),v) -> (T.indVal20 a `VCons` (T.indVal20 b `VCons` (T.indVal9 i `VCons` VNil)),polyMap (mapSym2 (T.indVal9 i)) (polyFromAnsVarR @v v))) <$> T.toListT6 a10_1

someAns10_1 :: (MonadError String m, Num v) => Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol -> m (T (Poly v))
someAns10_1 vid a b i =
  withSomeSing vid $ \sid ->
  withSomeSing i   $ \si  ->
  withSomeSing " 01" $ \s01 ->
  withSomeSing " 02" $ \s02 ->
  case sAns10_1Rank sid s01 s02 si of
         SJust sl ->
           case sSane sl %~ STrue of
             Proved Refl ->
               let t = withSingI sl $ T $ ans10_1 sid s01 s02 si
               in relabelT (VSpace (vid <> "Area") 21) [(" 01",a),(" 02",b)] t

ans10_2 :: forall (id :: Symbol) (a :: Symbol) (b :: Symbol) (p :: Symbol) (q :: Symbol) (l :: Rank) v.
           (
            Ans10_2Rank id a b p q ~ 'Just l,
            Sane l ~ 'True,
            Num v
           ) => Sing id -> Sing a -> Sing b -> Sing p -> Sing q -> Tensor l (Poly v)
ans10_2 sid sa sb sp sq = case sAns10_2Rank sid sa sb sp sq of
                            SJust sl ->
                              case sLengthR sl of
                                SS (SS (SS (SS SZ))) -> withSingI sl $ fromList $ sortBy (\a b -> fst a `compare` fst b) xs
  where
    (_,_,a10_2) = LG.mkAnsatzTensorFastAbs 10 LG.symList10_1 LG.areaList10_1 :: (LG.AnsatzForestEta, LG.AnsatzForestEpsilon, T.ATens 0 2 0 0 0 2 T.AnsVarR)
    xs = (\((_,a `T.Append` (b `T.Append` T.Empty),_,_,_,p `T.Append` (q `T.Append` T.Empty)),v) -> (T.indVal3 p `VCons` (T.indVal3 q `VCons` (T.indVal20 a `VCons` (T.indVal20 b `VCons` VNil))),polyMap (map2ST (T.indVal3 p) (T.indVal3 q)) (polyFromAnsVarR @v v))) <$> T.toListT6 a10_2

someAns10_2 :: (MonadError String m, Num v) => Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol -> m (T (Poly v))
someAns10_2 vid a b p q =
  withSomeSing vid $ \sid ->
  withSomeSing " 01" $ \s01 ->
  withSomeSing " 02" $ \s02 ->
  withSomeSing " 03" $ \s03 ->
  withSomeSing " 04" $ \s04 ->
  case sAns10_2Rank sid s01 s02 s03 s04 of
         SJust sl ->
           case sSane sl %~ STrue of
             Proved Refl ->
               let t = withSingI sl $ T $ ans10_2 sid s01 s02 s03 s04
               in relabelT (VSpace vid 4) [(" 03",p),(" 04",q)] =<< relabelT (VSpace (vid <> "Area") 21) [(" 01",a),(" 02",b)] t

ans12 :: forall (id :: Symbol) (a :: Symbol) (b :: Symbol) (c :: Symbol) (l :: Rank) v.
         (
          Ans12Rank id a b c ~ 'Just l,
          Sane l ~ 'True,
          Num v
         ) => Sing id -> Sing a -> Sing b -> Sing c -> Tensor l (Poly v)
ans12 sid sa sb sc = case sAns12Rank sid sa sb sc of
                       SJust sl ->
                         case sLengthR sl of
                           SS (SS (SS SZ)) -> withSingI sl $ fromList xs
  where
    (_,_,a12) = LG.mkAnsatzTensorFastAbs 12 LG.symList12 LG.areaList12 :: (LG.AnsatzForestEta, LG.AnsatzForestEpsilon, T.ATens 0 3 0 0 0 0 T.AnsVarR)
    xs = (\((_,a `T.Append` (b `T.Append` (c `T.Append` T.Empty)),_,_,_,_),v) -> (T.indVal20 a `VCons` (T.indVal20 b `VCons` (T.indVal20 c `VCons` VNil)),polyFromAnsVarR @v v)) <$> T.toListT6 a12

someAns12 :: (MonadError String m, Num v) => Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol -> m (T (Poly v))
someAns12 vid a b c =
  withSomeSing vid $ \sid ->
  withSomeSing a   $ \sa  ->
  withSomeSing b   $ \sb  ->
  withSomeSing c   $ \sc  ->
  case sAns12Rank sid sa sb sc of
         SJust sl ->
           case sSane sl %~ STrue of
             Proved Refl -> withSingI sl $ return $ T $ ans12 sid sa sb sc
         SNothing -> throwError $ "Illegal indices for ans12: " ++ show a ++ " " ++ show b ++ " " ++ show c ++ "!"

ans14_1 :: forall (id :: Symbol) (a :: Symbol) (b :: Symbol) (c :: Symbol) (i :: Symbol) (l :: Rank) v.
         (
          Ans14_1Rank id a b c i ~ 'Just l,
          Sane l ~ 'True,
          Num v
         ) => Sing id -> Sing a -> Sing b -> Sing c -> Sing i -> Tensor l (Poly v)
ans14_1 sid sa sb sc si = case sAns14_1Rank sid sa sb sc si of
                            SJust sl ->
                              case sLengthR sl of
                                SS (SS (SS (SS SZ))) -> withSingI sl $ fromList xs
  where
    (_,_,a14_1) = LG.mkAnsatzTensorFastAbs 14 LG.symList14_2 LG.areaList14_2 :: (LG.AnsatzForestEta, LG.AnsatzForestEpsilon, T.ATens 0 3 0 1 0 0 T.AnsVarR)
    xs = (\((_,a `T.Append` (b `T.Append` (c `T.Append` T.Empty)),_,i `T.Append` T.Empty,_,_),v) ->
                    (T.indVal20 a `VCons` (T.indVal20 b `VCons` (T.indVal20 c `VCons` (T.indVal9 i `VCons` VNil))),polyMap (mapSym2 (T.indVal9 i)) (polyFromAnsVarR @v v))) <$> T.toListT6 a14_1

someAns14_1 :: (MonadError String m, Num v) => Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol -> m (T (Poly v))
someAns14_1 vid a b c i =
  withSomeSing vid $ \sid ->
  withSomeSing i   $ \si  ->
  withSomeSing " 01" $ \s01 ->
  withSomeSing " 02" $ \s02 ->
  withSomeSing " 03" $ \s03 ->
  case sAns14_1Rank sid s01 s02 s03 si of
         SJust sl ->
           case sSane sl %~ STrue of
             Proved Refl ->
               let t = withSingI sl $ T $ ans14_1 sid s01 s02 s03 si
               in relabelT (VSpace (vid <> "Area") 21) [(" 01",a),(" 02",b),(" 03",c)] t

ans14_2 :: forall (id :: Symbol) (a :: Symbol) (b :: Symbol) (c :: Symbol) (p :: Symbol) (q :: Symbol) (l :: Rank) v.
         (
          Ans14_2Rank id a b c p q ~ 'Just l,
          Sane l ~ 'True,
          Num v
         ) => Sing id -> Sing a -> Sing b -> Sing c -> Sing p -> Sing q -> Tensor l (Poly v)
ans14_2 sid sa sb sc sp sq = case sAns14_2Rank sid sa sb sc sp sq of
                               SJust sl ->
                                 case sLengthR sl of
                                   SS (SS (SS (SS (SS SZ)))) -> withSingI sl $ fromList $ sortBy (\a b -> fst a `compare` fst b) xs
  where
    (_,_,a14_2) = LG.mkAnsatzTensorFastAbs 14 LG.symList14_1 LG.areaList14_1 :: (LG.AnsatzForestEta, LG.AnsatzForestEpsilon, T.ATens 0 3 0 0 0 2 T.AnsVarR)
    xs = (\((_,a `T.Append` (b `T.Append` (c `T.Append` T.Empty)),_,_,_,p `T.Append` (q `T.Append` T.Empty)),v) ->
                    (T.indVal3 p `VCons` (T.indVal3 q `VCons` (T.indVal20 a `VCons` (T.indVal20 b `VCons` (T.indVal20 c `VCons` VNil)))),polyMap (map2ST (T.indVal3 p) (T.indVal3 q)) (polyFromAnsVarR @v v))) <$> T.toListT6 a14_2

someAns14_2 :: (MonadError String m, Num v) =>
               Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol -> m (T (Poly v))
someAns14_2 vid a b c p q =
  withSomeSing vid $ \sid ->
  withSomeSing " 01" $ \s01 ->
  withSomeSing " 02" $ \s02 ->
  withSomeSing " 03" $ \s03 ->
  withSomeSing " 04" $ \s04 ->
  withSomeSing " 05" $ \s05 ->
  case sAns14_2Rank sid s01 s02 s03 s04 s05 of
         SJust sl ->
           case sSane sl %~ STrue of
             Proved Refl ->
               let t = withSingI sl $ T $ ans14_2 sid s01 s02 s03 s04 s05
               in relabelT (VSpace vid 4) [(" 04",p),(" 05",q)] =<< relabelT (VSpace (vid <> "Area") 21) [(" 01",a),(" 02",b),(" 03",c)] t
