{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
-- {-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE OverloadedStrings #-}

module Ansaetze where

import qualified Math.Tensor.LorentzGenerator as LG
import qualified Math.Tensor as T

import TH
import Safe
import Tensor
import Scalar

import Data.Singletons
import Data.Singletons.Decide
import Data.Singletons.Prelude

import Data.List (sortBy)
import Data.List.NonEmpty (NonEmpty(..))
import Control.Monad.Except

makeVarsConsecutive :: [T (Poly v)] -> [T (Poly v)]
makeVarsConsecutive = go 0
  where
    go n [] = []
    go n (a:as) = fmap (shiftVars n) a : as'
      where
        vars = concat $ fmap (getVars . snd) $ toListT a
        as' = if null vars
              then go n as
              else go (n + maximum vars) as

sndOrderAnsaetze :: (Num v, Eq v, MonadError String m) => m [T (Poly v)]
sndOrderAnsaetze = do
  let ans0 = scalar $ singletonPoly 0 1 1
  let ans6 = someAns6 "ST" "A" "I"
  ans8 <- someAns8 "ST" "A" "B"
  ans10_1 <- someAns10_1 "ST" "A" "B" "I"
  ans10_2 <- someAns10_2 "ST" "A" "B" "p" "q"
  let as = makeVarsConsecutive [ans0,ans6,ans8,ans10_1,ans10_2]
  z <- zero [(VSpace "STArea" 21, Cov ("A" :| []))]
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
        Num v => Sing id -> Sing a -> Tensor (Ans4ILists id a) (Poly v)
ans4 sid sa = withSingI (sAns4ILists sid sa) $ fromList xs
  where
    (_,_,ans4) = LG.mkAnsatzTensorFastAbs 4 LG.symList4 LG.areaList4 :: (LG.AnsatzForestEta, LG.AnsatzForestEpsilon, T.ATens 0 1 0 0 0 0 T.AnsVarR)
    xs = fmap (\((_,i `T.Append` T.Empty,_,_,_,_),v) -> (T.indVal20 i `VCons` VNil,polyFromAnsVarR v)) $ T.toListT6 ans4

someAns4 :: Num v => Demote Symbol -> Demote Symbol -> T (Poly v)
someAns4 id a =
  withSomeSing id $ \sid ->
  withSomeSing a  $ \sa  ->
  withSingI (sAns4ILists sid sa) $
  T $ ans4 sid sa

ans6 :: forall (id :: Symbol) (a :: Symbol) (i :: Symbol) v.
        (
         Sane (Ans6ILists id a i) ~ 'True,
         Num v
        ) => Sing id -> Sing a -> Sing i -> Tensor (Ans6ILists id a i) (Poly v)
ans6 sid sa si = withSingI (sAns6ILists sid sa si) $ fromList xs
  where
    (_,_,ans6) = LG.mkAnsatzTensorFastAbs 6 LG.symList6 LG.areaList6 :: (LG.AnsatzForestEta, LG.AnsatzForestEpsilon, T.ATens 0 1 0 1 0 0 T.AnsVarR)
    xs = fmap (\((_,a `T.Append` T.Empty,_,i `T.Append` T.Empty,_,_),v) -> (T.indVal20 a `VCons` (T.indVal9 i `VCons` VNil),polyMap (mapSym2 (T.indVal9 i)) (polyFromAnsVarR v))) $ T.toListT6 ans6

someAns6 :: Num v => Demote Symbol -> Demote Symbol -> Demote Symbol -> T (Poly v)
someAns6 id a i =
  withSomeSing id $ \sid ->
  withSomeSing a  $ \sa  ->
  withSomeSing i  $ \si  ->
  let sl = sAns6ILists sid sa si
  in case sSane sl %~ STrue of
       Proved Refl -> withSingI sl $ T $ ans6 sid sa si

ans8 :: forall (id :: Symbol) (a :: Symbol) (b :: Symbol) (l :: ILists) v.
        (
         Ans8ILists id a b ~ 'Just l,
         Sane l ~ 'True,
         Num v
        ) => Sing id -> Sing a -> Sing b -> Tensor l (Poly v)
ans8 sid sa sb = case sAns8ILists sid sa sb of
                   SJust sl ->
                     case sLengthILs sl of
                       SS (SS SZ) -> withSingI sl $ fromList xs
  where
    (_,_,ans8) = LG.mkAnsatzTensorFastAbs 8 LG.symList8 LG.areaList8 :: (LG.AnsatzForestEta, LG.AnsatzForestEpsilon, T.ATens 0 2 0 0 0 0 T.AnsVarR)
    xs = fmap (\((_,a `T.Append` (b `T.Append` T.Empty),_,_,_,_),v) -> (T.indVal20 a `VCons` (T.indVal20 b `VCons` VNil),(polyFromAnsVarR v :: Poly v))) $ T.toListT6 ans8

someAns8 :: (MonadError String m, Num v) => Demote Symbol -> Demote Symbol -> Demote Symbol -> m (T (Poly v))
someAns8 id a b =
  withSomeSing id $ \sid ->
  withSomeSing a  $ \sa  ->
  withSomeSing b  $ \sb  ->
  case sAns8ILists sid sa sb of
         SJust sl ->
           case sSane sl %~ STrue of
             Proved Refl -> withSingI sl $ return $ T $ ans8 sid sa sb
         SNothing -> throwError $ "Illegal indices for ans8: " ++ show a ++ " " ++ show b ++ "!"

ans10_1 :: forall (id :: Symbol) (a :: Symbol) (b :: Symbol) (i :: Symbol) (l :: ILists) v.
           (
            Ans10_1ILists id a b i ~ 'Just l,
            Sane l ~ 'True,
            Num v
           ) => Sing id -> Sing a -> Sing b -> Sing i -> Tensor l (Poly v)
ans10_1 sid sa sb si = case sAns10_1ILists sid sa sb si of
                         SJust sl ->
                           case sLengthILs sl of
                             SS (SS (SS SZ)) -> withSingI sl $ fromList xs
  where
    (_,_,ans10_1) = LG.mkAnsatzTensorFastAbs 10 LG.symList10_2 LG.areaList10_2 :: (LG.AnsatzForestEta, LG.AnsatzForestEpsilon, T.ATens 0 2 0 1 0 0 T.AnsVarR)
    xs = fmap (\((_,a `T.Append` (b `T.Append` T.Empty),_,i `T.Append` T.Empty,_,_),v) -> (T.indVal20 a `VCons` (T.indVal20 b `VCons` (T.indVal9 i `VCons` VNil)),(polyMap (mapSym2 (T.indVal9 i)) (polyFromAnsVarR v) :: Poly v))) $ T.toListT6 ans10_1

someAns10_1 :: (MonadError String m, Num v) => Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol -> m (T (Poly v))
someAns10_1 id a b i =
  withSomeSing id $ \sid ->
  withSomeSing i  $ \si  ->
  withSomeSing " 01" $ \s01 ->
  withSomeSing " 02" $ \s02 ->
  case sAns10_1ILists sid s01 s02 si of
         SJust sl ->
           case sSane sl %~ STrue of
             Proved Refl ->
               let t = withSingI sl $ T $ ans10_1 sid s01 s02 si
               in relabelT (VSpace (id <> "Area") 21) [(" 01",a),(" 02",b)] t

ans10_2 :: forall (id :: Symbol) (a :: Symbol) (b :: Symbol) (p :: Symbol) (q :: Symbol) (l :: ILists) v.
           (
            Ans10_2ILists id a b p q ~ 'Just l,
            Sane l ~ 'True,
            Num v
           ) => Sing id -> Sing a -> Sing b -> Sing p -> Sing q -> Tensor l (Poly v)
ans10_2 sid sa sb sp sq = case sAns10_2ILists sid sa sb sp sq of
                            SJust sl ->
                              case sLengthILs sl of
                                SS (SS (SS (SS SZ))) -> withSingI sl $ fromList $ sortBy (\a b -> fst a `compare` fst b) xs
  where
    (_,_,ans10_2) = LG.mkAnsatzTensorFastAbs 10 LG.symList10_1 LG.areaList10_1 :: (LG.AnsatzForestEta, LG.AnsatzForestEpsilon, T.ATens 0 2 0 0 0 2 T.AnsVarR)
    xs = fmap (\((_,a `T.Append` (b `T.Append` T.Empty),_,_,_,p `T.Append` (q `T.Append` T.Empty)),v) -> (T.indVal3 p `VCons` (T.indVal3 q `VCons` (T.indVal20 a `VCons` (T.indVal20 b `VCons` VNil))),(polyMap (map2ST (T.indVal3 p) (T.indVal3 q)) (polyFromAnsVarR v) :: Poly v))) $ T.toListT6 ans10_2

someAns10_2 :: (MonadError String m, Num v) => Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol -> m (T (Poly v))
someAns10_2 id a b p q =
  withSomeSing id $ \sid ->
  withSomeSing " 01" $ \s01 ->
  withSomeSing " 02" $ \s02 ->
  withSomeSing " 03" $ \s03 ->
  withSomeSing " 04" $ \s04 ->
  case sAns10_2ILists sid s01 s02 s03 s04 of
         SJust sl ->
           case sSane sl %~ STrue of
             Proved Refl ->
               let t = withSingI sl $ T $ ans10_2 sid s01 s02 s03 s04
               in relabelT (VSpace id 4) [(" 03",p),(" 04",q)] =<< (relabelT (VSpace (id <> "Area") 21) [(" 01",a),(" 02",b)] t)

ans12 :: forall (id :: Symbol) (a :: Symbol) (b :: Symbol) (c :: Symbol) (l :: ILists) v.
         (
          Ans12ILists id a b c ~ 'Just l,
          Sane l ~ 'True,
          Num v
         ) => Sing id -> Sing a -> Sing b -> Sing c -> Tensor l (Poly v)
ans12 sid sa sb sc = case sAns12ILists sid sa sb sc of
                       SJust sl ->
                         case sLengthILs sl of
                           SS (SS (SS SZ)) -> withSingI sl $ fromList xs
  where
    (_,_,ans12) = LG.mkAnsatzTensorFastAbs 12 LG.symList12 LG.areaList12 :: (LG.AnsatzForestEta, LG.AnsatzForestEpsilon, T.ATens 0 3 0 0 0 0 T.AnsVarR)
    xs = fmap (\((_,a `T.Append` (b `T.Append` (c `T.Append` T.Empty)),_,_,_,_),v) -> (T.indVal20 a `VCons` (T.indVal20 b `VCons` (T.indVal20 c `VCons` VNil)),(polyFromAnsVarR v :: Poly v))) $ T.toListT6 ans12

someAns12 :: (MonadError String m, Num v) => Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol -> m (T (Poly v))
someAns12 id a b c =
  withSomeSing id $ \sid ->
  withSomeSing a  $ \sa  ->
  withSomeSing b  $ \sb  ->
  withSomeSing c  $ \sc  ->
  case sAns12ILists sid sa sb sc of
         SJust sl ->
           case sSane sl %~ STrue of
             Proved Refl -> withSingI sl $ return $ T $ ans12 sid sa sb sc
         SNothing -> throwError $ "Illegal indices for ans12: " ++ show a ++ " " ++ show b ++ " " ++ show c ++ "!"

ans14_1 :: forall (id :: Symbol) (a :: Symbol) (b :: Symbol) (c :: Symbol) (i :: Symbol) (l :: ILists) v.
         (
          Ans14_1ILists id a b c i ~ 'Just l,
          Sane l ~ 'True,
          Num v
         ) => Sing id -> Sing a -> Sing b -> Sing c -> Sing i -> Tensor l (Poly v)
ans14_1 sid sa sb sc si = case sAns14_1ILists sid sa sb sc si of
                            SJust sl ->
                              case sLengthILs sl of
                                SS (SS (SS (SS SZ))) -> withSingI sl $ fromList xs
  where
    (_,_,ans14_1) = LG.mkAnsatzTensorFastAbs 14 LG.symList14_2 LG.areaList14_2 :: (LG.AnsatzForestEta, LG.AnsatzForestEpsilon, T.ATens 0 3 0 1 0 0 T.AnsVarR)
    xs = fmap (\((_,a `T.Append` (b `T.Append` (c `T.Append` T.Empty)),_,i `T.Append` T.Empty,_,_),v) ->
                    (T.indVal20 a `VCons` (T.indVal20 b `VCons` (T.indVal20 c `VCons` (T.indVal9 i `VCons` VNil))),polyMap (mapSym2 (T.indVal9 i)) (polyFromAnsVarR v :: Poly v))) $ T.toListT6 ans14_1

someAns14_1 :: (MonadError String m, Num v) => Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol -> m (T (Poly v))
someAns14_1 id a b c i =
  withSomeSing id $ \sid ->
  withSomeSing i  $ \si  ->
  withSomeSing " 01" $ \s01 ->
  withSomeSing " 02" $ \s02 ->
  withSomeSing " 03" $ \s03 ->
  case sAns14_1ILists sid s01 s02 s03 si of
         SJust sl ->
           case sSane sl %~ STrue of
             Proved Refl ->
               let t = withSingI sl $ T $ ans14_1 sid s01 s02 s03 si
               in relabelT (VSpace (id <> "Area") 21) [(" 01",a),(" 02",b),(" 03",c)] t

ans14_2 :: forall (id :: Symbol) (a :: Symbol) (b :: Symbol) (c :: Symbol) (p :: Symbol) (q :: Symbol) (l :: ILists) v.
         (
          Ans14_2ILists id a b c p q ~ 'Just l,
          Sane l ~ 'True,
          Num v
         ) => Sing id -> Sing a -> Sing b -> Sing c -> Sing p -> Sing q -> Tensor l (Poly v)
ans14_2 sid sa sb sc sp sq = case sAns14_2ILists sid sa sb sc sp sq of
                               SJust sl ->
                                 case sLengthILs sl of
                                   SS (SS (SS (SS (SS SZ)))) -> withSingI sl $ fromList $ sortBy (\a b -> fst a `compare` fst b) $ xs
  where
    (_,_,ans) = LG.mkAnsatzTensorFastAbs 14 LG.symList14_1 LG.areaList14_1 :: (LG.AnsatzForestEta, LG.AnsatzForestEpsilon, T.ATens 0 3 0 0 0 2 T.AnsVarR)
    xs = fmap (\((_,a `T.Append` (b `T.Append` (c `T.Append` T.Empty)),_,_,_,p `T.Append` (q `T.Append` T.Empty)),v) ->
                    (T.indVal3 p `VCons` (T.indVal3 q `VCons` (T.indVal20 a `VCons` (T.indVal20 b `VCons` (T.indVal20 c `VCons` VNil)))),polyMap (map2ST (T.indVal3 p) (T.indVal3 q)) (polyFromAnsVarR v :: Poly v))) $ T.toListT6 ans

someAns14_2 :: (MonadError String m, Num v) =>
               Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol -> Demote Symbol -> m (T (Poly v))
someAns14_2 id a b c p q =
  withSomeSing id $ \sid ->
  withSomeSing " 01" $ \s01 ->
  withSomeSing " 02" $ \s02 ->
  withSomeSing " 03" $ \s03 ->
  withSomeSing " 04" $ \s04 ->
  withSomeSing " 05" $ \s05 ->
  case sAns14_2ILists sid s01 s02 s03 s04 s05 of
         SJust sl ->
           case sSane sl %~ STrue of
             Proved Refl ->
               let t = withSingI sl $ T $ ans14_2 sid s01 s02 s03 s04 s05
               in relabelT (VSpace id 4) [(" 04",p),(" 05",q)] =<< relabelT (VSpace (id <> "Area") 21) [(" 01",a),(" 02",b),(" 03",c)] t
