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

module Tensor where

import TH

import Data.Kind (Type)

import Data.Singletons.Prelude
import Data.Singletons.Prelude.List
import Data.Singletons.Prelude.List.NonEmpty hiding (sSort, SortSym0)
import Data.Singletons.Prelude.Ord
import Data.Singletons.TH

import Data.List (sort)
import Data.List.NonEmpty (NonEmpty((:|)))

data Tensor :: ILists -> Type -> Type where
    ZeroTensor :: forall (l :: ILists) v . Sane l ~ 'True => Tensor l v
    Scalar :: forall (l :: ILists) v.  l ~ '[] => v -> Tensor l v
    Tensor :: forall (l :: ILists)
                     (l' :: ILists)
                     v.
              (Sane l ~ 'True,
               Tail' l ~ l') =>
              [(Int, Tensor l' v)] -> Tensor l v

instance (SingI l, Show v) => Show (Tensor l v) where
  show = show . toRep

deriving instance Eq v => Eq (Tensor l v)

data IxR = ICovR Int | IConR Int deriving (Show, Ord, Eq)

data VSpaceR = VSpaceR { vIdR :: Int,
                         vDimR :: Int } deriving (Show, Ord, Eq)

data IListR = CovConR (NonEmpty Int) (NonEmpty Int) |
              CovR (NonEmpty Int) |
              ConR (NonEmpty Int) deriving (Show, Ord, Eq)

type IListsR = [(VSpaceR, IListR)]

fromIx :: Ix -> IxR
fromIx (ICov i) = ICovR $ fromN i
fromIx (ICon i) = IConR $ fromN i

toIx :: IxR -> Ix
toIx (ICovR i) = ICov $ toN i
toIx (IConR i) = ICon $ toN i

fromV :: VSpace -> VSpaceR
fromV (VSpace i d) = VSpaceR (fromN i) (fromN d)

toV :: VSpaceR -> VSpace
toV (VSpaceR i d) = VSpace (toN i) (toN d)

fromI :: IList -> IListR
fromI (CovCon xs ys) = CovConR (fmap fromN xs) (fmap fromN ys)
fromI (Cov xs)        = CovR (fmap fromN xs)
fromI (Con xs)        = ConR (fmap fromN xs)

toI :: IListR -> IList
toI (CovConR xs ys) = CovCon (fmap toN xs) (fmap toN ys)
toI (CovR xs)        = Cov (fmap toN xs)
toI (ConR xs)        = Con (fmap toN xs)

fromIs :: ILists -> IListsR
fromIs = fmap (\(v, i) -> (fromV v, fromI i))

toIs :: IListsR -> ILists
toIs = fmap (\(v, i) -> (toV v, toI i))

data TensorR :: Type -> Type where
  ZeroTensorR :: IListsR -> TensorR v
  ScalarR :: v -> TensorR v
  TensorR :: (VSpaceR, IxR) -> [(Int, TensorR v)] -> TensorR v

deriving instance Show v => Show (TensorR v)
deriving instance Eq v   => Eq (TensorR v)

toRep :: forall l v.SingI l => Tensor l v -> TensorR v
toRep ZeroTensor = let xs = fromSing (sing :: Sing l)
                   in ZeroTensorR $ fromIs xs
toRep (Scalar s) = ScalarR s
toRep (Tensor ms) = let sl     = sTail' (sing :: Sing l)
                        (v, i) = fromSing $ sHead' (sing :: Sing l)
                        ms'    = fmap (fmap (\t -> withSingI sl $ toRep t)) ms
                    in TensorR (fromV v, fromIx i) ms'

fromRep :: forall l v.SingI l => TensorR v -> Either String (Tensor l v)
fromRep (ScalarR s) = case (sing :: Sing l) of
                        SNil -> Right $ Scalar s
                        _    -> Left "cannot construct Scalar with non-empty index list"
fromRep (ZeroTensorR lr) =
  case toSing (toIs lr) of
    SomeSing sl' -> case sl' %~ (sing :: Sing l) of
      Proved Refl -> case sSane (sing :: Sing l) of
        STrue  -> Right ZeroTensor
        SFalse -> Left "insane indices in ZeroTensor"
      _           -> Left "indices in ZeroTensorR don't match type to be constructed"
fromRep (TensorR (vr, ir) ms) =
  case (sing :: Sing l) of
    SNil -> Left "cannot reconstruct Tensor with empty index list"
    _    ->
      case toSing (toV vr) of
        SomeSing sv -> case toSing (toIx ir) of
          SomeSing si -> case STuple2 sv si %~ sHead' (sing :: Sing l) of
            Proved Refl -> case sSane (sing :: Sing l) of
              STrue  ->
               let sl  = sTail' (sing :: Sing l)
                   ms' = fmap (fmap (\t -> withSingI sl $ fromRep t)) ms
                   ms'' = filter (\(_, e) -> case e of
                                               Left _ -> False
                                               Right _ -> True) ms'
                   ms''' = fmap (fmap (\e -> case e of
                                               Right t -> t)) ms''
               in case ms''' of
                    [] -> Left "empty tensor"
                    _  -> Right $ Tensor ms'''
              SFalse -> Left "insane indices in Tensor"
            _           -> Left "indices in TensorR don't match type to be constructed"

removeZeros :: (Num v, Eq v) => Tensor l v -> Tensor l v
removeZeros ZeroTensor = ZeroTensor
removeZeros (Scalar s) = if s == 0 then ZeroTensor else Scalar s
removeZeros (Tensor ms) =
    case ms' of
      [] -> ZeroTensor
      _  -> Tensor ms'
  where
    ms' = filter
     (\(_, t) ->
        case t of
          ZeroTensor -> False
          _          -> True) $
            fmap (fmap removeZeros) ms

unionWith :: (a -> b -> c) -> (a -> c) -> (b -> c) -> [(Int, a)] -> [(Int, b)] -> [(Int, c)]
unionWith _ _ f [] ys = fmap (fmap f) ys
unionWith _ f _ xs [] = fmap (fmap f) xs
unionWith f g h xs@((ix,vx):xs') ys@((iy,vy):ys')
    | ix == iy = (ix, f vx vy) : unionWith f g h xs' ys'
    | ix <  iy = (ix, g vx) : unionWith f g h xs' ys
    | ix >  iy = (iy, h vy) : unionWith f g h xs ys'

addLists :: (Num a, Eq a) => [(Int, a)] -> [(Int, a)] -> [(Int, a)]
addLists [] ys = ys
addLists xs [] = xs
addLists xs@((ix,vx):xs') ys@((iy,vy):ys')
    | ix == iy = let vz = vx + vy
                     zs = addLists xs' ys' in
                 if vz == 0
                 then zs
                 else (ix, vz) : zs
    | ix < iy = (ix, vx) : addLists xs' ys
    | ix > iy = (iy, vy) : addLists xs ys'

(&+) :: forall (l :: ILists) (l' :: ILists) v.
        ((l ~ l'), Num v, Eq v) =>
        Tensor l v -> Tensor l' v -> Tensor l v
(&+) ZeroTensor t = t
(&+) t ZeroTensor = t
(&+) (Scalar s) (Scalar s') = let s'' = s + s' in
                              if s'' == 0
                              then ZeroTensor
                              else Scalar s''
(&+) (Tensor xs) (Tensor xs') = removeZeros $ Tensor xs''
    where
       xs'' = unionWith (&+) id id xs xs' 

negateTens :: forall (l :: ILists) v. Num v =>
               Tensor l v -> Tensor l v
negateTens ZeroTensor = ZeroTensor
negateTens (Scalar s) = Scalar $ negate s
negateTens (Tensor x) = Tensor $ fmap (fmap negateTens) x

(&-) :: forall (l :: ILists) (l' :: ILists) v.
        ((l ~ l'), Num v, Eq v) =>
        Tensor l v -> Tensor l' v -> Tensor l v
(&-) t1 t2 = t1 &+ (negateTens t2)

(&*) :: forall (l :: ILists) (l' :: ILists) (l'' :: ILists) v.
               (Num v, l'' ~ MergeILs l l', Sane l'' ~ 'True,
                SingI l, SingI l') =>
               Tensor l v -> Tensor l' v -> Tensor l'' v
(&*) (Scalar s) (Scalar t) = Scalar (s*t)
(&*) (Scalar s) (Tensor ms) =
  let sl' = sTail' (sing :: Sing l')
  in case sSane sl' of
      STrue -> Tensor $ fmap (fmap (\t -> withSingI sl' $ Scalar s &* t)) ms
(&*) (Tensor ms) (Scalar s) =
  let sl = sTail' (sing :: Sing l)
  in case sSane sl of
      STrue -> Tensor $ fmap (fmap (\t -> withSingI sl $ t &* Scalar s)) ms
(&*) (Tensor ms) (Tensor ms') =
  let sl = sing :: Sing l
      sl' = sing :: Sing l'
      sh = sHead' sl
      sh' = sHead' sl'
      st = sTail' sl
      st' = sTail' sl'
      sl'' = sMergeILs sl sl'
  in case sSane sl'' of
       STrue -> case sSane (sTail' sl'') of
         STrue -> case sh of
           STuple2 sv si ->
             case sh' of
               STuple2 sv' si' ->
                 case sCompare sv sv' of
                   SLT -> case sMergeILs st sl' %~ sTail' sl'' of
                            Proved Refl -> Tensor $ fmap (fmap (\t -> withSingI st $ t &* (Tensor ms' :: Tensor l' v))) ms
                   SGT -> case sMergeILs sl st' %~ sTail' sl'' of
                            Proved Refl -> Tensor $ fmap (fmap (\t -> withSingI st' $ (Tensor ms :: Tensor l v) &* t)) ms'
                   SEQ -> case sCompare si si' of
                            SLT -> case sMergeILs st sl' %~ sTail' sl'' of
                                     Proved Refl -> Tensor $ fmap (fmap (\t -> withSingI st $ t &* (Tensor ms' :: Tensor l' v))) ms
                            SGT -> case sMergeILs sl st' %~ sTail' sl'' of
                                     Proved Refl -> Tensor $ fmap (fmap (\t -> withSingI st' $ (Tensor ms :: Tensor l v) &* t)) ms'
(&*) ZeroTensor _ = ZeroTensor
(&*) _ ZeroTensor = ZeroTensor

toList :: forall l v.SingI l => Tensor l v -> [([Int], v)]
toList ZeroTensor = []
toList (Scalar s) = [([], s)]
toList (Tensor ms) =
  let st = sTail' (sing :: Sing l)
  in case st of
       SNil -> fmap (\(i, Scalar s)  -> ([i], s)) ms
       _    -> concat $ fmap (\(i, v) -> case v of Tensor t -> fmap (\(is, v') -> (i:is, v')) (withSingI st $ toList v)) ms

delta :: forall (id :: Nat)
                (n :: Nat)
                (a :: Nat)
                (b :: Nat)
                (l :: ILists)
                v.
         (
          '[ '( 'VSpace id n, 'CovCon (a :| '[]) (b :| '[]))] ~ l,
          Different a b ~ 'True,
          Sane l ~ 'True,
          SingI n,
          NonZero n ~ 'True,
          Num v
         ) => Tensor l v
delta = case (sing :: Sing n) of
          sn -> let x = fromN (fromSing sn)
                in Tensor (f x)
  where
    f x = map (\i -> (i, Tensor [(i, Scalar 1)])) [0..x - 1]

eta :: forall (id :: Nat)
              (n :: Nat)
              (a :: Nat)
              (b :: Nat)
              (l :: ILists)
              v.
       (
        '[ '( 'VSpace id n, 'Cov (a :| '[b])) ] ~ l,
        Different a b ~ 'True,
        Sane l ~ 'True,
        SingI n,
        NonZero n ~ 'True,
        Num v
       ) => Tensor l v
eta = case (sing :: Sing n) of
        sn -> let x = fromN (fromSing sn)
              in Tensor (f x)
  where
    f x = map (\i -> (i, Tensor [(i, Scalar (if i == 0 then -1 else 1))])) [0..x - 1]

type V4 = 'VSpace 'Zero ('Succ ('Succ ('Succ ('Succ 'Zero))))
type Up2 = 'Cov ('Zero :| '[ 'Succ 'Zero])
type UpDown = 'CovCon ('Zero :| '[]) (('Succ 'Zero) :| '[])

someFunc :: IO ()
someFunc = putStrLn "someFunc"
