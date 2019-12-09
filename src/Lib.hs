-- {-# LANGUAGE RankNTypes, GADTs, KindSignatures, DataKinds, TypeOperators, TypeFamilies, TemplateHaskell, TypeApplications, ScopedTypeVariables, UndecidableInstances, PolyKinds, StandaloneDeriving, EmptyCase, InstanceSigs #-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
-- {-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}

module Lib where

import Data.Singletons.Prelude
import Data.Singletons.Prelude.List
import Data.Singletons.TH

import Data.List (sort)

$(singletons [d|
  data Nat where
      Zero :: Nat
      Succ :: Nat -> Nat
  
  data Slot = Slot { slotType :: Nat,
                     slotRange :: Nat,
                     slotId  :: Nat }
  
  type SlotLists = ([Slot], [Slot])

  n0 :: Nat
  n0 = Zero

  n1 :: Nat
  n1 = Succ n0

  n2 :: Nat
  n2 = Succ n1

  n3 :: Nat
  n3 = Succ n2

  n4 :: Nat
  n4 = Succ n3

  deriving instance Show Nat
  deriving instance Eq Nat
  deriving instance Ord Nat
  
  deriving instance Show Slot
  deriving instance Eq Slot
  deriving instance Ord Slot

  isSLEmpty :: SlotLists -> Bool
  isSLEmpty (xs, ys) = null xs && null ys

  slHeadTail :: SlotLists -> (Slot, SlotLists)
  slHeadTail (xs, ys) =
    case xs of
      (x : xs') -> (x, (xs', ys))
      []        -> case ys of
                   (y : ys') -> (y, (xs, ys'))
                   []        -> undefined

  labels :: [Slot] -> [Nat]
  labels = map (\(Slot _ _ l) -> l)

  hasDuplicates :: (Ord a, Eq a) => [a] -> Bool
  hasDuplicates = hasDuplicates' . sort
  
  hasDuplicates' :: Eq a => [a] -> Bool
  hasDuplicates' [] = False
  hasDuplicates' (x:[]) = False
  hasDuplicates' (x:y:xs) = (x == y) || hasDuplicates' (y : xs)

  saneLabels :: SlotLists -> Bool
  saneLabels (xs, ys) = not $ hasDuplicates xs' || hasDuplicates ys'
    where
      xs' = labels xs
      ys' = labels ys

  addSLLists :: SlotLists -> SlotLists -> SlotLists
  addSLLists (xs, ys) (xs', ys') = (xs ++ xs', ys ++ ys')

  sortSLLists :: SlotLists -> SlotLists
  sortSLLists (xs, ys) = (sort xs, sort ys)
  |])

data Tensor :: SlotLists -> * -> * where
    ZeroTensor :: forall (l :: SlotLists) v . SaneLabels l ~ 'True => Tensor l v
    Scalar :: forall (l :: SlotLists) v. (SaneLabels l ~ 'True, l ~ '( '[], '[])) => v -> Tensor l v
    Tensor :: forall (l :: SlotLists)
                     (l' :: SlotLists)
                     (s :: Slot)
                     v.
              ('(s, l') ~ SlHeadTail l,
               SaneLabels l ~ 'True) =>
              [(Int, Tensor l' v)] -> Tensor l v

deriving instance Show v => Show (Tensor k v)

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

addTens' :: forall (l :: SlotLists) (l' :: SlotLists) v.
            ((l ~ l'), Num v) =>
            Tensor l v -> Tensor l' v -> Tensor l v
addTens' ZeroTensor t = t
addTens' t ZeroTensor = t
addTens' (Scalar s) (Scalar s')   = Scalar (s + s')
addTens' (Tensor xs) (Tensor xs') = Tensor xs''
    where
       xs'' = unionWith addTens' id id xs xs' 

negateTens' :: forall (l :: SlotLists) v. Num v =>
               Tensor l v -> Tensor l v
negateTens' ZeroTensor = ZeroTensor
negateTens' (Scalar s) = Scalar $ negate s
negateTens' (Tensor x) = Tensor $ fmap (fmap negateTens') x

subTens' :: forall (l :: SlotLists) (l' :: SlotLists) v.
            ((l ~ l'), Num v) =>
            Tensor l v -> Tensor l' v -> Tensor l v
subTens' t1 t2 = t1 `addTens'` (negateTens' t2)

prodTens' :: forall (l :: SlotLists) (l' :: SlotLists) (l'' :: SlotLists) v.
             (Num v, l'' ~ AddSLLists l l', SaneLabels l'' ~ 'True) =>
             Tensor l v -> Tensor l' v -> Tensor l'' v
prodTens' _ _ = ZeroTensor

toListTens :: forall (l :: SlotLists) v.
              (SaneLabels l ~ 'True, SingI l) =>
              Tensor l v -> [(([(Slot, Int)], [(Slot, Int)]), v)]
toListTens ZeroTensor = []
toListTens (Scalar s) = [(([], []), s)]
toListTens (Tensor ms) = case sFst (sSlHeadTail (sing :: Sing l)) of
    slot -> [(([(fromSing slot, 0)], []), undefined)]

delta :: Tensor '( '[ 'Slot N0 N4 N0], '[ 'Slot N0 N4 N1]) Int
delta = Tensor xs
  where
    xs = map (\i -> (i, Tensor [(i, Scalar 1)])) [0..3]

eta :: Tensor '( '[ 'Slot N0 N4 N0, 'Slot N0 N4 N1], '[]) Int
eta = Tensor xs
  where
    xs = map (\i -> (i, Tensor [(i, Scalar (if i == 0 then -1 else 1))])) [0..3]

someFunc :: IO ()
someFunc = putStrLn "someFunc"
