-- {-# LANGUAGE RankNTypes, GADTs, KindSignatures, DataKinds, TypeOperators, TypeFamilies, TemplateHaskell, TypeApplications, ScopedTypeVariables, UndecidableInstances, PolyKinds, StandaloneDeriving #-}

{-# LANGUAGE RankNTypes, KindSignatures, DataKinds, StandaloneDeriving, GADTs #-}

module Lib where

data Nat where
    Zero :: Nat
    Succ :: Nat -> Nat

deriving instance Show Nat
deriving instance Eq Nat
deriving instance Ord Nat

type Nat0 = Zero
type Nat1 = Succ Nat0
type Nat2 = Succ Nat1
type Nat3 = Succ Nat2
type Nat4 = Succ Nat3
type Nat5 = Succ Nat4
type Nat6 = Succ Nat5
type Nat7 = Succ Nat6
type Nat8 = Succ Nat7
type Nat9 = Succ Nat8
type Nat10 = Succ Nat9
type Nat11 = Succ Nat10


data Slot = Slot { slotType :: Nat,
                   slotRange :: Nat,
                   slotPos :: Bool,
                   slotId  :: Nat } deriving (Show, Eq, Ord)

data Tensor :: [Slot] -> * -> * where
    ZeroTensor :: forall (l :: [Slot]) v . Tensor l v
    Scalar :: forall (l :: [Slot]) v. l ~ '[] => v -> Tensor l v
    Tensor :: forall (l :: [Slot])
                     (l' :: [Slot])
                     (s :: Slot)
                     v.
              l ~ ('(:) s l') => [(Int, Tensor l' v)] -> Tensor l v

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

addTens' :: forall (l :: [Slot]) (l' :: [Slot]) v.
            ((l ~ l'), Num v) =>
            Tensor l v -> Tensor l' v -> Tensor l v
addTens' ZeroTensor t = t
addTens' t ZeroTensor = t
addTens' (Scalar s) (Scalar s')   = Scalar (s + s')
addTens' (Tensor xs) (Tensor xs') = Tensor xs''
    where
       xs'' = unionWith addTens' id id xs xs' 

negateTens' :: forall (l :: [Slot]) v. Num v =>
               Tensor l v -> Tensor l v
negateTens' ZeroTensor = ZeroTensor
negateTens' (Scalar s) = Scalar $ negate s
negateTens' (Tensor x) = Tensor $ fmap (fmap negateTens') x

subTens' :: forall (l :: [Slot]) (l' :: [Slot]) v.
            ((l ~ l'), Num v) =>
            Tensor l v -> Tensor l' v -> Tensor l v
subTens' t1 t2 = t1 `addTens'` (negateTens' t2)

delta :: Tensor '[ 'Slot Nat0 Nat4 'True Nat0, 'Slot Nat0 Nat4 'False Nat1] Int
delta = Tensor xs
  where
    xs = map (\i -> (i, Tensor [(i, Scalar 1)])) [0..3]

eta :: Tensor '[ 'Slot Nat0 Nat4 'True Nat0, 'Slot Nat0 Nat4 'True Nat1] Int
eta = Tensor xs
  where
    xs = map (\i -> (i, Tensor [(i, Scalar (if i == 0 then -1 else 1))])) [0..3]

someFunc :: IO ()
someFunc = putStrLn "someFunc"
