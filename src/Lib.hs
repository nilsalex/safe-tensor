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

module Lib where

import Data.Kind (Type)

import Data.Singletons.Prelude
import Data.Singletons.Prelude.List
import Data.Singletons.Prelude.List.NonEmpty hiding (sSort, SortSym0)
import Data.Singletons.TH

import Data.List (sort)
import Data.List.NonEmpty (NonEmpty((:|)))

$(singletons [d|
  data Nat where
      Zero :: Nat
      Succ :: Nat -> Nat

  data VSpace = VSpace { vId :: Nat,
                         vDim :: Nat }
  
  data IList = CovCon (NonEmpty Nat) (NonEmpty Nat) |
               Cov (NonEmpty Nat) |
               Con (NonEmpty Nat)

  type ILists = [(VSpace, IList)]

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
  
  deriving instance Show VSpace
  deriving instance Eq VSpace
  deriving instance Ord VSpace

  deriving instance Show IList
  deriving instance Eq IList
  deriving instance Ord IList

  nonZero :: Nat -> Bool
  nonZero Zero     = False
  nonZero (Succ n) = True

  pred' :: Nat -> Nat
  pred' (Succ n) = n
  pred' Zero = error "predecessor of Zero"

  different :: Nat -> Nat -> Bool
  different Zero Zero = False
  different Zero (Succ n) = True
  different (Succ n) Zero = True
  different (Succ n) (Succ m) = different n m

  isAscending' :: Ord a => NonEmpty a -> Bool
  isAscending' (x :| xs) = isAscending (x:xs)

  isAscending :: Ord a => [a] -> Bool
  isAscending []   = True
  isAscending (x:[]) = True
  isAscending (x:y:xs) = x < y && isAscending (y:xs)

  sane :: ILists -> Bool
  sane xs = isAscending (fmap fst xs) && all ascending (fmap snd xs)
    where
      ascending (CovCon x y) = isAscending' x && isAscending' y
      ascending (Cov x) = isAscending' x
      ascending (Con y) = isAscending' y

  head' :: ILists -> (VSpace, Nat)
  head' xs = case headMaybe xs of
               Just h -> h
               Nothing -> error "head' of empty list"

  headMaybe :: ILists -> Maybe (VSpace, Nat)
  headMaybe ((v, l):_) = Just
                         (v, case l of
                               CovCon (a :| _) _ -> a
                               Cov (a :| _)      -> a
                               Con (a :| _)      -> a)
  headMaybe [] = Nothing

  tail' :: ILists -> ILists
  tail' xs = case tailMaybe xs of
               Just xs' -> xs'
               Nothing  -> error "tail' of empty list"

  tailMaybe :: ILists -> Maybe ILists
  tailMaybe ((v, l):ls) =
    let l' = case l of
               CovCon (a :| []) bs -> Just $ Con bs
               CovCon (a :| (a':as)) bs -> Just $ CovCon (a' :| as) bs

               Cov (a :| []) -> Nothing
               Cov (a :| (a':as)) -> Just $ Cov (a' :| as)

               Con (a :| []) -> Nothing
               Con (a :| (a':as)) -> Just $ Con (a' :| as)
             in case l' of
                  Just l'' -> Just $ (v, l''):ls
                  Nothing  -> Just ls
  tailMaybe [] = Nothing

  mergeILs :: ILists -> ILists -> ILists
  mergeILs [] ys = ys
  mergeILs xs [] = xs
  mergeILs ((xv,xl):xs) ((yv,yl):ys) = 
    if xv < yv
    then (xv,xl) : mergeILs xs ((yv,yl):ys)
    else if yv > xv
         then (yv,yl) : mergeILs ((xv,xl):xs) ys
         else (xv, mergeIL xl yl) : mergeILs xs ys

  mergeIL :: IList -> IList -> IList
  mergeIL (CovCon xs ys) (CovCon xs' ys') = 
    CovCon (mergeNE xs xs') (mergeNE ys ys')
  mergeIL (CovCon xs ys) (Cov xs') = CovCon (mergeNE xs xs') ys
  mergeIL (CovCon xs ys) (Con ys') = CovCon xs (mergeNE ys ys')
  mergeIL (Cov xs) (CovCon xs' ys) = CovCon (mergeNE xs xs') ys
  mergeIL (Cov xs) (Cov xs') = Cov (mergeNE xs xs')
  mergeIL (Cov xs) (Con ys) = CovCon xs ys
  mergeIL (Con ys) (CovCon xs ys') = CovCon xs (mergeNE ys ys')
  mergeIL (Con ys) (Cov xs) = CovCon xs ys
  mergeIL (Con ys) (Con ys') = Con (mergeNE ys ys')

  merge :: Ord a => [a] -> [a] -> [a]
  merge [] ys = ys
  merge xs [] = xs
  merge (x:xs) (y:ys) =
    if x < y
    then x : merge xs (y:ys)
    else if x > y
         then y : merge (x:xs) ys
         else error "merging overlapping lists"

  mergeNE :: Ord a => NonEmpty a -> NonEmpty a -> NonEmpty a
  mergeNE (x :| xs) (y :| ys) =
    if x < y
    then x :| merge xs (y:ys)
    else if x > y
         then y :| merge (x:xs) ys
         else error "merging overlapping non-empty lists"

  |])
  
fromN :: Nat -> Int
fromN Zero = 0
fromN (Succ n) = 1 + fromN n

toN :: Int -> Nat
toN 0 = Zero
toN n = Succ (toN (n-1))

data Tensor :: ILists -> Type -> Type where
    ZeroTensor :: forall (l :: ILists) v . Sane l ~ 'True => Tensor l v
    Scalar :: forall (l :: ILists) v. (Sane l ~ 'True, l ~ '[]) => v -> Tensor l v
    Tensor :: forall (l :: ILists)
                     (l' :: ILists)
                     v.
              (Sane l ~ 'True,
               Tail' l ~ l') =>
              [(Int, Tensor l' v)] -> Tensor l v

instance (SingI l, Show v) => Show (Tensor l v) where
  show = show . toRep

deriving instance Eq v => Eq (Tensor l v)

data VSpaceR = VSpaceR { vIdR :: Int,
                         vDimR :: Int } deriving (Show, Ord, Eq)

data IListR = CovConR (NonEmpty Int) (NonEmpty Int) |
              CovR (NonEmpty Int) |
              ConR (NonEmpty Int) deriving (Show, Ord, Eq)

type IListsR = [(VSpaceR, IListR)]

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
  TensorR :: (VSpaceR, Int) -> [(Int, TensorR v)] -> TensorR v

deriving instance Show v => Show (TensorR v)
deriving instance Eq v   => Eq (TensorR v)

toRep :: forall l v.SingI l => Tensor l v -> TensorR v
toRep ZeroTensor = let xs = fromSing (sing :: Sing l)
                   in ZeroTensorR $ fromIs xs
toRep (Scalar s) = ScalarR s
toRep (Tensor ms) = let sl     = sTail' (sing :: Sing l)
                        (v, i) = fromSing $ sHead' (sing :: Sing l)
                        ms'    = fmap (fmap (\t -> withSingI sl $ toRep t)) ms
                    in TensorR (fromV v, fromN i) ms'

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
        SomeSing sv -> case toSing (toN ir) of
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
               (Num v, l'' ~ MergeILs l l', Sane l'' ~ 'True) =>
               Tensor l v -> Tensor l' v -> Tensor l'' v
(&*) _ _ = ZeroTensor

{-
toListTens :: forall (l :: SlotLists) v.
              (SaneLabels l ~ 'True, SingI l) =>
              Tensor l v -> [(([(Slot, Int)], [(Slot, Int)]), v)]
toListTens ZeroTensor = []
toListTens (Scalar s) = [(([], []), s)]
toListTens (Tensor ms) = case sFst (sSlHeadTail (sing :: Sing l)) of
    slot -> [(([(fromSing slot, 0)], []), undefined)]
-}

delta :: forall (id :: Nat)
                (n :: Nat)
                (a :: Nat)
                (b :: Nat)
                (l :: ILists)
                v.
         (
          '[ '( 'VSpace id n, 'CovCon (a :| '[]) (b :| '[]))] ~ l,
--          Different a b ~ 'True,
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
