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

module TH where

import Data.Kind (Type)

import Data.Singletons.Prelude
import Data.Singletons.Prelude.List
import Data.Singletons.Prelude.List.NonEmpty hiding (sSort, SortSym0)
import Data.Singletons.Prelude.Ord
import Data.Singletons.TH

import Data.List (sort)
import Data.List.NonEmpty (NonEmpty((:|)))

$(singletons [d|
  data Nat where
      Zero :: Nat
      Succ :: Nat -> Nat

  data VSpace = VSpace { vId :: Nat,
                         vDim :: Nat }

  data Ix    = ICov Nat | ICon Nat
  
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

  deriving instance Show Ix
  deriving instance Eq Ix
  deriving instance Ord Ix

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

  isAscending :: Ord a => [a] -> Bool
  isAscending [] = True
  isAscending (x:[]) = True
  isAscending (x:y:xs) = x < y && isAscending ((y:xs))

  isAscending' :: Ord a => NonEmpty a -> Bool
  isAscending' (x :| xs) = isAscending (x:xs)

  isAscendingI :: IList -> Bool
  isAscendingI (CovCon x y) = isAscending' x && isAscending' y
  isAscendingI (Cov x) = isAscending' x
  isAscendingI (Con y) = isAscending' y

  sane :: ILists -> Bool
  sane [] = True
  sane ((_, is):[]) = isAscendingI is
  sane ((v, is):(v', is'):xs) =
      v < v' && isAscendingI is && sane ((v',is'):xs)

  head' :: ILists -> (VSpace, Ix)
  head' xs = case headMaybe xs of
               Just h -> h
               Nothing -> error "head' of empty list"

  headMaybe :: ILists -> Maybe (VSpace, Ix)
  headMaybe ((v, l):_) = Just
                         (v, case l of
                               CovCon (a :| _) _ -> ICov a
                               Cov (a :| _)      -> ICov a
                               Con (a :| _)      -> ICon a)
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
