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
import Data.Singletons.TypeLits

import Data.List (sort)
import Data.List.NonEmpty (NonEmpty((:|)))

$(singletons [d|
  data VSpace a b = VSpace { vId :: a,
                            vDim :: b }
                    deriving (Show, Ord, Eq)

  data Ix a    = ICov a | ICon a
                 deriving (Show, Ord, Eq)
  
  data IList a = CovCon (NonEmpty a) (NonEmpty a) |
                 Cov (NonEmpty a) |
                 Con (NonEmpty a)
                 deriving (Show, Ord, Eq)

  type ILists = [(VSpace Symbol Nat, IList Symbol)]

  isAscending :: Ord a => [a] -> Bool
  isAscending [] = True
  isAscending (x:[]) = True
  isAscending (x:y:xs) = x < y && isAscending ((y:xs))

  isAscending' :: Ord a => NonEmpty a -> Bool
  isAscending' (x :| xs) = isAscending (x:xs)

  isAscendingI :: Ord a => IList a -> Bool
  isAscendingI (CovCon x y) = isAscending' x && isAscending' y
  isAscendingI (Cov x) = isAscending' x
  isAscendingI (Con y) = isAscending' y

  sane :: ILists -> Bool
  sane [] = True
  sane ((_, is):[]) = isAscendingI is
  sane ((v, is):(v', is'):xs) =
      v < v' && isAscendingI is && sane ((v',is'):xs)

  head' :: ILists -> (VSpace Symbol Nat, Ix Symbol)
  head' xs = case headMaybe xs of
               Just h -> h
               Nothing -> error "head' of empty list"

  headMaybe :: ILists -> Maybe (VSpace Symbol Nat, Ix Symbol)
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

  mergeIL :: Ord a => IList a -> IList a -> IList a
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

  contractL :: ILists -> ILists
  contractL [] = []
  contractL ((v, is):xs) = case contractI is of
                             Nothing -> contractL xs
                             Just is' -> (v, is') : contractL xs

  prepICov :: a -> IList a -> IList a
  prepICov a (CovCon (x:|xs) y) = CovCon (a:|(x:xs)) y
  prepICov a (Cov (x:|xs)) = Cov (a:|(x:xs))
  prepICov a (Con y) = CovCon (a:|[]) y

  prepICon :: a -> IList a -> IList a
  prepICon a (CovCon x (y:|ys)) = CovCon (x) (a:|(y:ys))
  prepICon a (Cov x) = CovCon x (a:|[])
  prepICon a (Con (y:|ys)) = Con (a:|(y:ys))

  contractI :: Ord a => IList a -> Maybe (IList a)
  contractI (CovCon (x:|xs) (y:|ys)) =
    case compare x y of
      EQ -> case xs of
              [] -> case ys of
                      [] -> Nothing
                      (y':ys') -> Just $ Con (y' :| ys')
              (x':xs') -> case ys of
                            [] -> Just $ Cov (x' :| xs')
                            (y':ys') -> contractI $ CovCon (x':|xs') (y':|ys')
      LT -> case xs of
              [] -> Just $ CovCon (x:|xs) (y:|ys)
              (x':xs') -> case contractI $ CovCon (x':|xs') (y:|ys) of
                            Nothing -> Just $ Cov (x:|[])
                            Just i  -> Just $ prepICov x i
      GT -> case ys of
              [] -> Just $ CovCon (x:|xs) (y:|ys)
              (y':ys') -> case contractI $ CovCon (x:|xs) (y':|ys') of
                            Nothing -> Just $ Con (y:|[])
                            Just i  -> Just $ prepICon x i
  contractI (Cov x) = Just $ Cov x
  contractI (Con x) = Just $ Con x

  |])
