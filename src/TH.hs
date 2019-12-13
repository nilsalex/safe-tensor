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

  data Ix a    = ICov a | ICon a deriving (Show, Ord, Eq)

  ixCompare :: Ord a => Ix a -> Ix a -> Ordering
  ixCompare (ICov a) (ICov b) = compare a b
  ixCompare (ICov a) (ICon b) = case compare a b of
                                  LT -> LT
                                  EQ -> LT
                                  GT -> GT
  ixCompare (ICon a) (ICov b) = case compare a b of
                                  LT -> LT
                                  EQ -> GT
                                  GT -> GT
  ixCompare (ICon a) (ICon b) = compare a b
  
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
  head' ((v, l):_) = (v, case l of
                           CovCon (a :| _) (b :| _) ->
                             case compare a b of
                               LT -> ICov a
                               EQ -> ICov a
                               GT -> ICon b
                           Cov (a :| _)      -> ICov a
                           Con (a :| _)      -> ICon a)
  head' [] = error "head' of empty list"

  tail' :: ILists -> ILists
  tail' ((v, l):ls) =
    let l' = case l of
               CovCon (a :| []) (b :| []) ->
                 case compare a b of
                   LT -> Just $ Con (b :| [])
                   EQ -> Just $ Con (b :| [])
                   GT -> Just $ Cov (a :| [])

               CovCon (a :| (a':as)) (b :| []) ->
                 case compare a b of
                   LT -> Just $ CovCon (a' :| as) (b :| [])
                   EQ -> Just $ CovCon (a' :| as) (b :| [])
                   GT -> Just $ Cov (a :| (a':as))

               CovCon (a :| []) (b :| (b':bs)) ->
                 case compare a b of
                   LT -> Just $ Con (b :| (b':bs))
                   EQ -> Just $ Con (b :| (b':bs))
                   GT -> Just $ CovCon (a :| []) (b' :| bs)

               CovCon (a :| (a':as)) (b :| (b':bs)) ->
                 case compare a b of
                   LT -> Just $ CovCon (a' :| as) (b :| (b':bs))
                   EQ -> Just $ CovCon (a' :| as) (b :| (b':bs))
                   GT -> Just $ CovCon (a :| (a':as)) (b' :| bs)

               Cov (a :| []) -> Nothing
               Cov (a :| (a':as)) -> Just $ Cov (a' :| as)

               Con (a :| []) -> Nothing
               Con (a :| (a':as)) -> Just $ Con (a' :| as)
             in case l' of
                  Just l'' -> (v, l''):ls
                  Nothing  -> ls
  tail' [] = error "tail' of empty list"

  mergeILs :: ILists -> ILists -> ILists
  mergeILs [] ys = ys
  mergeILs xs [] = xs
  mergeILs ((xv,xl):xs) ((yv,yl):ys) = 
    case compare xv yv of
      LT -> (xv,xl) : mergeILs xs ((yv,yl):ys)
      EQ -> (xv, mergeIL xl yl) : mergeILs xs ys
      GT -> (yv,yl) : mergeILs ((xv,xl):xs) ys

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
    case compare x y of
      LT -> x : merge xs (y:ys)
      EQ -> error "merging overlapping lists"
      GT -> y : merge (x:xs) ys

  mergeNE :: Ord a => NonEmpty a -> NonEmpty a -> NonEmpty a
  mergeNE (x :| xs) (y :| ys) =
    case compare x y of
      LT -> x :| merge xs (y:ys)
      EQ -> error "merging overlapping non-empty lists"
      GT -> y :| merge (x:xs) ys

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

  elemNE :: Ord a => a -> NonEmpty a -> Bool
  elemNE a (x :| []) = a == x
  elemNE a (x :| (x':xs)) = case compare a x of
                              LT -> False
                              EQ -> True
                              GT -> elemNE a (x' :| xs)
  
  canTransposeCov :: (Ord a, Ord b) => VSpace a b -> a -> a -> [(VSpace a b, IList a)] -> Bool
  canTransposeCov _ _ _ [] = False
  canTransposeCov v a b ((v',il):ls) =
    case compare v v' of
      LT -> False
      GT -> canTransposeCov v a b ls
      EQ -> case il of
              Con _  -> canTransposeCov v a b ls
              Cov cs -> case elemNE a cs of
                          True -> case elemNE b cs of
                                    True -> True
                                    False -> False
                          False -> case elemNE b cs of
                                    True -> False
                                    False -> canTransposeCov v a b ls
              CovCon cs _ -> case elemNE a cs of
                               True -> case elemNE b cs of
                                         True -> True
                                         False -> False
                               False -> case elemNE b cs of
                                         True -> False
                                         False -> canTransposeCov v a b ls
  
  canTransposeCon :: (Ord a, Ord b) => VSpace a b -> a -> a -> [(VSpace a b, IList a)] -> Bool
  canTransposeCon _ _ _ [] = False
  canTransposeCon v a b ((v',il):ls) =
    case compare v v' of
      LT -> False
      GT -> canTransposeCon v a b ls
      EQ -> case il of
              Cov _  -> canTransposeCon v a b ls
              Con cs -> case elemNE a cs of
                          True -> case elemNE b cs of
                                    True -> True
                                    False -> False
                          False -> case elemNE b cs of
                                    True -> False
                                    False -> canTransposeCon v a b ls
              CovCon _ cs -> case elemNE a cs of
                               True -> case elemNE b cs of
                                         True -> True
                                         False -> False
                               False -> case elemNE b cs of
                                         True -> False
                                         False -> canTransposeCon v a b ls
  
  canTranspose :: (Ord a, Ord b) => VSpace a b -> Ix a -> Ix a -> [(VSpace a b, IList a)] -> Bool
  canTranspose v (ICov a) (ICov b) l = case compare a b of
                                         LT -> canTransposeCov v a b l
                                         EQ -> False
                                         GT -> False
  canTranspose v (ICon a) (ICon b) l = case compare a b of
                                         LT -> canTransposeCon v a b l
                                         EQ -> False
                                         GT -> False
  canTranspose _ (ICon _) (ICov _) _ = False
  canTranspose _ (ICov _) (ICon _) _ = False

  |])
