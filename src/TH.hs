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

import Data.Singletons.Prelude
import Data.Singletons.Prelude.List.NonEmpty hiding (sSort, SortSym0)
import Data.Singletons.Prelude.Ord
import Data.Singletons.TH
import Data.Singletons.TypeLits

import Data.List.NonEmpty (NonEmpty((:|)))

$(singletons [d|
  data VSpace a b = VSpace { vId :: a,
                            vDim :: b }
                    deriving (Show, Ord, Eq)

  data Ix a    = ICon a | ICov a deriving (Show, Ord, Eq)

  ixCompare :: Ord a => Ix a -> Ix a -> Ordering
  ixCompare (ICon a) (ICon b) = compare a b
  ixCompare (ICon a) (ICov b) = case compare a b of
                                  LT -> LT
                                  EQ -> LT
                                  GT -> GT
  ixCompare (ICov a) (ICon b) = case compare a b of
                                  LT -> LT
                                  EQ -> GT
                                  GT -> GT
  ixCompare (ICov a) (ICov b) = compare a b
  
  data IList a = ConCov (NonEmpty a) (NonEmpty a) |
                 Cov (NonEmpty a) |
                 Con (NonEmpty a)
                 deriving (Show, Ord, Eq)

  type ILists = [(VSpace Symbol Nat, IList Symbol)]

  deltaILists :: Symbol -> Nat -> Symbol -> Symbol -> ILists
  deltaILists vid vdim a b = [(VSpace vid vdim, ConCov (a :| []) (b :| []))]

  isAscending :: Ord a => [a] -> Bool
  isAscending [] = True
  isAscending (x:[]) = True
  isAscending (x:y:xs) = x < y && isAscending ((y:xs))

  isAscending' :: Ord a => NonEmpty a -> Bool
  isAscending' (x :| xs) = isAscending (x:xs)

  isAscendingI :: Ord a => IList a -> Bool
  isAscendingI (ConCov x y) = isAscending' x && isAscending' y
  isAscendingI (Con x) = isAscending' x
  isAscendingI (Cov y) = isAscending' y

  lengthNE :: NonEmpty a -> Nat
  lengthNE (_ :| []) = 1
  lengthNE (_ :| (x:xs)) = 1 + lengthNE (x :| xs)

  lengthIL :: IList a -> Nat
  lengthIL (ConCov xs ys) = (lengthNE xs) + (lengthNE ys)
  lengthIL (Con xs) = lengthNE xs
  lengthIL (Cov ys) = lengthNE ys

  lengthILs :: ILists -> Nat
  lengthILs [] = 0
  lengthILs ((_,x):xs) = lengthIL x + lengthILs xs

  sane :: ILists -> Bool
  sane [] = True
  sane ((_, is):[]) = isAscendingI is
  sane ((v, is):(v', is'):xs) =
      v < v' && isAscendingI is && sane ((v',is'):xs)

  head' :: ILists -> (VSpace Symbol Nat, Ix Symbol)
  head' ((v, l):_) = (v, case l of
                           ConCov (a :| _) (b :| _) ->
                             case compare a b of
                               LT -> ICon a
                               EQ -> ICon a
                               GT -> ICov b
                           Con (a :| _)      -> ICon a
                           Cov (a :| _)      -> ICov a)
  head' [] = error "head' of empty list"

  tail' :: ILists -> ILists
  tail' ((v, l):ls) =
    let l' = case l of
               ConCov (a :| []) (b :| []) ->
                 case compare a b of
                   LT -> Just $ Cov (b :| [])
                   EQ -> Just $ Cov (b :| [])
                   GT -> Just $ Con (a :| [])

               ConCov (a :| (a':as)) (b :| []) ->
                 case compare a b of
                   LT -> Just $ ConCov (a' :| as) (b :| [])
                   EQ -> Just $ ConCov (a' :| as) (b :| [])
                   GT -> Just $ Con (a :| (a':as))

               ConCov (a :| []) (b :| (b':bs)) ->
                 case compare a b of
                   LT -> Just $ Cov (b :| (b':bs))
                   EQ -> Just $ Cov (b :| (b':bs))
                   GT -> Just $ ConCov (a :| []) (b' :| bs)

               ConCov (a :| (a':as)) (b :| (b':bs)) ->
                 case compare a b of
                   LT -> Just $ ConCov (a' :| as) (b :| (b':bs))
                   EQ -> Just $ ConCov (a' :| as) (b :| (b':bs))
                   GT -> Just $ ConCov (a :| (a':as)) (b' :| bs)

               Con (a :| []) -> Nothing
               Con (a :| (a':as)) -> Just $ Con (a' :| as)

               Cov (a :| []) -> Nothing
               Cov (a :| (a':as)) -> Just $ Cov (a' :| as)
             in case l' of
                  Just l'' -> (v, l''):ls
                  Nothing  -> ls
  tail' [] = error "tail' of empty list"

  mergeILs :: ILists -> ILists -> Maybe ILists
  mergeILs [] ys = Just ys
  mergeILs xs [] = Just xs
  mergeILs ((xv,xl):xs) ((yv,yl):ys) = 
    case compare xv yv of
      LT -> fmap ((xv,xl) :) $ mergeILs xs ((yv,yl):ys)
      EQ -> do
             xl' <- mergeIL xl yl
             xs' <- mergeILs xs ys
             Just $ (xv, xl') : ys
      GT -> fmap ((yv,yl) :) $ mergeILs ((xv,xl):xs) ys

  mergeIL :: Ord a => IList a -> IList a -> Maybe (IList a)
  mergeIL (ConCov xs ys) (ConCov xs' ys') = do
      xs'' <- mergeNE xs xs'
      ys'' <- mergeNE ys ys'
      Just $ ConCov xs'' ys''
  mergeIL (ConCov xs ys) (Con xs') = do
      xs'' <- mergeNE xs xs'
      Just $ ConCov xs'' ys
  mergeIL (ConCov xs ys) (Cov ys') = do
      ys'' <- mergeNE ys ys'
      Just $ ConCov xs ys''
  mergeIL (Con xs) (ConCov xs' ys) = do
      xs'' <- mergeNE xs xs'
      Just $ ConCov xs'' ys
  mergeIL (Con xs) (Con xs') = fmap Con $ mergeNE xs xs'
  mergeIL (Con xs) (Cov ys) = Just $ ConCov xs ys
  mergeIL (Cov ys) (ConCov xs ys') = do
      ys'' <- mergeNE ys ys'
      Just $ ConCov xs ys''
  mergeIL (Cov ys) (Con xs) = Just $ ConCov xs ys
  mergeIL (Cov ys) (Cov ys') = fmap Cov $ mergeNE ys ys'

  merge :: Ord a => [a] -> [a] -> Maybe [a]
  merge [] ys = Just ys
  merge xs [] = Just xs
  merge (x:xs) (y:ys) =
    case compare x y of
      LT -> fmap (x :) $ merge xs (y:ys)
      EQ -> Nothing
      GT -> fmap (y :) $ merge (x:xs) ys

  mergeNE :: Ord a => NonEmpty a -> NonEmpty a -> Maybe (NonEmpty a)
  mergeNE (x :| xs) (y :| ys) =
    case compare x y of
      LT -> fmap (x :|) $ merge xs (y:ys)
      EQ -> Nothing
      GT -> fmap (y :|) $ merge (x:xs) ys

  contractL :: ILists -> ILists
  contractL [] = []
  contractL ((v, is):xs) = case contractI is of
                             Nothing -> contractL xs
                             Just is' -> (v, is') : contractL xs

  prepICon :: a -> IList a -> IList a
  prepICon a (ConCov (x:|xs) y) = ConCov (a:|(x:xs)) y
  prepICon a (Con (x:|xs)) = Con (a:|(x:xs))
  prepICon a (Cov y) = ConCov (a:|[]) y

  prepICov :: a -> IList a -> IList a
  prepICov a (ConCov x (y:|ys)) = ConCov (x) (a:|(y:ys))
  prepICov a (Con x) = ConCov x (a:|[])
  prepICov a (Cov (y:|ys)) = Cov (a:|(y:ys))

  contractI :: Ord a => IList a -> Maybe (IList a)
  contractI (ConCov (x:|xs) (y:|ys)) =
    case compare x y of
      EQ -> case xs of
              [] -> case ys of
                      [] -> Nothing
                      (y':ys') -> Just $ Cov (y' :| ys')
              (x':xs') -> case ys of
                            [] -> Just $ Con (x' :| xs')
                            (y':ys') -> contractI $ ConCov (x':|xs') (y':|ys')
      LT -> case xs of
              [] -> Just $ ConCov (x:|xs) (y:|ys)
              (x':xs') -> case contractI $ ConCov (x':|xs') (y:|ys) of
                            Nothing -> Just $ Con (x:|[])
                            Just i  -> Just $ prepICon x i
      GT -> case ys of
              [] -> Just $ ConCov (x:|xs) (y:|ys)
              (y':ys') -> case contractI $ ConCov (x:|xs) (y':|ys') of
                            Nothing -> Just $ Cov (y:|[])
                            Just i  -> Just $ prepICov x i
  contractI (Con x) = Just $ Con x
  contractI (Cov x) = Just $ Cov x

  elemNE :: Ord a => a -> NonEmpty a -> Bool
  elemNE a (x :| []) = a == x
  elemNE a (x :| (x':xs)) = case compare a x of
                              LT -> False
                              EQ -> True
                              GT -> elemNE a (x' :| xs)
  
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
              ConCov cs _ -> case elemNE a cs of
                               True -> case elemNE b cs of
                                         True -> True
                                         False -> False
                               False -> case elemNE b cs of
                                         True -> False
                                         False -> canTransposeCon v a b ls
  
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
              ConCov _ cs -> case elemNE a cs of
                               True -> case elemNE b cs of
                                         True -> True
                                         False -> False
                               False -> case elemNE b cs of
                                         True -> False
                                         False -> canTransposeCov v a b ls
  
  canTranspose :: (Ord a, Ord b) => VSpace a b -> Ix a -> Ix a -> [(VSpace a b, IList a)] -> Bool
  canTranspose v (ICon a) (ICon b) l = case compare a b of
                                         LT -> canTransposeCon v a b l
                                         EQ -> True
                                         GT -> canTransposeCov v b a l
  canTranspose v (ICov a) (ICov b) l = case compare a b of
                                         LT -> canTransposeCov v a b l
                                         EQ -> True
                                         GT -> canTransposeCov v b a l
  canTranspose _ (ICov _) (ICon _) _ = False
  canTranspose _ (ICon _) (ICov _) _ = False

  removeUntil :: Ix Symbol -> ILists -> ILists
  removeUntil i ls = go i ls
    where
      go i' ls'
        | snd (head' ls') == i' = tail' ls'
        | otherwise             = go i $ tail' ls'

  |])
