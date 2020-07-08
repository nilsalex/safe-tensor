{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
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
{-# LANGUAGE OverloadedStrings #-}

{-# LANGUAGE CPP #-}
#if MIN_VERSION_base(4,14,0)
{-# LANGUAGE StandaloneKindSignatures #-}
#endif

-----------------------------------------------------------------------------
{-|
Module      : Math.Tensor.Safe.TH
Description : Type families and singletons for generalized types.
Copyright   : (c) Nils Alex, 2020
License     : MIT
Maintainer  : nils.alex@fau.de

Type families and singletons for generalized types.
For documentation see re-exports in "Math.Tensor.Safe".
-}
-----------------------------------------------------------------------------
module Math.Tensor.Safe.TH where

import Data.Singletons.Prelude
import Data.Singletons.Prelude.Enum
import Data.Singletons.Prelude.List.NonEmpty hiding (sLength)
import Data.Singletons.Prelude.Ord
import Data.Singletons.TH
import Data.Singletons.TypeLits

import Data.List.NonEmpty (NonEmpty((:|)),sort,sortBy,(<|))

$(singletons [d|
  data N where
      Z :: N
      S :: N -> N

  fromNat :: Nat -> N
  fromNat n = case n == 0 of
                True -> Z
                False -> S $ fromNat (pred n)

  deriving instance Show N
  deriving instance Eq N
  instance Ord N where
    Z <= _         = True
    (S _) <= Z     = False
    (S n) <= (S m) = n <= m
  
  instance Num N where
    Z + n = n
    (S n) + m = S $ n + m
  
    n - Z         = n
    Z - S _       = error "cannot subtract (S n) from Z!"
    (S n) - (S m) = n - m
  
    negate Z = Z
    negate _ = error "cannot negate (S n)!"
  
    Z * _ = Z
    (S n) * m = m + n * m
  
    abs n = n
    signum n = n
  
    fromInteger n
      | n == 0 = Z
      | otherwise = S $ fromInteger (n-1)
  
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
  
  type GRank s n = [(VSpace s n, IList s)]
  type Rank = GRank Symbol Nat
  
  isAscending :: Ord a => [a] -> Bool
  isAscending []  = True
  isAscending [_] = True
  isAscending (x:y:xs) = x < y && isAscending (y:xs)
  
  isAscendingNE :: Ord a => NonEmpty a -> Bool
  isAscendingNE (x :| xs) = isAscending (x:xs)
  
  isAscendingI :: Ord a => IList a -> Bool
  isAscendingI (ConCov x y) = isAscendingNE x && isAscendingNE y
  isAscendingI (Con x) = isAscendingNE x
  isAscendingI (Cov y) = isAscendingNE y
  
  isLengthNE :: NonEmpty a -> Nat -> Bool
  isLengthNE (_ :| []) l = l == 1
  isLengthNE (_ :| (x:xs)) l = isLengthNE (x :| xs) (pred l)
  
  lengthNE :: NonEmpty a -> N
  lengthNE (_ :| []) = S Z
  lengthNE (_ :| (x:xs)) = S Z + lengthNE (x :| xs)
  
  lengthIL :: IList a -> N
  lengthIL (ConCov xs ys) = lengthNE xs + lengthNE ys
  lengthIL (Con xs) = lengthNE xs
  lengthIL (Cov ys) = lengthNE ys
  
  lengthR :: GRank s n -> N
  lengthR [] = Z
  lengthR ((_,x):xs) = lengthIL x + lengthR xs
  
  sane :: (Ord a, Ord b) => [(VSpace a b, IList a)] -> Bool
  sane [] = True
  sane [(_, is)] = isAscendingI is
  sane ((v, is):(v', is'):xs) =
      v < v' && isAscendingI is && sane ((v',is'):xs)
  
  headR :: Ord s => GRank s n -> (VSpace s n, Ix s)
  headR ((v, l):_) = (v, case l of
                           ConCov (a :| _) (b :| _) ->
                             case compare a b of
                               LT -> ICon a
                               EQ -> ICon a
                               GT -> ICov b
                           Con (a :| _)      -> ICon a
                           Cov (a :| _)      -> ICov a)
  headR [] = error "headR of empty list"
  
  tailR :: Ord s => GRank s n -> GRank s n
  tailR ((v, l):ls) =
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
  
               Con (_ :| []) -> Nothing
               Con (_ :| (a':as)) -> Just $ Con (a' :| as)
  
               Cov (_ :| []) -> Nothing
               Cov (_ :| (a':as)) -> Just $ Cov (a' :| as)
             in case l' of
                  Just l'' -> (v, l''):ls
                  Nothing  -> ls
  tailR [] = error "tailR of empty list"
  
  mergeR :: (Ord s, Ord n) => GRank s n -> GRank s n -> Maybe (GRank s n)
  mergeR [] ys = Just ys
  mergeR xs [] = Just xs
  mergeR ((xv,xl):xs) ((yv,yl):ys) = 
    case compare xv yv of
      LT -> ((xv,xl) :) <$> mergeR xs ((yv,yl):ys)
      EQ -> do
             xl' <- mergeIL xl yl
             xs' <- mergeR xs ys
             Just $ (xv, xl') : xs'
      GT -> ((yv,yl) :) <$> mergeR ((xv,xl):xs) ys
  
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
  mergeIL (Con xs) (Con xs') = Con <$> mergeNE xs xs'
  mergeIL (Con xs) (Cov ys) = Just $ ConCov xs ys
  mergeIL (Cov ys) (ConCov xs ys') = do
      ys'' <- mergeNE ys ys'
      Just $ ConCov xs ys''
  mergeIL (Cov ys) (Con xs) = Just $ ConCov xs ys
  mergeIL (Cov ys) (Cov ys') = Cov <$> mergeNE ys ys'
  
  merge :: Ord a => [a] -> [a] -> Maybe [a]
  merge [] ys = Just ys
  merge xs [] = Just xs
  merge (x:xs) (y:ys) =
    case compare x y of
      LT -> (x :) <$> merge xs (y:ys)
      EQ -> Nothing
      GT -> (y :) <$> merge (x:xs) ys
  
  mergeNE :: Ord a => NonEmpty a -> NonEmpty a -> Maybe (NonEmpty a)
  mergeNE (x :| xs) (y :| ys) =
    case compare x y of
      LT -> (x :|) <$> merge xs (y:ys)
      EQ -> Nothing
      GT -> (y :|) <$> merge (x:xs) ys
  
  contractR :: Ord s => GRank s n -> GRank s n
  contractR [] = []
  contractR ((v, is):xs) = case contractI is of
                             Nothing -> contractR xs
                             Just is' -> (v, is') : contractR xs
  
  prepICon :: a -> IList a -> IList a
  prepICon a (ConCov (x:|xs) y) = ConCov (a:|(x:xs)) y
  prepICon a (Con (x:|xs)) = Con (a:|(x:xs))
  prepICon a (Cov y) = ConCov (a:|[]) y
  
  prepICov :: a -> IList a -> IList a
  prepICov a (ConCov x (y:|ys)) = ConCov x (a:|(y:ys))
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
                            Just i  -> Just $ prepICov y i
  contractI (Con x) = Just $ Con x
  contractI (Cov x) = Just $ Cov x
  
  subsetNE :: Ord a => NonEmpty a -> NonEmpty a -> Bool
  subsetNE (x :| []) ys = x `elemNE` ys
  subsetNE (x :| (x':xs)) ys = (x `elemNE` ys) && ((x' :| xs) `subsetNE` ys)
  
  elemNE :: Ord a => a -> NonEmpty a -> Bool
  elemNE a (x :| []) = a == x
  elemNE a (x :| (x':xs)) = case compare a x of
                              LT -> False
                              EQ -> True
                              GT -> elemNE a (x' :| xs)
  
  canTransposeCon :: (Ord s, Ord n) => VSpace s n -> s -> s -> GRank s n -> Bool
  canTransposeCon _ _ _ [] = False
  canTransposeCon v a b ((v',il):r) =
    case compare v v' of
      LT -> False
      GT -> canTransposeCon v a b r
      EQ -> case il of
              Cov _  -> canTransposeCon v a b r
              Con cs -> case elemNE a cs of
                          True -> case elemNE b cs of
                                    True -> True
                                    False -> False
                          False -> case elemNE b cs of
                                    True -> False
                                    False -> canTransposeCon v a b r
              ConCov cs _ -> case elemNE a cs of
                               True -> case elemNE b cs of
                                         True -> True
                                         False -> False
                               False -> case elemNE b cs of
                                         True -> False
                                         False -> canTransposeCon v a b r
  
  canTransposeCov :: (Ord s, Ord n) => VSpace s n -> s -> s -> GRank s n -> Bool
  canTransposeCov _ _ _ [] = False
  canTransposeCov v a b ((v',il):r) =
    case compare v v' of
      LT -> False
      GT -> canTransposeCov v a b r
      EQ -> case il of
              Con _  -> canTransposeCov v a b r
              Cov cs -> case elemNE a cs of
                          True -> case elemNE b cs of
                                    True -> True
                                    False -> False
                          False -> case elemNE b cs of
                                    True -> False
                                    False -> canTransposeCov v a b r
              ConCov _ cs -> case elemNE a cs of
                               True -> case elemNE b cs of
                                         True -> True
                                         False -> False
                               False -> case elemNE b cs of
                                         True -> False
                                         False -> canTransposeCov v a b r
  
  canTranspose :: (Ord s, Ord n) => VSpace s n -> Ix s -> Ix s -> GRank s n -> Bool
  canTranspose v (ICon a) (ICon b) r = case compare a b of
                                         LT -> canTransposeCon v a b r
                                         EQ -> True
                                         GT -> canTransposeCov v b a r
  canTranspose v (ICov a) (ICov b) r = case compare a b of
                                         LT -> canTransposeCov v a b r
                                         EQ -> True
                                         GT -> canTransposeCov v b a r
  canTranspose _ (ICov _) (ICon _) _ = False
  canTranspose _ (ICon _) (ICov _) _ = False
  
  removeUntil :: Ord s => Ix s -> GRank s n -> GRank s n
  removeUntil i r = go i r
    where
      go i' r'
        | snd (headR r') == i' = tailR r'
        | otherwise            = go i $ tailR r'
  
  data TransList a = TransCon (NonEmpty a) (NonEmpty a) |
                     TransCov (NonEmpty a) (NonEmpty a)
    deriving (Show, Eq)
  
  saneTransList :: Ord a => TransList a -> Bool
  saneTransList tl =
      case tl of
        TransCon sources targets -> isAscendingNE sources &&
                                    sort targets == sources
        TransCov sources targets -> isAscendingNE sources &&
                                    sort targets == sources
  
  canTransposeMult :: (Ord s, Ord n) => VSpace s n -> TransList s -> GRank s n -> Bool
  canTransposeMult vs tl r = case transpositions vs tl r of
                               Just _  -> True
                               Nothing -> False
  
  transpositions :: (Ord s, Ord n) => VSpace s n -> TransList s -> GRank s n -> Maybe [(N,N)]
  transpositions _ _ []              = Nothing
  transpositions vs tl ((vs',il):r) =
      case saneTransList tl of
        False -> Nothing
        True ->
          case compare vs vs' of
            LT -> Nothing
            GT -> transpositions vs tl r
            EQ ->
              case il of
                Con xs ->
                  case tl of
                    TransCon sources targets -> transpositions' sources targets (fmap Just xs)
                    TransCov _ _ -> Nothing
                Cov xs ->
                  case tl of
                    TransCov sources targets -> transpositions' sources targets (fmap Just xs)
                    TransCon _ _ -> Nothing
                ConCov xsCon xsCov ->
                  case tl of
                    TransCon sources targets -> transpositions' sources targets (xsCon `zipCon` xsCov)
                    TransCov sources targets -> transpositions' sources targets (xsCon `zipCov` xsCov)
  
  zipCon :: Ord a => NonEmpty a -> NonEmpty a -> NonEmpty (Maybe a)
  zipCon (x :| xs) (y :| ys) =
    case ICon x `ixCompare` ICov y of
      LT -> case xs of
              []       -> Just x :| fmap (const Nothing) (y:ys)
              (x':xs') -> Just x <| zipCon (x' :| xs') (y :| ys)
      GT -> case ys of
              []       -> Nothing :| fmap Just (x : xs)
              (y':ys') -> Nothing <| zipCon (x :| xs) (y' :| ys')
  
  zipCov :: Ord a => NonEmpty a -> NonEmpty a -> NonEmpty (Maybe a)
  zipCov (x :| xs) (y :| ys) =
    case ICon x `ixCompare` ICov y of
      LT -> case xs of
              []       -> Nothing :| fmap Just (y:ys)
              (x':xs') -> Nothing <| zipCov (x' :| xs') (y :| ys)
      GT -> case ys of
              []       -> Just y :| fmap (const Nothing) (x : xs)
              (y':ys') -> Just y <| zipCov (x :| xs) (y' :| ys')
  
  transpositions' :: Eq a => NonEmpty a -> NonEmpty a -> NonEmpty (Maybe a) -> Maybe [(N,N)]
  transpositions' sources targets xs =
    do
      ss <- mapM (`find` xs') sources
      ts <- mapM (`find` xs') targets
      zip' ss ts
    where
      xs' = go' Z xs
  
      go' :: N -> NonEmpty a -> NonEmpty (N,a)
      go' n (y :| []) = (n,y) :| []
      go' n (y :| (y':ys')) = (n,y) <| go' (S n) (y' :| ys')
  
      find :: Eq a => a -> NonEmpty (N, Maybe a) -> Maybe N
      find _ ((_,Nothing) :| []) = Nothing
      find a ((_,Nothing) :| (y':ys')) = find a (y' :| ys')
      find a ((n,Just y) :| ys)  =
        case a == y of
          True -> Just n
          False  -> 
            case ys of
              [] -> Nothing
              y':ys' -> find a (y' :| ys')
  
      zip' :: NonEmpty a -> NonEmpty b -> Maybe [(a,b)]
      zip' (a :| []) (b :| []) = Just [(a,b)]
      zip' (_ :| (_:_)) (_ :| []) = Nothing
      zip' (_ :| []) (_ :| (_:_)) = Nothing
      zip' (y:|(y':ys')) (z:|(z':zs')) = ((y,z):) <$> zip' (y':|ys') (z':|zs')
  
  type RelabelList s = NonEmpty (s,s)
  
  saneRelabelList :: Ord a => NonEmpty (a,a) -> Bool
  saneRelabelList xs = isAscendingNE xs &&
                       isAscendingNE xs'
    where
      xs' = sort $ fmap (\(a,b) -> (b,a)) xs
  
  relabelNE :: Ord a => NonEmpty (a,a) -> NonEmpty a -> Maybe (NonEmpty (a,a))
  relabelNE = go
    where
      go :: Ord a => NonEmpty (a,a) -> NonEmpty a -> Maybe (NonEmpty (a,a))
      go ((source,target) :| ms) (x :| xs) =
        case source `compare` x of
          LT ->
            case ms of
              []     -> Just $ (\a -> (a,a)) <$> (x :| xs)
              m':ms' -> go (m' :| ms') (x :| xs)
          EQ ->
            case ms of
              []     -> Just $ ((target,source) :|) $ fmap (\a -> (a,a)) xs
              m':ms' ->
                case xs of
                  []     -> Just $ (target,source) :| []
                  x':xs' -> ((target,source) <|) <$> go (m' :| ms') (x' :| xs')
          GT ->
            case xs of
              []     -> Just $ (x,x) :| []
              x':xs' -> ((x,x) <|) <$> go ((source,target) :| ms) (x' :| xs')
  
  relabelR :: (Ord s, Ord n) => VSpace s n -> RelabelList s -> GRank s n -> Maybe (GRank s n)
  relabelR _ _ [] = Nothing
  relabelR vs rls ((vs',il):r) =
    case vs `compare` vs' of
      LT -> Nothing
      EQ -> (\il' -> (vs',il'):r) <$> relabelIL rls il
      GT -> ((vs',il) :) <$> relabelR vs rls r
  
  relabelIL :: Ord a => NonEmpty (a,a) -> IList a -> Maybe (IList a)
  relabelIL rl is = case relabelIL' rl is of
                      Nothing -> Nothing
                      Just (Con is') -> Just $ Con $ fst <$> is'
                      Just (Cov is') -> Just $ Cov $ fst <$> is'
                      Just (ConCov is' js') -> Just $ ConCov (fst <$> is') (fst <$> js')
  
  relabelIL' :: Ord a => NonEmpty (a,a) -> IList a -> Maybe (IList (a,a))
  relabelIL' rl (Con is) =
    do
      is' <- Con . sort <$> relabelNE rl is
      case isAscendingI is' of
        True -> return is'
        False -> Nothing
  relabelIL' rl (Cov is) =
    do
      is' <- Cov . sort <$> relabelNE rl is
      case isAscendingI is' of
        True -> return is'
        False -> Nothing
  relabelIL' rl (ConCov is js) =
    do
      is' <- sort <$> relabelNE rl is
      js' <- sort <$> relabelNE rl js
      let l' = ConCov is' js'
      case isAscendingI l' of
        True -> return l'
        False -> Nothing
  
  relabelTranspositions :: Ord a => NonEmpty (a,a) -> IList a -> Maybe [(N,N)]
  relabelTranspositions rl is =
    case relabelIL' rl is of
      Nothing -> Nothing
      Just (Con is') -> Just $ relabelTranspositions' is'
      Just (Cov is') -> Just $ relabelTranspositions' is'
      Just (ConCov is' js') -> Just $ relabelTranspositions' $ is' `zipConCov` js'
  
  zipConCov :: Ord a => NonEmpty a -> NonEmpty a -> NonEmpty a
  zipConCov = go
    where
      go :: Ord a => NonEmpty a -> NonEmpty a -> NonEmpty a
      go (i :| is) (j :| js) =
        case i `compare` j of
          LT -> case is of
                  [] -> i <| (j:|js)
                  i':is' -> i <| go (i' :| is') (j :| js)
          EQ -> case is of
                  [] -> i <| (j:|js)
                  i':is' -> i <| go (i' :| is') (j :| js)
          GT -> case js of
                  [] -> j <| (i:|is)
                  j':js' -> j <| go (i :| is) (j' :| js')
  
  relabelTranspositions' :: Ord a => NonEmpty (a,a) -> [(N,N)]
  relabelTranspositions' is = go'' is'''
    where
      is' = go Z is
      is'' = sortBy (\a b -> snd a `compare` snd b) is'
      is''' = go' Z is''
      --is'''' = sort is'''
  
      go :: N -> NonEmpty (a,b) -> NonEmpty (N,b)
      go n ((_,y) :| [])     = (n,y) :| []
      go n ((_,y) :| (j:js)) = (n,y) <| go (S n) (j :| js)
  
      go' :: N -> NonEmpty (a,b) -> NonEmpty (a,N)
      go' n ((x,_) :| [])     = (x,n) :| []
      go' n ((x,_) :| (j:js)) = (x,n) <| go' (S n) (j :| js)
  
      go'' :: NonEmpty (a,a) -> [(a,a)]
      go'' ((x1,x2) :| []) = [(x2,x1)]
      go'' ((x1,x2) :| (y:ys)) = (x2,x1) : go'' (y :| ys)
  |])
  
toInt :: N -> Int
toInt Z = 0
toInt (S n) = 1 + toInt n
