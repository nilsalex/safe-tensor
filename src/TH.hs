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
{-# LANGUAGE OverloadedStrings #-}

module TH where

import Data.Kind (Type)

import Data.Singletons.Prelude
import Data.Singletons.Prelude.Enum
import Data.Singletons.Prelude.List.NonEmpty hiding (sLength)
import Data.Singletons.Prelude.Ord
import Data.Singletons.TH
import Data.Singletons.TypeLits

import Data.List.NonEmpty (NonEmpty((:|)),sort,(<|))

$(singletons [d|
  data N where
      Z :: N
      S :: N -> N

  deriving instance Show N
  deriving instance Eq N
  instance Ord N where
    Z <= _         = True
    (S n) <= Z     = False
    (S n) <= (S m) = n <= m

  instance Num N where
    Z + n = n
    (S n) + m = S $ n + m

    n - Z         = n
    --_ - n         = error ""
    (S n) - (S m) = n - m

    Z * _ = Z
    (S n) * m = m + n * m

    abs n = n
    signum n = n

    fromInteger n
      | n == 0 = Z
      | otherwise = S $ fromInteger (n-1)

  fromNat :: Nat -> N
  fromNat n = case n == 0 of
                True -> Z
                False -> S $ fromNat (pred n)

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

  epsilonILists :: Symbol -> Nat -> NonEmpty Symbol -> Maybe ILists
  epsilonILists vid vdim is =
      case isLengthNE is vdim of
        True  ->
          case isAscendingNE is of
            True -> Just [(VSpace vid vdim, Cov is)]
            False -> Nothing
        False -> Nothing

  epsilonInvILists :: Symbol -> Nat -> NonEmpty Symbol -> Maybe ILists
  epsilonInvILists vid vdim is =
      case isLengthNE is vdim of
        True  ->
          case isAscendingNE is of
            True -> Just [(VSpace vid vdim, Con is)]
            False -> Nothing
        False -> Nothing

  sym2Dim :: Nat -> Nat
  sym2Dim n = go 0 n
    where
      go :: Nat -> Nat -> Nat
      go acc n = case n == 0 of
                   True  -> acc
                   False -> go (acc + n) (pred n)

  injSym2ConILists :: Symbol -> Nat -> Symbol -> Symbol -> Symbol -> ILists
  injSym2ConILists vid vdim a b i =
      [(VSpace vid vdim, Con (a :| [b])), (VSpace (vid <> "Sym2") (sym2Dim vdim), Cov (i :| []))]

  injSym2CovILists :: Symbol -> Nat -> Symbol -> Symbol -> Symbol -> ILists
  injSym2CovILists vid vdim a b i =
      [(VSpace vid vdim, Cov (a :| [b])), (VSpace (vid <> "Sym2") (sym2Dim vdim), Con (i :| []))]

  surjSym2ConILists :: Symbol -> Nat -> Symbol -> Symbol -> Symbol -> ILists
  surjSym2ConILists = injSym2CovILists

  surjSym2CovILists :: Symbol -> Nat -> Symbol -> Symbol -> Symbol -> ILists
  surjSym2CovILists = injSym2ConILists

  injAreaConILists :: Symbol -> Symbol -> Symbol -> Symbol -> Symbol -> Symbol -> ILists
  injAreaConILists vid a b c d i =
    [(VSpace vid 4, Con (a :| [b,c,d])), (VSpace (vid <> "Area") 21, Cov (i :| []))]

  injAreaCovILists :: Symbol -> Symbol -> Symbol -> Symbol -> Symbol -> Symbol -> ILists
  injAreaCovILists vid a b c d i =
    [(VSpace vid 4, Cov (a :| [b,c,d])), (VSpace (vid <> "Area") 21, Con (i :| []))]

  surjAreaConILists :: Symbol -> Symbol -> Symbol -> Symbol -> Symbol -> Symbol -> ILists
  surjAreaConILists vid a b c d i =
    [(VSpace vid 4, Cov (a :| [b,c,d])), (VSpace (vid <> "Area") 21, Con (i :| []))]

  surjAreaCovILists :: Symbol -> Symbol -> Symbol -> Symbol -> Symbol -> Symbol -> ILists
  surjAreaCovILists vid a b c d i =
    [(VSpace vid 4, Con (a :| [b,c,d])), (VSpace (vid <> "Area") 21, Cov (i :| []))]

  isAscending :: Ord a => [a] -> Bool
  isAscending [] = True
  isAscending (x:[]) = True
  isAscending (x:y:xs) = x < y && isAscending ((y:xs))

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
  lengthIL (ConCov xs ys) = (lengthNE xs) + (lengthNE ys)
  lengthIL (Con xs) = lengthNE xs
  lengthIL (Cov ys) = lengthNE ys

  lengthILs :: ILists -> N
  lengthILs [] = Z
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
             Just $ (xv, xl') : xs'
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

  subsetNE :: Ord a => NonEmpty a -> NonEmpty a -> Bool
  subsetNE (x :| []) ys = x `elemNE` ys
  subsetNE (x :| (x':xs)) ys = (x `elemNE` ys) && ((x' :| xs) `subsetNE` ys)

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

  data TransList a = TransCon (NonEmpty a) (NonEmpty a) |
                     TransCov (NonEmpty a) (NonEmpty a)
    deriving (Show, Eq)
  
  saneTransList :: (Ord a, Eq a) => TransList a -> Bool
  saneTransList tl =
      case tl of
        TransCon sources targets -> isAscendingNE sources &&
                                    sort targets == sources
        TransCov sources targets -> isAscendingNE sources &&
                                    sort targets == sources

  canTransposeMult :: (Ord a, Ord b) => VSpace a b -> TransList a -> [(VSpace a b, IList a)] -> Bool
  canTransposeMult vs tl ils = case transpositions vs tl ils of
                                 Just _  -> True
                                 Nothing -> False
  
  transpositions :: (Ord a, Ord b) => VSpace a b -> TransList a -> [(VSpace a b, IList a)] -> Maybe [(N,N)]
  transpositions _ _ []              = Nothing
  transpositions vs tl ((vs',il):is) =
      case saneTransList tl of
        False -> Nothing
        True ->
          case compare vs vs' of
            LT -> Nothing
            GT -> transpositions vs tl is
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
      ss <- mapM (\a -> find a xs') sources
      ts <- mapM (\a -> find a xs') targets
      zip' ss ts
    where
      xs' = go' Z xs
  
      go' :: N -> NonEmpty a -> NonEmpty (N,a)
      go' n (x :| []) = (n,x) :| []
      go' n (x :| (x':xs')) = (n,x) <| go' (S n) (x' :| xs')
  
      find :: Eq a => a -> NonEmpty (N, Maybe a) -> Maybe N
      find a ((_,Nothing) :| []) = Nothing
      find a ((_,Nothing) :| (x':xs')) = find a (x' :| xs')
      find a ((n,Just x) :| xs)  =
        case a == x of
          True -> Just n
          False  -> 
            case xs of
              [] -> Nothing
              x':xs' -> find a (x' :| xs')
  
      zip' :: NonEmpty a -> NonEmpty b -> Maybe [(a,b)]
      zip' (a :| []) (b :| []) = Just [(a,b)]
      zip' (_ :| (_:_)) (_ :| []) = Nothing
      zip' (_ :| []) (_ :| (_:_)) = Nothing
      zip' (x:|(x':xs')) (y:|(y':ys')) = fmap ((x,y):) $ zip' (x':|xs') (y':|ys')
  |])

toInt :: N -> Int
toInt Z = 0
toInt (S n) = 1 + toInt n

data Vec :: N -> Type -> Type where
    VNil :: Vec Z a
    VCons :: a -> Vec n a -> Vec (S n) a

deriving instance Show a => Show (Vec n a)

instance Eq a => Eq (Vec n a) where
  VNil           == VNil           = True
  (x `VCons` xs) == (y `VCons` ys) = x == y && xs == ys

instance Ord a => Ord (Vec n a) where
  VNil `compare` VNil = EQ
  (x `VCons` xs) `compare` (y `VCons` ys) =
    case x `compare` y of
      LT -> LT
      EQ -> xs `compare` ys
      GT -> GT

vecFromListUnsafe :: forall (n :: N) a.
                     Sing n -> [a] -> Vec n a
vecFromListUnsafe SZ [] = VNil
vecFromListUnsafe (SS sn) (x:xs) =
    let xs' = vecFromListUnsafe sn xs
    in  x `VCons` xs'

