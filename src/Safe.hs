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

module Safe where

import TH
import Internal

import Data.Kind (Type)

import Data.Singletons
import Data.Singletons.Prelude
import Data.Singletons.Prelude.Maybe
import Data.Singletons.Decide
import Data.Singletons.TypeLits

import Data.List (foldl',groupBy,sortBy)
import Data.List.NonEmpty (NonEmpty((:|)))

toInt :: N -> Int
toInt Z = 0
toInt (S n) = 1 + toInt n

data Vec :: N -> Type -> Type where
    VNil :: Vec Z a
    VCons :: a -> Vec n a -> Vec (S n) a

deriving instance Show a => Show (Vec n a)

data Tensor :: ILists -> Type -> Type where
    ZeroTensor :: forall (l :: ILists) v . Sane l ~ 'True => Tensor l v
    Scalar :: forall (l :: ILists) v.  l ~ '[] => v -> Tensor l v
    Tensor :: forall (l :: ILists) (l' :: ILists) v.
              (Sane l ~ 'True, Tail' l ~ l') =>
              [(Int, Tensor l' v)] -> Tensor l v

deriving instance Eq v => Eq (Tensor l v)
deriving instance Show v => Show (Tensor l v)

instance Functor (Tensor l) where
  fmap f ZeroTensor = ZeroTensor
  fmap f (Scalar s) = Scalar $ f s
  fmap f (Tensor ms) = Tensor $ fmap (fmap (fmap f)) ms

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

infixl 6 &+

(&-) :: forall (l :: ILists) (l' :: ILists) v.
        ((l ~ l'), Num v, Eq v) =>
        Tensor l v -> Tensor l' v -> Tensor l v
(&-) t1 t2 = t1 &+ (fmap negate t2)

infixl 6 &-

(&*) :: forall (l :: ILists) (l' :: ILists) (l'' :: ILists) v.
               (Num v, Just l'' ~ MergeILs l l', Sane l'' ~ 'True,
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
      SJust sl'' = sMergeILs sl sl'
  in case sSane sl'' of
       STrue -> case sSane (sTail' sl'') of
         STrue -> case sh of
           STuple2 sv si ->
             case sh' of
               STuple2 sv' si' ->
                 case sCompare sv sv' of
                   SLT -> case sMergeILs st sl' %~ SJust (sTail' sl'') of
                            Proved Refl -> Tensor $ fmap (fmap (\t -> withSingI st $ t &* (Tensor ms' :: Tensor l' v))) ms
                   SGT -> case sMergeILs sl st' %~ SJust (sTail' sl'') of
                            Proved Refl -> Tensor $ fmap (fmap (\t -> withSingI st' $ (Tensor ms :: Tensor l v) &* t)) ms'
                   SEQ -> case sIxCompare si si' of
                            SLT -> case sMergeILs st sl' %~ SJust (sTail' sl'') of
                                     Proved Refl -> Tensor $ fmap (fmap (\t -> withSingI st $ t &* (Tensor ms' :: Tensor l' v))) ms
                            SEQ -> case sMergeILs st sl' %~ SJust (sTail' sl'') of
                                     Proved Refl -> Tensor $ fmap (fmap (\t -> withSingI st $ t &* (Tensor ms' :: Tensor l' v))) ms
                            SGT -> case sMergeILs sl st' %~ SJust (sTail' sl'') of
                                     Proved Refl -> Tensor $ fmap (fmap (\t -> withSingI st' $ (Tensor ms :: Tensor l v) &* t)) ms'
(&*) ZeroTensor _ = ZeroTensor
(&*) _ ZeroTensor = ZeroTensor

infixl 7 &*

contract :: forall (l :: ILists) (l' :: ILists) v.
            (l' ~ ContractL l, SingI l, Num v, Eq v)
            => Tensor l v -> Tensor l' v
contract ZeroTensor = let sl' = sContractL (sing :: Sing l)
                      in case sSane sl' of
                           STrue -> ZeroTensor
contract (Scalar v) = Scalar v
contract (Tensor ms) =
    let sl = sing :: Sing l
        sl' = sContractL sl
        st = sTail' sl
    in case st of
         SNil -> case sl %~ sContractL sl of
                   Proved Refl -> Tensor ms
         _    -> case sSane sl' of
                   STrue -> 
                     let st' = sTail' st
                         sh  = sHead' sl
                         sv  = sFst sh
                         si  = sSnd sh
                         sh' = sHead' st
                         sv' = sFst sh'
                         si' = sSnd sh'
                         t'  = withSingI st $
                               case sTail' sl' %~ sContractL st of
                                 Proved Refl -> removeZeros $ Tensor $ fmap (fmap contract) ms
                     in case sv %~ sv' of
                          Disproved _ -> t'
                          Proved Refl -> case si of
                            SICon sa -> case si' of
                              SICov sb -> case sa %~ sb of

                                Proved Refl -> 
                                          let ms' = fmap (\(i, v) -> case v of
                                                                       Tensor vs ->
                                                                         case filter (\(i', _) -> i == i') vs of
                                                                              [] -> Nothing
                                                                              (_, (v')):[] -> Just v'
                                                                              _ -> error "duplicate key in tensor assoc list") ms
                                              ms'' = filter (\x -> case x of
                                                                     Nothing -> False
                                                                     Just x' -> True) ms'
                                              ms''' = fmap (\(Just x) -> x) ms'' :: [Tensor (Tail' (Tail' l)) v]
                                          in case st' %~ sl' of
                                                    Proved Refl -> foldl' (&+) ZeroTensor ms'''
                                                    Disproved _ -> case sContractL st' %~ sl' of
                                                                     Proved Refl -> case sSane st' of
                                                                                      STrue -> withSingI (st') $ contract $ foldl' (&+) ZeroTensor ms'''

                                Disproved _ -> t'
                              _        -> t'
                            _        -> t'

transpose :: forall (vs :: VSpace Symbol Nat) (a :: Ix Symbol) (b :: Ix Symbol) (l :: ILists) v.
              (CanTranspose vs a b l ~ 'True, SingI l) =>
              Sing vs -> Sing a -> Sing b -> Tensor l v -> Tensor l v
transpose _ _ _ ZeroTensor = ZeroTensor
transpose _ _ _ (Scalar _) = error "This is not possible, might yet have to convince the type system."
transpose v a b t@(Tensor ms) =
  case a `sCompare` b of
    SEQ -> t
    SGT -> case sCanTranspose v b a (sing :: Sing l) %~ STrue of
             Proved Refl -> transpose v b a t
    SLT ->
      let sl = sing :: Sing l
          sh = sHead' sl
          sv = sFst sh
          si = sSnd sh
          st = sTail' sl
      in withSingI st $
         case sv %~ v of
           Proved Refl -> case si %~ a of
             Proved Refl -> let sl' = sRemoveUntil b sl
                            in withSingI sl' $
                               case sSane sl' %~ STrue of
                                 Proved Refl ->
                                   let tl  = toTListUntil b t
                                       tl' = fmap (\(i:is, val) -> (last is : (init is ++ [i]),val)) tl
                                       tl'' = sortBy (\(i,_) (i',_) -> i `compare` i') tl'
                                   in  fromTList tl''
             Disproved _ -> case sCanTranspose v a b st of
                              STrue -> Tensor $ fmap (fmap (transpose v a b)) ms
           Disproved _ -> case sCanTranspose v a b st of
                            STrue -> Tensor $ fmap (fmap (transpose v a b)) ms

transposeMult :: forall (vs :: VSpace Symbol Nat) (tl :: TransList Symbol) (l :: ILists) v.
                 (IsJust (Transpositions vs tl l) ~ 'True, SingI l) =>
                 Sing vs -> Sing tl -> Tensor l v -> Tensor l v
transposeMult _ _ ZeroTensor = ZeroTensor
transposeMult sv stl t@(Tensor ms) =
    let sl = sing :: Sing l
        sh = sHead' sl
        st = sTail' sl
        sl' = sTail sl
        sts = sTranspositions sv stl sl
    in case sv %~ sFst sh of
         Proved Refl ->
           case sSane sl' %~ STrue of
             Proved Refl ->
               case sts of
                 SJust sts' ->
                   withSingI (sFst (sHead sl)) $
                   withSingI sl' $
                   let VSpace _ dim = fromSing sv
                       ts  = fromSing sts'
                       ts' = go ts $ take (fromIntegral dim) [0..]
                       xs  = toTListWhile t
                       xs' = fmap (\(is, v) -> (transposeIndices ts' is, v)) xs
                       xs'' = sortBy (\(i,_) (i',_) -> i `compare` i') xs'
                   in  fromTList xs''
         Disproved _ ->
           withSingI st $
           case sIsJust (sTranspositions sv stl st) %~ STrue of
             Proved Refl -> Tensor $ fmap (fmap (transposeMult sv stl)) ms
  where
    transposeIndices ts' is = fmap snd $
                              sortBy (\(i,_) (i',_) -> i `compare` i') $
                              zip ts' is

    go :: [(N,N)] -> [Int] -> [Int]
    go [] is = is
    go ((s,t):ts) (i:is)
      | s' == i = t' : go ts is
      | s' >  i = i : go ((s,t):ts) is
     where
      s' = toInt s
      t' = toInt t

toList :: forall l v n.
          (SingI l, SingI n, LengthILs l ~ n) =>
          Tensor l v -> [(Vec n Int, v)]
toList ZeroTensor = []
toList (Scalar s) = [(VNil, s)]
toList (Tensor ms) =
  let st = sTail' (sing :: Sing l)
      sn = sing :: Sing n
      sm = sLengthILs st
  in case st of
       SNil ->
         case sn of
           SS SZ -> fmap (\(i, Scalar s) -> (VCons i VNil, s)) ms
       _    ->
         case sn of
           SS sm' ->
             withSingI sm' $
             case sm %~ sm' of
               Proved Refl ->
                 concat $
                 fmap (\(i, v) -> case v of Tensor t -> fmap (\(is, v') -> (VCons i is, v')) (withSingI st $ toList v)) ms

fromList' :: forall l v n.
             (Sane l ~ True, LengthILs l ~ n) =>
             Sing l -> [(Vec n Int, v)] -> Tensor l v
fromList' sl [] = ZeroTensor
fromList' sl xs =
    let sn = sLengthILs sl
        st = sTail' sl
        sm = sLengthILs st
    in case sn of
         SZ ->
           case sl %~ SNil of
             Proved Refl -> Scalar $ snd (head xs)
         SS sm' ->
           withSingI sm' $
           case sm %~ sm' of
             Proved Refl ->
               withSingI st $
               case sSane st %~ STrue of
                 Proved Refl ->
                       case fmap (\((i `VCons` is),v) -> (i,(is ,v))) xs of
                         xs' -> Tensor $ fmap (fmap (fromList' st)) $ myGroup xs'
  where
    myGroup ys =
      let ys' = groupBy (\(i,_) (i',_) -> i == i') ys
      in fmap (\x -> (fst $ head x, fmap snd x)) ys'

fromList :: forall l v n.
            (SingI l, Sane l ~ True, LengthILs l ~ n) =>
            [(Vec n Int, v)] -> Tensor l v
fromList =
  let sl = sing :: Sing l
  in fromList' sl

toTListWhile :: forall l v vs.
                (SingI l, SingI vs, vs ~ Fst (Head l), Sane l ~ True) =>
                Tensor l v -> [([Int], Tensor (Tail l) v)]
toTListWhile (Tensor ms) =
  let svs = sing :: Sing vs
      sl = sing :: Sing l
      st = sTail' sl
  in case st %~ sTail sl of
       Proved Refl -> fmap (\(i,v) -> (pure i,v)) ms
       Disproved _ ->
         case sSane st %~ STrue of
           Proved Refl ->
             case sTail sl %~ sTail st of
               Proved Refl ->
                 withSingI st $
                 withSingI (sFst (sHead st)) $
                 let ms' = fmap (\(i,v) -> (i,toTListWhile v)) ms
                 in  concat $ fmap (\(i, xs) -> fmap (\(is, v) -> (i:is, v)) xs) ms'

toTListUntil :: forall (a :: Ix Symbol) l l' v.
                (SingI l, SingI l', RemoveUntil a l ~ l', Sane l ~ True, Sane l' ~ True) =>
                Sing a -> Tensor l v -> [([Int], Tensor l' v)]
toTListUntil sa (Tensor ms) =
    let sl = sing :: Sing l
        st = sTail' sl
        sh = sHead' sl
    in case sSnd sh %~ sa of
         Proved Refl -> withSingI st $
                        case st %~ (sing :: Sing l') of
                          Proved Refl -> fmap (\(i,v) -> (pure i,v)) ms
         Disproved _ ->
           withSingI st $
           case sSane st %~ STrue of
             Proved Refl ->
               case sRemoveUntil sa st %~ (sing :: Sing l') of
                 Proved Refl ->
                   let ms' = fmap (\(i,v) -> (i,toTListUntil sa v)) ms
                   in  concat $ fmap (\(i, xs) -> fmap (\(is, v) -> (i:is, v)) xs) ms'

fromTList :: forall l l' v.(Sane l ~ True, Sane l' ~ True, SingI l, SingI l') =>
                           [([Int], Tensor l v)] -> Tensor l' v
fromTList [] = ZeroTensor
fromTList [([],t)] = case (sing :: Sing l) %~ (sing :: Sing l') of
                       Proved Refl -> t
fromTList xs =
    let sl' = sing :: Sing l'
        st' = sTail' sl'
    in withSingI st' $
      case sSane st' of
        STrue -> Tensor $ fmap (fmap fromTList) xs'''
  where
    xs' = fmap (\((i:is),v) -> (i,(is,v))) xs
    xs'' = groupBy (\(i,_) (i',_) -> i == i') xs'
    xs''' = fmap (\x -> (fst $ head x, map snd x)) xs''

delta' :: forall (id :: Symbol) (n :: Nat) (a :: Symbol) (b :: Symbol) (l :: ILists) v.
          (
           KnownNat n,
           Num v,
           '[ '( 'VSpace id n, 'ConCov (a :| '[]) (b :| '[])) ] ~ l,
           Tail' (Tail' l) ~ '[],
           Sane (Tail' l) ~ 'True
          ) =>
          Sing id -> Sing n -> Sing a -> Sing b ->
          Tensor l v
delta' _ _ _ _ = delta

delta :: forall (id :: Symbol) (n :: Nat) (a :: Symbol) (b :: Symbol) (l :: ILists) v.
         (
          '[ '( 'VSpace id n, 'ConCov (a :| '[]) (b :| '[]))] ~ l,
          Tail' (Tail' l) ~ '[],
          Sane (Tail' l) ~ 'True,
          SingI n,
          Num v
         ) => Tensor l v
delta = case (sing :: Sing n) of
          sn -> let x = fromIntegral $ withKnownNat sn $ natVal sn
                in Tensor (f x)
  where
    f x = map (\i -> (i, Tensor [(i, Scalar 1)])) [0..x - 1]

eta' :: forall (id :: Symbol) (n :: Nat) (a :: Symbol) (b :: Symbol) (l :: ILists) v.
        (
         '[ '( 'VSpace id n, 'Cov (a :| '[b])) ] ~ l,
         (a < b) ~ 'True,
         SingI n,
         Num v
        ) =>
        Sing id -> Sing n -> Sing a -> Sing b ->
        Tensor l v
eta' _ _ _ _ = eta

eta :: forall (id :: Symbol) (n :: Nat) (a :: Symbol) (b :: Symbol) (l :: ILists) v.
       (
        '[ '( 'VSpace id n, 'Cov (a :| '[b])) ] ~ l,
        (a < b) ~ 'True,
        SingI n,
        Num v
       ) => Tensor l v
eta = case (sing :: Sing n) of
        sn -> let x = fromIntegral $ withKnownNat sn $ natVal sn
              in Tensor (f x)
  where
    f x = map (\i -> (i, Tensor [(i, Scalar (if i == 0 then 1 else -1))])) [0..x - 1]

etaInv' :: forall (id :: Symbol) (n :: Nat) (a :: Symbol) (b :: Symbol) (l :: ILists) v.
        (
         '[ '( 'VSpace id n, 'Con (a :| '[b])) ] ~ l,
         (a < b) ~ 'True,
         SingI n,
         Num v
        ) =>
        Sing id -> Sing n -> Sing a -> Sing b ->
        Tensor l v
etaInv' _ _ _ _ = etaInv

etaInv :: forall (id :: Symbol) (n :: Nat) (a :: Symbol) (b :: Symbol) (l :: ILists) v.
       (
        '[ '( 'VSpace id n, 'Con (a :| '[b])) ] ~ l,
        (a < b) ~ 'True,
        SingI n,
        Num v
       ) => Tensor l v
etaInv = case (sing :: Sing n) of
        sn -> let x = fromIntegral $ withKnownNat sn $ natVal sn
              in Tensor (f x)
  where
    f x = map (\i -> (i, Tensor [(i, Scalar (if i == 0 then 1 else -1))])) [0..x - 1]

asym :: forall (id :: Symbol) (n :: Nat) (a :: Symbol) (b :: Symbol) (l :: ILists) v.
       (
        '[ '( 'VSpace id n, 'Con (a :| '[b])) ] ~ l,
        (a < b) ~ 'True,
        SingI n,
        Num v
       ) => Tensor l v
asym = case (sing :: Sing n) of
        sn -> let x = fromIntegral $ withKnownNat sn $ natVal sn
              in Tensor (f x)
  where
    f x = fmap (\i -> (i, Tensor $
            fmap (\j -> (j, Scalar (case i `compare` j of
                                      LT -> 1
                                      EQ -> 0
                                      GT -> -1))) [0..x-1])) [0..x-1]

type V4 = 'VSpace "Spacetime" 4
type Up2 a b = 'Con (a :| '[b])
type UpDown a b = 'ConCov (a :| '[]) (b :| '[])

d_ap :: Tensor '[ '(V4, UpDown "p" "a") ] Rational
d_ap = delta

e_ab :: Tensor '[ '(V4, Up2 "a" "b") ] Rational
e_ab = etaInv

as_ab :: Tensor '[ '(V4, Up2 "a" "b") ] Rational
as_ab = asym

someFunc :: IO ()
someFunc = putStrLn "someFunc"
