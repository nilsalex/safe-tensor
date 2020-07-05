{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}

-----------------------------------------------------------------------------
{-|
Module      : Math.Tensor.Safe
Description : Dependently typed tensor algebra.
Copyright   : (c) Nils Alex, 2020
License     : MIT
Maintainer  : nils.alex@fau.de
Stability   : experimental

Dependently typed tensor algebra.
-}
-----------------------------------------------------------------------------
module Math.Tensor.Safe
  ( -- * The Tensor GADT
    Tensor(..)
    -- * Generic Rank of a Tensor
    -- |A vector space is the product of a label and a dimension.
  , VSpace(..)
    -- |Type-level naturals used for representing vector space dimensions.
  , N(..)
    -- |The generic tensor rank is a list of vector spaces with label, dimension and
    -- associated index list.
  , GRank
    -- |The rank of a tensor is a generic rank specialized to 'Symbol' and 'N'
  , Rank
  , -- * Conversion from and to lists
    fromList
  , fromList'
  , toList
  , -- * Tensor algebra
    (&+), (&-), (&*), removeZeros
  , -- * Contraction
    contract
  , -- * Transpositions
    transpose
  , transposeMult
  , -- * Relabelling
    relabel
  ) where

import Math.Tensor.Safe.TH
import Math.Tensor.Safe.Proofs

import Data.Kind (Type)

import Data.Constraint hiding (contract)

import Data.Singletons
import Data.Singletons.Prelude
import Data.Singletons.Prelude.Maybe
import Data.Singletons.Decide
import Data.Singletons.TypeLits

import Data.Bifunctor (first,second)
import Data.List (foldl',groupBy,sortBy)

-- |The 'Tensor' type is parameterized by its generalized 'Rank' @r@ and holds
-- arbitrary values @v@.
data Tensor :: Rank -> Type -> Type where
    ZeroTensor :: forall (r :: Rank) v . Sane r ~ 'True => Tensor r v -- ^
    -- A tensor of any sane rank type can be zero.
    Scalar :: forall v. v -> Tensor '[] v -- ^
    -- A tensor of empty rank is a scalar holding some value.
    Tensor :: forall (r :: Rank) (r' :: Rank) v.
              (Sane r ~ 'True, Tail' r ~ r') =>
              [(Int, Tensor r' v)] -> Tensor r v -- ^
    -- A non-zero tensor of sane non-empty rank is represented as an assocs list of
    -- component-value pairs. The keys must be unique and in ascending order.
    -- The values are tensors of the next-lower rank.

deriving instance Eq v => Eq (Tensor r v)
deriving instance Show v => Show (Tensor r v)

instance Functor (Tensor r) where
  fmap f ZeroTensor = ZeroTensor
  fmap f (Scalar s) = Scalar $ f s
  fmap f (Tensor ms) = Tensor $ fmap (fmap (fmap f)) ms

-- |Union of assocs lists with a merging function if a component is present in both lists
-- and two functions to treat components only present in either list.
unionWith :: (a -> b -> c) -> (a -> c) -> (b -> c) -> [(Int, a)] -> [(Int, b)] -> [(Int, c)]
unionWith _ _ f [] ys = fmap (fmap f) ys
unionWith _ f _ xs [] = fmap (fmap f) xs
unionWith f g h xs@((ix,vx):xs') ys@((iy,vy):ys') =
  case ix `compare` iy of
    LT -> (ix, g vx) : unionWith f g h xs' ys
    EQ -> (ix, f vx vy) : unionWith f g h xs' ys'
    GT -> (iy, h vy) : unionWith f g h xs ys'

-- |Add two sorted assocs lists.
addLists :: (Num a, Eq a) => [(Int, a)] -> [(Int, a)] -> [(Int, a)]
addLists [] ys = ys
addLists xs [] = xs
addLists xs@((ix,vx):xs') ys@((iy,vy):ys') =
  case ix `compare` iy of
    LT -> (ix, vx) : addLists xs' ys
    EQ -> let vz = vx + vy
              zs = addLists xs' ys' in
          if vz == 0
          then zs
          else (ix, vz) : zs
    GT -> (iy, vy) : addLists xs ys'

-- |Given a 'Num' and 'Eq' instance, remove all zero values from the tensor,
-- eventually replacing a zero @Scalar@ or an empty @Tensor@ with @ZeroTensor@.
removeZeros :: (Num v, Eq v) => Tensor r v -> Tensor r v
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

-- |Tensor addition. Ranks of summands and sum coincide.
-- Zero values are removed from the result.
(&+) :: forall (r :: Rank) (r' :: Rank) v.
        ((r ~ r'), Num v, Eq v) =>
        Tensor r v -> Tensor r' v -> Tensor r v
(&+) ZeroTensor t = t
(&+) t ZeroTensor = t
(&+) (Scalar s) (Scalar s') = 
    if s'' == 0 then ZeroTensor else Scalar s''
  where
    s'' = s + s'
(&+) (Tensor xs) (Tensor xs') = removeZeros $ Tensor xs''
    where
       xs'' = unionWith (&+) id id xs xs' 
(&+) _ _ = error "Cannot add scalar and tensor! Should have been caught by the type system!"

infixl 6 &+

-- |Tensor subtraction. Ranks of operands and difference coincide.
-- Zero values are removed from the result.
(&-) :: forall (r :: Rank) (r' :: Rank) v.
        ((r ~ r'), Num v, Eq v) =>
        Tensor r v -> Tensor r' v -> Tensor r v
(&-) t1 t2 = t1 &+ fmap negate t2

infixl 6 &-

-- |Tensor multiplication, ranks of factors passed explicitly as singletons.
mult :: forall (r :: Rank) (r' :: Rank) (r'' :: Rank) v.
               (Num v, Just r'' ~ MergeR r r') =>
               Sing r -> Sing r' -> Tensor r v -> Tensor r' v -> Tensor r'' v
mult _ _ (Scalar s) (Scalar t) = Scalar (s*t)
mult sr sr' (Scalar s) (Tensor ms) =
  case saneTail'Proof sr' of
    Sub Dict -> Tensor $ fmap (fmap (\t -> mult sr (sTail' sr') (Scalar s) t)) ms
mult sr sr' (Tensor ms) (Scalar s) =
  case saneTail'Proof sr of
    Sub Dict -> Tensor $ fmap (fmap (\t -> mult (sTail' sr) sr' t (Scalar s))) ms
mult sr sr' (Tensor ms) (Tensor ms') =
  let sh = sHead' sr
      sh' = sHead' sr'
      st = sTail' sr
      st' = sTail' sr'
  in case saneMergeRProof sr sr' of
       Sub Dict ->
         case sh of
           STuple2 sv si ->
             case sh' of
               STuple2 sv' si' ->
                 case sCompare sv sv' of
                   SLT -> case proofMergeLT sr sr' of
                            Sub Dict ->
                              case saneTail'Proof sr of
                                Sub Dict -> Tensor $ fmap (fmap (\t -> mult st sr' t (Tensor ms'))) ms
                   SGT -> case proofMergeGT sr sr' of
                            Sub Dict ->
                              case saneTail'Proof sr' of
                                Sub Dict -> Tensor $ fmap (fmap (\t -> mult sr st' (Tensor ms) t)) ms'
                   SEQ -> case proofMergeIxNotEQ sr sr' of
                            Sub Dict ->
                              case sIxCompare si si' of
                                SLT -> case proofMergeIxLT sr sr' of
                                         Sub Dict ->
                                           case saneTail'Proof sr of
                                             Sub Dict -> Tensor $ fmap (fmap (\t -> mult st sr' t (Tensor ms'))) ms
                                SGT -> case proofMergeIxGT sr sr' of
                                         Sub Dict ->
                                           case saneTail'Proof sr' of
                                             Sub Dict -> Tensor $ fmap (fmap (\t -> mult sr st' (Tensor ms) t)) ms'
mult sr sr' ZeroTensor ZeroTensor =
  case saneMergeRProof sr sr' of
    Sub Dict -> ZeroTensor
mult sr sr' ZeroTensor (Scalar _) =
  case saneMergeRProof sr sr' of
    Sub Dict -> ZeroTensor
mult sr sr' ZeroTensor (Tensor _) =
  case saneMergeRProof sr sr' of
    Sub Dict -> ZeroTensor
mult sr sr' (Scalar _) ZeroTensor =
  case saneMergeRProof sr sr' of
    Sub Dict -> ZeroTensor
mult sr sr' (Tensor _) ZeroTensor =
  case saneMergeRProof sr sr' of
    Sub Dict -> ZeroTensor

-- |Tensor multiplication. Ranks of factors must not overlap. The Product
-- rank is the merged rank of the factors.
(&*) :: forall (r :: Rank) (r' :: Rank) (r'' :: Rank) v.
               (Num v, Just r'' ~ MergeR r r', SingI r, SingI r') =>
               Tensor r v -> Tensor r' v -> Tensor r'' v
(&*) = mult (sing :: Sing r) (sing :: Sing r')

infixl 7 &*

contract' :: forall (r :: Rank) (r' :: Rank) v.
             (r' ~ ContractR r, Num v, Eq v)
             => Sing r -> Tensor r v -> Tensor r' v
contract' sr t = case sContractR sr %~ sr of
                   Proved Refl -> t
                   Disproved _ -> contract'' sr t

contract'' :: forall (r :: Rank) (r' :: Rank) v.
              (r' ~ ContractR r, Num v, Eq v)
              => Sing r -> Tensor r v -> Tensor r' v
contract'' sr ZeroTensor =
  case saneContractProof sr of
    Sub Dict -> ZeroTensor
contract'' sr (Scalar v) = Scalar v
contract'' sr t@(Tensor ms) =
    case sTail' sr of
       SNil ->
         case singletonContractProof sr of
           Sub Dict -> Tensor ms
       st   ->
         case saneContractProof sr of
           Sub Dict ->
             let st' = sTail' st
                 sh  = sHead' sr
                 sv  = sFst sh
                 si  = sSnd sh
                 sh' = sHead' st
                 sv' = sFst sh'
                 si' = sSnd sh'
             in case sv %== sv' of
                  SFalse ->
                    case contractTailDiffVProof sr of
                      Sub Dict -> removeZeros $ Tensor $ fmap (fmap (contract'' st)) ms
                  STrue -> case si of
                    SICon sa -> case si' of
                      SICov sb -> case sa %== sb of
                        STrue -> 
                          let ms' = fmap (\(i, v) -> case v of
                                                       Tensor vs ->
                                                         case filter (\(i', _) -> i == i') vs of
                                                              [] -> Nothing
                                                              [(_, v')] -> Just v'
                                                              _ -> error "duplicate key in tensor assoc list") ms
                              ms'' = filter (\case
                                                 Nothing -> False
                                                 Just x' -> True) ms'
                              ms''' = fmap (\(Just x) -> x) ms'' :: [Tensor (Tail' (Tail' r)) v]
                          in  case saneTail'Proof sr of
                                Sub Dict ->
                                  case saneTail'Proof st of
                                    Sub Dict ->
                                      case contractTailSameVSameIProof sr of
                                        Sub Dict -> contract' st' $ foldl' (&+) ZeroTensor ms'''
                        SFalse ->
                          case contractTailSameVDiffIProof sr of
                            Sub Dict -> removeZeros $ Tensor $ fmap (fmap (contract'' st)) ms
                      SICon _ ->
                        case contractTailSameVNoCovProof sr of
                          Sub Dict -> removeZeros $ Tensor $ fmap (fmap (contract'' st)) ms
                    SICov _ ->
                      case contractTailSameVNoConProof sr of
                        Sub Dict -> removeZeros $ Tensor $ fmap (fmap (contract'' st)) ms

-- |Tensor contraction. Contracting a tensor is the identity function on non-contractible tensors.
-- Otherwise, the result is the contracted tensor with the contracted labels removed from the rank.
contract :: forall (r :: Rank) (r' :: Rank) v.
            (r' ~ ContractR r, SingI r, Num v, Eq v)
            => Tensor r v -> Tensor r' v
contract = contract' (sing :: Sing r)

-- |Tensor transposition. Given a vector space and two index labels, the result is a tensor with
-- the corresponding entries swapped. Only possible if the indices are part of the rank. The
-- rank remains untouched.
transpose :: forall (vs :: VSpace Symbol N) (a :: Ix Symbol) (b :: Ix Symbol) (r :: Rank) v.
              (CanTranspose vs a b r ~ 'True, SingI r) =>
              Sing vs -> Sing a -> Sing b -> Tensor r v -> Tensor r v
transpose _ _ _ ZeroTensor = ZeroTensor
transpose _ _ _ (Scalar _) = error "This is not possible, might yet have to convince the type system."
transpose v a b t@(Tensor ms) =
  case a `sCompare` b of
    SEQ -> t
    SGT -> case sCanTranspose v b a (sing :: Sing r) %~ STrue of
             Proved Refl -> transpose v b a t
    SLT ->
      let sr = sing :: Sing r
          sh = sHead' sr
          sv = sFst sh
          si = sSnd sh
          st = sTail' sr
      in withSingI st $
         case sv %~ v of
           Proved Refl -> case si %~ a of
             Proved Refl -> let sr' = sRemoveUntil b sr
                            in withSingI sr' $
                               case sSane sr' %~ STrue of
                                 Proved Refl ->
                                   let tl  = toTListUntil b t
                                       tl' = fmap (\(i:is, val) -> (last is : (init is ++ [i]),val)) tl
                                       tl'' = sortBy (\(i,_) (i',_) -> i `compare` i') tl'
                                   in  fromTList tl''
             Disproved _ -> case sCanTranspose v a b st of
                              STrue -> Tensor $ fmap (fmap (transpose v a b)) ms
           Disproved _ -> case sCanTranspose v a b st of
                            STrue -> Tensor $ fmap (fmap (transpose v a b)) ms

-- |Transposition of multiple labels. Given a vector space and a list of transpositions, the
-- result is a tensor with the corresponding entries swapped. Only possible if the indices are
-- part of the rank. The rank remains untouched.
transposeMult :: forall (vs :: VSpace Symbol N) (tl :: TransList Symbol) (r :: Rank) v.
                 (IsJust (Transpositions vs tl r) ~ 'True, SingI r) =>
                 Sing vs -> Sing tl -> Tensor r v -> Tensor r v
transposeMult _ _ ZeroTensor = ZeroTensor
transposeMult sv stl t@(Tensor ms) =
    let sr = sing :: Sing r
        sh = sHead' sr
        st = sTail' sr
        sr' = sTail sr
        sts = sTranspositions sv stl sr
    in case sv %~ sFst sh of
         Proved Refl ->
           case sSane sr' %~ STrue of
             Proved Refl ->
               case sts of
                 SJust sts' ->
                   withSingI (sFst (sHead sr)) $
                   withSingI sr' $
                   let sn = sLengthIL (sSnd (sHead sr))
                       n  = fromSing sn
                       ts  = fromSing sts'
                       ts' = go ts $ take' n 0
                       xs  = toTListWhile t
                       xs' = fmap (first (transposeIndices ts')) xs
                       xs'' = sortBy (\(i,_) (i',_) -> i `compare` i') xs'
                   in  fromTList xs''
         Disproved _ ->
           withSingI st $
           case sIsJust (sTranspositions sv stl st) %~ STrue of
             Proved Refl -> Tensor $ fmap (fmap (transposeMult sv stl)) ms
  where
    take' Z i = [i]
    take' (S n) i = i : take' n (i+1)

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

-- |Tensor relabelling. Given a vector space and a list of relabellings, the result is a tensor
-- with the resulting rank after relabelling. Only possible if labels to be renamed are part of
-- the rank and if uniqueness of labels after relabelling is preserved.
relabel :: forall (vs :: VSpace Symbol N) (rl :: RelabelList Symbol) (r1 :: Rank) (r2 :: Rank) v.
                 (RelabelR vs rl r1 ~ 'Just r2, Sane r2 ~ 'True, SingI r1, SingI r2) =>
                 Sing vs -> Sing rl -> Tensor r1 v -> Tensor r2 v
relabel _ _ ZeroTensor = ZeroTensor
relabel sv srl t@(Tensor ms) =
    let sr1 = sing :: Sing r1
        sr2 = sing :: Sing r2
        sh = sHead' sr1
        sr1' = sTail' sr1
        sr2' = sTail' sr2
        sr1'' = sTail sr1
        sts = sRelabelTranspositions srl (sSnd (sHead sr1))
    in case sv %~ sFst sh of
         Proved Refl ->
           case sSane sr1'' %~ STrue of
             Proved Refl ->
               case sts of
                 SJust sts' ->
                   withSingI (sFst (sHead sr1)) $
                   withSingI sr1'' $
                   let sn = sLengthIL (sSnd (sHead sr1))
                       n  = fromSing sn
                       ts  = fromSing sts'
                       ts' = go ts $ take' n 0
                       xs  = toTListWhile t
                       xs' = fmap (first (transposeIndices ts')) xs
                       xs'' = sortBy (\(i,_) (i',_) -> i `compare` i') xs'
                   in  fromTList xs''
         Disproved _ ->
           case sRelabelR sv srl sr1' %~ SJust sr2' of
             Proved Refl ->
               case sSane sr2' %~ STrue of
                 Proved Refl -> withSingI sr1' $ withSingI sr2' $ Tensor $ fmap (fmap (relabel sv srl)) ms
  where
    take' Z i = [i]
    take' (S n) i = i : take' n (i+1)

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

-- |Get assocs list from tensor. Keys are length-indexed vectors of indices.
toList :: forall r v n.
          (SingI r, SingI n, LengthR r ~ n) =>
          Tensor r v -> [(Vec n Int, v)]
toList ZeroTensor = []
toList (Scalar s) = [(VNil, s)]
toList (Tensor ms) =
  let st = sTail' (sing :: Sing r)
      sn = sing :: Sing n
      sm = sLengthR st
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
                 concatMap (\(i, v) -> case v of Tensor t -> fmap (first (VCons i)) (withSingI st $ toList v)) ms

fromList' :: forall r v n.
             (Sane r ~ True, LengthR r ~ n) =>
             Sing r -> [(Vec n Int, v)] -> Tensor r v
fromList' sr [] = ZeroTensor
fromList' sr xs =
    let sn = sLengthR sr
        st = sTail' sr
        sm = sLengthR st
    in case sn of
         SZ ->
           case sr %~ SNil of
             Proved Refl -> Scalar $ snd (head xs)
         SS sm' ->
           withSingI sm' $
           case sm %~ sm' of
             Proved Refl ->
               withSingI st $
               case sSane st %~ STrue of
                 Proved Refl ->
                       case fmap (\(i `VCons` is,v) -> (i,(is ,v))) xs of
                         xs' -> Tensor $ fmap (fromList' st) <$> myGroup xs'
  where
    myGroup ys =
      let ys' = groupBy (\(i,_) (i',_) -> i == i') ys
      in fmap (\x -> (fst $ head x, fmap snd x)) ys'

-- |Construct 'Tensor' from assocs list. Keys are length-indexed vectors of indices.
fromList :: forall r v n.
            (SingI r, Sane r ~ True, LengthR r ~ n) =>
            [(Vec n Int, v)] -> Tensor r v
fromList =
  let sr = sing :: Sing r
  in fromList' sr

-- |Decompose tensor into assocs list with keys being lists of indices for the first vector space
-- and values being the tensors with lower rank for the remaining vector spaces.
toTListWhile :: forall r v.
                (SingI r, Sane r ~ True) =>
                Tensor r v -> [([Int], Tensor (Tail r) v)]
toTListWhile (Tensor ms) =
  let sr = sing :: Sing r
      st = sTail' sr
  in case st %~ sTail sr of
       Proved Refl -> fmap (first pure) ms
       Disproved _ ->
         case sSane st %~ STrue of
           Proved Refl ->
             case sTail sr %~ sTail st of
               Proved Refl ->
                 withSingI st $
                 withSingI (sFst (sHead st)) $
                 let ms' = fmap (second toTListWhile) ms
                 in  concatMap (\(i, xs) -> fmap (first ((:) i)) xs) ms'

-- |Decompose tensor into assocs list with keys being lists of indices up to and including the
-- desired label, and values being tensors of corresponding lower rank.
toTListUntil :: forall (a :: Ix Symbol) r r' v.
                (SingI r, SingI r', RemoveUntil a r ~ r', Sane r ~ True, Sane r' ~ True) =>
                Sing a -> Tensor r v -> [([Int], Tensor r' v)]
toTListUntil sa (Tensor ms) =
    let sr = sing :: Sing r
        st = sTail' sr
        sh = sHead' sr
    in case sSnd sh %~ sa of
         Proved Refl -> withSingI st $
                        case st %~ (sing :: Sing r') of
                          Proved Refl -> fmap (first pure) ms
         Disproved _ ->
           withSingI st $
           case sSane st %~ STrue of
             Proved Refl ->
               case sRemoveUntil sa st %~ (sing :: Sing r') of
                 Proved Refl ->
                   let ms' = fmap (second (toTListUntil sa)) ms
                   in  concatMap (\(i, xs) -> fmap (first ((:) i)) xs) ms'

-- |Construct tensor from assocs list. Keys are lists of indices, values are
-- tensors of lower rank. Used internally for tensor algebra.
fromTList :: forall r r' v.(Sane r ~ True, Sane r' ~ True, SingI r, SingI r') =>
                           [([Int], Tensor r v)] -> Tensor r' v
fromTList [] = ZeroTensor
fromTList xs@((i0,t0):ys)
  | null i0 = if null ys
              then case (sing :: Sing r) %~ (sing :: Sing r') of
                     Proved Refl -> t0
              else error $ "illegal assocs in fromTList : " ++ (show $ (fmap fst) xs)
  | otherwise =
      let sr' = sing :: Sing r'
          st' = sTail' sr'
      in withSingI st' $
        case sSane st' of
          STrue -> Tensor $ fmap (fmap fromTList) xs'''
  where
    xs' = fmap (\(i:is,v) -> (i,(is,v))) xs
    xs'' = groupBy (\(i,_) (i',_) -> i == i') xs'
    xs''' = fmap (\x -> (fst $ head x, map snd x)) xs''
