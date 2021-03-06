{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
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

Dependently typed implementation of the Einstein tensor calculus, primarily used
in mathematical physics. For usage examples, see
<https://github.com/nilsalex/safe-tensor/#readme>.
-}
-----------------------------------------------------------------------------
module Math.Tensor.Safe
  ( 
    -- * Tensor calculus
    -- |Given a field \(K\) and a \(K\)-vector space \(V\) of dimension \(n\),
    -- a /tensor/ \(T\) of rank \((r,s)\) is a multilinear map from \(r\)
    -- copies of the dual vector space \(V^\ast\) and \(s\) copies of \(V\)
    -- to \(K\),
    --
    -- \[
    --    T \colon \underbrace{V^\ast \times \dots \times V^\ast}_{r\text{ times}} \times \underbrace{V \times \dots \times V}_{s\text{ times}} \rightarrow K.
    -- \]
    --
    -- The /components/ \(T^{a_1\dots a_r}_{\hphantom{a_1\dots a_r}b_1\dots b_s} \in K\)
    -- with respect to a basis \((e_i)_{i=1\dots n}\) of \(V\) and a corresponding
    -- dual basis \((\epsilon^i)_{i=1\dots n}\) of \(V^\ast\) are the \(n^{r+s}\)
    -- numbers
    --
    -- \[
    --    T^{a_1\dots a_r}_{\hphantom{a_1\dots a_r}b_1\dots b_s} = T(\epsilon^{a_1},\dots,\epsilon^{a_r},e_{b_1},\dots,e_{b_s}).
    -- \]
    --
    -- The upper indices \(a_i\) are called /contravariant/ and the lower indices \(b_i\) are
    -- called /covariant/, reflecting their behaviour under a
    -- [change of basis](https://en.wikipedia.org/wiki/Change_of_basis). From the components
    -- and the basis, the tensor can be reconstructed as
    --
    -- \[
    --    T = T^{a_1\dots a_r}_{\hphantom{a_1\dots a_3}b_1\dots b_s} \cdot e_{a_1} \otimes \dots \otimes e_{a_r} \otimes \epsilon^{b_1} \otimes \dots \otimes \epsilon^{b_s}
    -- \]
    --
    -- using the [Einstein summation convention](https://ncatlab.org/nlab/show/Einstein+summation+convention)
    -- and the [tensor product](https://en.wikipedia.org/wiki/Tensor_product).
    --
    -- The representation of tensors using their components with respect to a fixed but arbitrary
    -- basis forms the foundation of this tensor calculus. An example is the sum of a \((2,0)\) tensor
    -- \(T\) and the transposition of a \((2,0)\) tensor \(S\), which using the calculus can be
    -- written as
    --
    -- \[
    --    \lbrack T + \operatorname{transpose}(S)\rbrack^{a b} = T^{a b} + S^{b a}.
    -- \]
    --
    -- The /generalized rank/ of the tensor \(T^{a b}\) in the above example is the set of
    -- contravariant indices \(\{a, b\}\). The indices must be distinct. The generalized
    -- rank of a tensor with both contravariant and covariant indices
    -- (e.g. \(T^{ac}_{\hphantom{ac}rbl}\)) is the set of contravariant and the
    -- set of covariant indices (e.g. \((\{a,c\}, \{b,l,r\})\)). Note that
    -- both sets need not be distinct, as they label completely different entities
    -- (basis vectors vs. dual basis vectors). Overlapping indices can be removed
    -- by performing a [contraction](https://ncatlab.org/nlab/show/contraction#contraction_of_tensors),
    -- see also @'contract'@.
    --
    -- Tensors with generalized rank can be understood as a
    -- [graded algebra](https://ncatlab.org/nlab/show/graded+algebra) where only
    -- tensors of the same generalized rank can be added together and the tensor product
    -- of two tensors yields a tensor with new generalized rank. Importantly, this product
    -- is only possible if both the contravariant indices and the covariant indices of the
    -- factors do not overlap. As an example, the generalized rank of the tensor product
    -- \(T^{ap}_{\hphantom{ap}fc} S^{eg}_{\hphantom{eg}p}\) would be
    -- \((\{a,e,g,p\},\{c,f,p\})\).
    --
    -- We take this abstraction one step further and consider tensors that are multilinear
    -- maps over potentially different vector spaces and duals thereof. The generalized rank
    -- now consists of the contra- and covariant index sets for each distinct vector space.
    -- Upon multiplication of tensors, only the indices for each vector space must be distinct
    -- and contraction only removes overlapping indices among the same vector space.
    --
    -- Practical examples of configurations with multiple vector spaces are situations where
    -- both the tangent space to spacetime, \(V = T_pM\), and symmetric tensors
    -- \(S^2(V) \subset V\otimes V\), which form a proper subset of \(V\otimes V\),
    -- are considered simultaneously. See also "Math.Tensor.Basic.Sym2".

    -- * Generalized rank
    -- |The tensor calculus described above is now implemented in Haskell. Using @Template Haskell@
    -- provided by the @singletons@ library, this code is lifted to the type level and
    -- singletons are generated.
    --
    -- A vector space is parameterised by a label @a@ and a dimension @b@.
    VSpace(..)
  , -- |Each vector space must have a list of indices. This can be a contravariant index list,
    -- a covariant index list, or both. For @'sane'@ generalized ranks, the individual
    -- lists must be ascending. As already noted, both lists in the mixed case need not
    -- be disjoint.
    IList(..)
  , -- |The generalized tensor rank is a list of vector spaces and associated index lists.
    -- Sane generalized ranks have their vector spaces in ascending order.
    GRank
  , -- |The specialisation used for the parameterisation of the tensor type.
    Rank
  , -- |As explained above, the contravariant or covariant indices for each vector space must
    -- be unique. They must also be /sorted/ for more efficiency. The same applies for the
    -- vector spaces: Each distinct vector space must have a unique representation,
    -- generalized ranks are sorted by the vector spaces. This is checked by the function
    -- @'sane'@.
    sane
  , -- |The function @'headR'@ extracts the first index within a generalized rank.
    -- The first index is always referring to the
    -- first vector space within the rank. If the rank is purely covariant or purley contravariant,
    -- the first index ist the first element of the respective index list. For mixed
    -- ranks, the first index is the one which compares less. If they compare equal, it is always
    -- the contravariant index. This defines an order where contractible indices always appear
    -- next to each other, which greatly facilitates contraction.
    headR
  , -- |The remaining rank after popping the @'headR'@ is obtained by the function @'tailR'@.
    tailR
  , -- |The total number of indices. 
    lengthR
  , -- |A generalized rank is contracted by considering each vector space separately.
    -- Indices appearing in both upper and lower position are removed from the rank.
    -- If that leaves a vector space without indices, it is also discarded.
    contractR
  , -- |Merging two generalized ranks in order to obtain the generalized rank of the
    -- tensor product. Returns @'Nothing'@ for incompatible ranks.
    mergeR
  , -- |To perform transpositions of two indices, single contravariant or covariant indices
    -- have to be specified. A representation for single indices is provided by the sum type @'Ix'@.
    Ix(..)
  , -- |To perform transpositions of multiple indices at once, a list of source
    -- and a list of target indices has to be provided. Both lists must be permutations
    -- of each other. A suitable representation is provided by the sum type @'TransRule'@.
    --
    -- Note that transposing indices in a tensor does not change its generalized rank.
    TransRule (..)
  , -- |To relabel a tensor, a list of source-target pairs has to be provided. Relabelling
    -- affects each index regardless of upper or lower position, so it suffices to have
    -- the type synonym @'RelabelRule'@.
    RelabelRule
  , -- |Relabelling a tensor changes its generalized rank. If tensor indices corresponding
    -- to a given vector space can be relabelled using a given @'RelabelRule'@,
    -- @'relabelR'@ returns the new generalized rank. Otherwise, it returns @'Nothing'@.
    relabelR

  , -- * The Tensor GADT
    -- |The @'Tensor'@ type parameterised by a generalized rank @r@ and a value type @v@
    -- is a recursive container for tensor components of value @v@.
    --
    --   - The base case is a @'Scalar'@, which represents a tensor with empty rank.
    --     A scalar holds a single value of type @v@.
    --
    --   - For non-empty ranks, a tensor is represented of as a mapping from all possible
    --     index values for the first index @'headR' r@ to tensors of lower rank @'tailR' r@,
    --     implemented as sparse ascending assocs list (omitting zero values).
    --
    --   - There is a shortcut for zero tensors, which are represented as @'ZeroTensor'@
    --     regardless of the generalized rank.
    --
    -- Generalized ranks must be @'Sane'@. The empty rank @'[]@ is always sane.
    Tensor(..)
  , -- ** Conversion from and to lists
    -- |A @'Tensor' r v@ can be constructed from a list of key-value pairs,
    -- where keys are length-typed vectors @'Vec'@ of @n = 'lengthR' r@ indices
    -- and values are the corresponding components.
    --
    -- The index values must be given in the order defined by repeatedly applying
    -- @'headR'@ to the rank.
    --
    -- Given a value, such an assocs list is obtained by @'toList'@.
    fromList
  , fromList'
  , toList

  , -- * Basic operations
    -- |We have now everything at our disposal to define basic tensor operations
    -- using the rank-parameterised @'Tensor'@ type. These operations (algebra,
    -- contraction, transposition, relabelling) are /safe/ in the sense that
    -- they can only be performed between tensors of matching type and the
    -- type of the resulting tensor is predetermined. There is also an
    -- existentially quantified variant of these operations available from
    -- "Math.Tensor".

    -- ** Tensor algebra
    (&+), (&-), (&*), removeZeros
  , -- ** Contraction
    contract
  , -- ** Transpositions
    transpose
  , transposeMult
  , -- ** Relabelling
    relabel

  , -- * Length-typed vectors
    -- |Type-level naturals used for tensor construction and also internally.
    N(..)
  , -- |Length-typed vector used for tensor construction and also internally.
    Vec(..)
  , vecFromListUnsafe
  ) where

import Math.Tensor.Safe.TH
import Math.Tensor.Safe.Proofs
import Math.Tensor.Safe.Vector

import Data.Kind (Type)

import Data.Constraint (Dict(Dict), (:-)(Sub))

import Data.Singletons
  ( Sing
  , SingI (sing)
  , withSingI, fromSing
  )
import Data.Singletons.Prelude
import Data.Singletons.Prelude.Maybe
  ( IsJust
  , sIsJust
  )
import Data.Singletons.Decide
  ( Decision (Proved, Disproved)
  , (:~:) (Refl)
  , (%~)
  )
import Data.Singletons.TypeLits (Nat, Symbol)

import Data.Maybe (mapMaybe)
import Data.Bifunctor (first,second)
import Data.List (foldl',groupBy,sortBy)

import Control.DeepSeq (NFData(rnf))

-- |The @'Tensor'@ type parameterized by its generalized rank @r@ and
-- arbitrary value type @v@.
data Tensor :: Rank -> Type -> Type where
    ZeroTensor :: forall (r :: Rank) v . Sane r ~ 'True => Tensor r v
    Scalar :: forall v. !v -> Tensor '[] v
    Tensor :: forall (r :: Rank) (r' :: Rank) v.
              (Sane r ~ 'True, TailR r ~ r') =>
              [(Int, Tensor r' v)] -> Tensor r v

deriving instance Eq v => Eq (Tensor r v)
deriving instance Show v => Show (Tensor r v)

instance NFData v => NFData (Tensor r v) where
    rnf ZeroTensor  = ()
    rnf (Scalar v)  = rnf v
    rnf (Tensor ts) = rnf ts

instance Functor (Tensor r) where
  fmap _ ZeroTensor = ZeroTensor
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

-- |Given a @'Num'@ and @'Eq'@ instance, remove all zero values from the tensor,
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

-- |Tensor addition. Generalized ranks of summands and sum coincide.
-- Zero values are removed from the result.
(&+) :: forall (r :: Rank) (r' :: Rank) v.
        ((r ~ r'), Num v, Eq v) =>
        Tensor r v -> Tensor r' v -> Tensor r v
(&+) ZeroTensor t = t
(&+) t ZeroTensor = t
(&+) (Scalar s) (Scalar s') = Scalar (s + s')
(&+) (Tensor xs) (Tensor xs') = Tensor xs''
    where
       xs'' = unionWith (&+) id id xs xs' 
(&+) _ _ = error "Cannot add scalar and tensor! Should have been caught by the type system!"

infixl 6 &+

-- |Tensor subtraction. Generalized ranks of operands and difference coincide.
-- Zero values are removed from the result.
(&-) :: forall (r :: Rank) (r' :: Rank) v.
        ((r ~ r'), Num v, Eq v) =>
        Tensor r v -> Tensor r' v -> Tensor r v
(&-) t1 t2 = t1 &+ fmap negate t2

infixl 6 &-

-- |Tensor multiplication, ranks @r@, @r'@ of factors passed explicitly as singletons.
-- Rank of result is @'MergeR' r r'@.
mult :: forall (r :: Rank) (r' :: Rank) (r'' :: Rank) v.
               (Num v, 'Just r'' ~ MergeR r r') =>
               Sing r -> Sing r' -> Tensor r v -> Tensor r' v -> Tensor r'' v
mult _ _ (Scalar s) (Scalar t) = Scalar (s*t)
mult sr sr' (Scalar s) (Tensor ms) =
  case saneTailRProof sr' of
    Sub Dict -> Tensor $ fmap (fmap (mult sr (sTailR sr') (Scalar s))) ms
mult sr sr' (Tensor ms) (Scalar s) =
  case saneTailRProof sr of
    Sub Dict -> Tensor $ fmap (fmap (\t -> mult (sTailR sr) sr' t (Scalar s))) ms
mult sr sr' (Tensor ms) (Tensor ms') =
  let sh = sHeadR sr
      sh' = sHeadR sr'
      st = sTailR sr
      st' = sTailR sr'
  in case saneMergeRProof sr sr' of
       Sub Dict ->
         case sh of
           STuple2 sv si ->
             case sh' of
               STuple2 sv' si' ->
                 case sCompare sv sv' of
                   SLT -> case proofMergeLT sr sr' of
                            Sub Dict ->
                              case saneTailRProof sr of
                                Sub Dict -> Tensor $ fmap (fmap (\t -> mult st sr' t (Tensor ms'))) ms
                   SGT -> case proofMergeGT sr sr' of
                            Sub Dict ->
                              case saneTailRProof sr' of
                                Sub Dict -> Tensor $ fmap (fmap (mult sr st' (Tensor ms))) ms'
                   SEQ -> case proofMergeIxNotEQ sr sr' of
                            Sub Dict ->
                              case sIxCompare si si' of
                                SLT -> case proofMergeIxLT sr sr' of
                                         Sub Dict ->
                                           case saneTailRProof sr of
                                             Sub Dict -> Tensor $ fmap (fmap (\t -> mult st sr' t (Tensor ms'))) ms
                                SGT -> case proofMergeIxGT sr sr' of
                                         Sub Dict ->
                                           case saneTailRProof sr' of
                                             Sub Dict -> Tensor $ fmap (fmap (mult sr st' (Tensor ms))) ms'
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

-- |Tensor multiplication. Generalized anks @r@, @r'@ of factors must not overlap. The product
-- rank is the merged rank @'MergeR' r r'@ of the factor ranks.
(&*) :: forall (r :: Rank) (r' :: Rank) (r'' :: Rank) v.
               (Num v, 'Just r'' ~ MergeR r r', SingI r, SingI r') =>
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
contract'' _ (Scalar v) = Scalar v
contract'' sr (Tensor ms) =
    case sTailR sr of
       SNil ->
         case singletonContractProof sr of
           Sub Dict -> Tensor ms
       st   ->
         case saneContractProof sr of
           Sub Dict ->
             let st' = sTailR st
                 sh  = sHeadR sr
                 sv  = sFst sh
                 si  = sSnd sh
                 sh' = sHeadR st
                 sv' = sFst sh'
                 si' = sSnd sh'
             in case sv %== sv' of
                  SFalse ->
                    case contractTailDiffVProof sr of
                      Sub Dict -> Tensor $ fmap (fmap (contract'' st)) ms
                  STrue -> case si of
                    SICon sa -> case si' of
                      SICov sb -> case sa %== sb of
                        STrue -> 
                          let ms' = mapMaybe (\(i, v) -> case v of
                                                           Tensor vs ->
                                                             case filter (\(i', _) -> i == i') vs of
                                                                  [] -> Nothing
                                                                  [(_, v')] -> Just v'
                                                                  _ -> error "duplicate key in tensor assoc list"
                                                           ZeroTensor -> Nothing)
                                             ms :: [Tensor (TailR (TailR r)) v]
                          in  case saneTailRProof sr of
                                Sub Dict ->
                                  case saneTailRProof st of
                                    Sub Dict ->
                                      case contractTailSameVSameIProof sr of
                                        Sub Dict -> contract' st' $ foldl' (&+) ZeroTensor ms'
                        SFalse ->
                          case contractTailSameVDiffIProof sr of
                            Sub Dict -> Tensor $ fmap (fmap (contract'' st)) ms
                      SICon _ ->
                        case contractTailSameVNoCovProof sr of
                          Sub Dict -> Tensor $ fmap (fmap (contract'' st)) ms
                    SICov _ ->
                      case contractTailSameVNoConProof sr of
                        Sub Dict -> Tensor $ fmap (fmap (contract'' st)) ms

-- |Tensor contraction. Contracting a tensor is the identity function on non-contractible tensors.
-- Otherwise, the result is the contracted tensor with the contracted labels removed from the
-- generalized rank.
contract :: forall (r :: Rank) (r' :: Rank) v.
            (r' ~ ContractR r, SingI r, Num v, Eq v)
            => Tensor r v -> Tensor r' v
contract = contract' (sing :: Sing r)

-- |Tensor transposition. Given a vector space and two index labels, the result is a tensor with
-- the corresponding entries swapped. Only possible if the indices are part of the rank. The
-- generalized rank remains untouched.
transpose :: forall (vs :: VSpace Symbol Nat) (a :: Ix Symbol) (b :: Ix Symbol) (r :: Rank) v.
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
          sh = sHeadR sr
          sv = sFst sh
          si = sSnd sh
          st = sTailR sr
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

-- |Transposition of multiple labels. Given a vector space and a transposition rule, the
-- result is a tensor with the corresponding entries swapped. Only possible if the indices are
-- part of the generalized rank. The generalized rank remains untouched.
transposeMult :: forall (vs :: VSpace Symbol Nat) (tl :: TransRule Symbol) (r :: Rank) v.
                 (IsJust (Transpositions vs tl r) ~ 'True, SingI r) =>
                 Sing vs -> Sing tl -> Tensor r v -> Tensor r v
transposeMult _ _ ZeroTensor = ZeroTensor
transposeMult sv stl tens@(Tensor ms) =
    let sr = sing :: Sing r
        sh = sHeadR sr
        st = sTailR sr
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
                       xs  = toTListWhile tens
                       xs' = fmap (first (transposeIndices ts')) xs
                       xs'' = sortBy (\(i,_) (i',_) -> i `compare` i') xs'
                   in  fromTList xs''
         Disproved _ ->
           withSingI st $
           case sIsJust (sTranspositions sv stl st) %~ STrue of
             Proved Refl -> Tensor $ fmap (fmap (transposeMult sv stl)) ms
  where
    take' :: N -> Int -> [Int]
    take' Z i = [i]
    take' (S n) i = i : take' n (i+1)

    transposeIndices :: [Int] -> [Int] -> [Int]
    transposeIndices ts' is = fmap snd $
                              sortBy (\(i,_) (i',_) -> i `compare` i') $
                              zip ts' is

    go :: [(N,N)] -> [Int] -> [Int]
    go [] is = is
    go ((s,t):ts) (i:is) =
      case s' `compare` i of
        EQ -> t' : go ts is
        GT -> i : go ((s,t):ts) is
        LT -> error $ "illegal permutation" <> show ((s,t):ts) <> "\t" <> show (i:is)
     where
      s' = toInt s
      t' = toInt t
    go _ [] = error "cannot transpose elements of empty list"

-- |Tensor relabelling. Given a vector space and a relabelling rule, the result is a tensor
-- with the resulting generalized rank after relabelling. Only possible if labels to be
-- renamed are part of the generalized rank and if uniqueness of labels after
-- relabelling is preserved.
relabel :: forall (vs :: VSpace Symbol Nat) (rl :: RelabelRule Symbol) (r1 :: Rank) (r2 :: Rank) v.
                 (RelabelR vs rl r1 ~ 'Just r2, Sane r2 ~ 'True, SingI r1, SingI r2) =>
                 Sing vs -> Sing rl -> Tensor r1 v -> Tensor r2 v
relabel _ _ ZeroTensor = ZeroTensor
relabel sv srl tens@(Tensor ms) =
    let sr1 = sing :: Sing r1
        sr2 = sing :: Sing r2
        sh = sHeadR sr1
        sr1' = sTailR sr1
        sr2' = sTailR sr2
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
                       xs  = toTListWhile tens
                       xs' = fmap (first (transposeIndices ts')) xs
                       xs'' = sortBy (\(i,_) (i',_) -> i `compare` i') xs'
                   in  fromTList xs''
         Disproved _ ->
           case sRelabelR sv srl sr1' %~ SJust sr2' of
             Proved Refl ->
               case sSane sr2' %~ STrue of
                 Proved Refl -> withSingI sr1' $ withSingI sr2' $ Tensor $ fmap (fmap (relabel sv srl)) ms
  where
    take' :: N -> Int -> [Int]
    take' Z i = [i]
    take' (S n) i = i : take' n (i+1)

    transposeIndices :: [Int] -> [Int] -> [Int]
    transposeIndices ts' is = fmap snd $
                              sortBy (\(i,_) (i',_) -> i `compare` i') $
                              zip ts' is

    go :: [(N,N)] -> [Int] -> [Int]
    go [] is = is
    go ((s,t):ts) (i:is) =
      case s' `compare` i of
        EQ -> t' : go ts is
        GT -> i : go ((s,t):ts) is
        LT -> error $ "illegal permutation" <> show ((s,t):ts) <> "\t" <> show (i:is)
     where
      s' = toInt s
      t' = toInt t
    go _ [] = error "cannot transpose elements of empty list"

-- |Get assocs list from @'Tensor'@. Keys are length-typed vectors of indices.
toList :: forall r v n.
          (SingI r, SingI n, LengthR r ~ n) =>
          Tensor r v -> [(Vec n Int, v)]
toList ZeroTensor = []
toList (Scalar s) = [(VNil, s)]
toList (Tensor ms) =
  let st = sTailR (sing :: Sing r)
      sn = sing :: Sing n
      sm = sLengthR st
  in case st of
       SNil ->
         case sn of
           SS SZ -> mapMaybe (\(i, x) -> case x of
                                           ZeroTensor -> Nothing
                                           Scalar s   -> Just (VCons i VNil, s)) ms
       _    ->
         case sn of
           SS sm' ->
             withSingI sm' $
             case sm %~ sm' of
               Proved Refl ->
                 concatMap (\(i, v) -> case v of
                                         Tensor _   -> fmap (first (VCons i)) (withSingI st $ toList v)
                                         ZeroTensor -> []) ms

-- |Construct @'Tensor'@ from assocs list. Keys are length-typed vectors of indices. Generalized
-- rank is passed explicitly as singleton.
fromList' :: forall r v n.
             (Sane r ~ 'True, LengthR r ~ n) =>
             Sing r -> [(Vec n Int, v)] -> Tensor r v
fromList' _  [] = ZeroTensor
fromList' sr xs =
    let sn = sLengthR sr
        st = sTailR sr
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
    myGroup :: Eq k => [(k,a)] -> [(k, [a])]
    myGroup ys =
      let ys' = groupBy (\(i,_) (i',_) -> i == i') ys
      in fmap (\x -> (fst $ head x, fmap snd x)) ys'

-- |Construct @'Tensor'@ from assocs list. Keys are length-typed vectors of indices.
fromList :: forall r v n.
            (SingI r, Sane r ~ 'True, LengthR r ~ n) =>
            [(Vec n Int, v)] -> Tensor r v
fromList =
  let sr = sing :: Sing r
  in fromList' sr

-- |Decompose tensor into assocs list with keys being lists of indices for the first vector space
-- and values being the tensors with lower rank for the remaining vector spaces.
toTListWhile :: forall r v.
                (SingI r, Sane r ~ 'True) =>
                Tensor r v -> [([Int], Tensor (Tail r) v)]
toTListWhile (Tensor ms) =
  let sr = sing :: Sing r
      st = sTailR sr
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
                 in  concatMap (\(i, xs) -> fmap (first (i :)) xs) ms'

-- |Decompose tensor into assocs list with keys being lists of indices up to and including the
-- desired label, and values being tensors of corresponding lower rank.
toTListUntil :: forall (a :: Ix Symbol) r r' v.
                (SingI r, SingI r', RemoveUntil a r ~ r', Sane r ~ 'True, Sane r' ~ 'True) =>
                Sing a -> Tensor r v -> [([Int], Tensor r' v)]
toTListUntil sa (Tensor ms) =
    let sr = sing :: Sing r
        st = sTailR sr
        sh = sHeadR sr
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
                   in  concatMap (\(i, xs) -> fmap (first (i :)) xs) ms'

-- |Construct tensor from assocs list. Keys are lists of indices, values are
-- tensors of lower rank. Used internally for tensor algebra.
fromTList :: forall r r' v.(Sane r ~ 'True, Sane r' ~ 'True, SingI r, SingI r') =>
                           [([Int], Tensor r v)] -> Tensor r' v
fromTList [] = ZeroTensor
fromTList xs@((i0,t0):ys)
  | null i0 = if null ys
              then case (sing :: Sing r) %~ (sing :: Sing r') of
                     Proved Refl -> t0
              else error $ "illegal assocs in fromTList : " ++ show (fmap fst xs)
  | otherwise =
      let sr' = sing :: Sing r'
          st' = sTailR sr'
      in withSingI st' $
        case sSane st' of
          STrue -> Tensor $ fmap (fmap fromTList) xs'''
  where
    xs' = fmap (\(i:is,v) -> (i,(is,v))) xs
    xs'' = groupBy (\(i,_) (i',_) -> i == i') xs'
    xs''' = fmap (\x -> (fst $ head x, map snd x)) xs''
