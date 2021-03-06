{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-----------------------------------------------------------------------------
{-|
Module      : Math.Tensor.LinearAlgebra.Equations
Description : Linear tensor equations.
Copyright   : (c) Nils Alex, 2020
License     : MIT
Maintainer  : nils.alex@fau.de

Linear tensor equations.
-}
-----------------------------------------------------------------------------
module Math.Tensor.LinearAlgebra.Equations
  ( Equation
  , tensorToEquations
  , equationFromRational
  , equationsToSparseMat
  , equationsToMat
  , tensorsToSparseMat
  , tensorsToMat
  , systemRank
  , Solution
  , fromRref
  , fromRrefRev
  , fromRow
  , fromRowRev
  , applySolution
  , solveTensor
  , solveSystem
  , redefineIndets
  ) where

import Math.Tensor
  ( T
  , removeZerosT
  , toListT
  )
import Math.Tensor.LinearAlgebra.Scalar
  ( Poly (Const, Affine, NotSupported)
  , Lin (Lin)
  , polyMap
  , normalize
  )
import Math.Tensor.LinearAlgebra.Matrix
  ( rref
  , isrref
  , verify
  )

import qualified Numeric.LinearAlgebra.Data as HM
  ( Matrix
  , R
  , Z
  , fromLists
  , toLists
  )
import Numeric.LinearAlgebra (rank)

import Data.Maybe (mapMaybe)
import qualified Data.IntMap.Strict as IM
  ( IntMap
  , foldl'
  , map
  , assocs
  , null
  , findWithDefault
  , lookupMax
  , keys
  , fromList
  , (!)
  , difference
  , intersectionWith
  , mapKeys
  , empty
  )
import Data.List (nub, sort)
import Data.Ratio (numerator, denominator)

-- |A linear equation is a mapping from variable
-- indices to coefficients
type Equation a = IM.IntMap a

-- |Extract linear equations from tensor components.
-- The equations are normalized, sorted, and made unique.
tensorToEquations :: Integral a => T (Poly Rational) -> [Equation a]
tensorToEquations = nub . sort . filter (not . IM.null) . fmap (equationFromRational . normalize . snd) . toListT

-- |Extract linear equation with integral coefficients from polynomial
-- tensor component with rational coefficients.
-- Made made integral by multiplying with the @lcm@ of all denominators.
equationFromRational :: forall a.Integral a => Poly Rational -> Equation a
equationFromRational (Affine x (Lin lin))
    | x == 0 = lin'
    | otherwise = error "affine equation not supported for the moment!"
  where
    fac :: a
    fac = IM.foldl' (\acc v -> lcm (fromIntegral (denominator v)) acc) 1 lin
    lin' = IM.map (\v -> fromIntegral (numerator v) * (fac `div` fromIntegral (denominator v))) lin
equationFromRational (Const c)
    | c == 0    = IM.empty
equationFromRational _ = error "equation can only be extracted from linear scalar!"

-- |Convert list of equations to sparse matrix representation of the
-- linear system.
equationsToSparseMat :: [Equation a] -> [((Int,Int), a)]
equationsToSparseMat xs = concat $ zipWith (\i m -> fmap (\(j,v) -> ((i,j),v)) (IM.assocs m)) [1..] xs

-- |Convert list of equations to dense matrix representation of the
-- linear system.
equationsToMat :: Integral a => [Equation a] -> [[a]]
equationsToMat eqns = mapMaybe (\m -> if IM.null m
                                      then Nothing
                                      else Just $ fmap (\j -> IM.findWithDefault 0 j m) [1..maxVar]) eqns
  where
    maxVar = maximum $ mapMaybe (fmap fst . IM.lookupMax) eqns

-- |Extract sparse matrix representation for the linear system given
-- by a list of existentially quantified tensors with polynomial values.
tensorsToSparseMat :: Integral a => [T (Poly Rational)] -> [((Int,Int), a)]
tensorsToSparseMat = equationsToSparseMat . concatMap tensorToEquations

-- |Extract dense matrix representation for the linear system given
-- by a list of existentially quantified tensors with polynomial values.
tensorsToMat :: Integral a => [T (Poly Rational)] -> [[a]]
tensorsToMat = equationsToMat . concatMap tensorToEquations

-- |Rank of a linear system. Uses dense svd provided by hmatrix.
matRank :: forall a.Integral a => [[a]] -> Int
matRank []  = 0
matRank mat = rank (hmat :: HM.Matrix HM.R)
  where
    hmat = HM.fromLists $ fmap (fmap (fromIntegral @a @HM.R)) mat

-- |Rank of the linear system given by a list of existentially
-- quantified tensors with polynomial values.
systemRank :: [T (Poly Rational)] -> Int
systemRank = matRank . tensorsToMat @Int

-- |The solution to a linear system is represented as a list of
-- substitution rules, stored as @'IM.IntMap' ('Poly' 'Rational')@.
type Solution = IM.IntMap (Poly Rational)

-- |Read substitution rules from reduced row echelon form
-- of a linear system.
fromRref :: HM.Matrix HM.Z -> Solution
fromRref ref = IM.fromList assocs
  where
    rows   = HM.toLists ref
    assocs = mapMaybe fromRow rows

fromRrefRev :: HM.Matrix HM.Z -> Solution
fromRrefRev ref = IM.fromList assocs
  where
    rows   = fmap reverse $ HM.toLists ref
    assocs = mapMaybe fromRowRev rows

-- |Read single substitution rule from single
-- row of reduced row echelon form.
fromRow :: forall a.Integral a => [a] -> Maybe (Int, Poly Rational)
fromRow xs = case assocs of
               []             -> Nothing
               [(i,_)]        -> Just (i, Const 0)
               (i, v):assocs' -> let assocs'' = fmap (\(i',v') -> (i', - fromIntegral @a @Rational v' / fromIntegral @a @Rational v)) assocs'
                                 in Just (i, Affine 0 (Lin (IM.fromList assocs'')))
  where
    assocs = filter ((/=0). snd) $ zip [(1::Int)..] xs

fromRowRev :: forall a.Integral a => [a] -> Maybe (Int, Poly Rational)
fromRowRev xs = case assocs of
                  []             -> Nothing
                  [(i,_)]        -> Just (i, Const 0)
                  (i, v):assocs' -> let assocs'' = fmap (\(i',v') -> (i', - fromIntegral @a @Rational v' / fromIntegral @a @Rational v)) assocs'
                                    in Just (i, Affine 0 (Lin (IM.fromList assocs'')))
  where
    assocs = reverse $ filter ((/=0). snd) $ zip [(1::Int)..] xs

-- |Apply substitution rules to tensor component.
applySolution :: Solution -> Poly Rational -> Poly Rational
applySolution s (Affine x (Lin lin))
    | x == 0 = case p of
                 Affine xFin (Lin linFin) -> if IM.null linFin
                                             then Const xFin
                                             else p
                 _ -> p
    | otherwise = error "affine equations not yet supported"
  where
    s' = IM.intersectionWith (\row v -> if v == 0
                                        then error "value 0 encountered in linear scalar"
                                        else polyMap (v*) row) s lin
    lin' = IM.difference lin s
    p0 = if IM.null lin'
         then Const 0
         else Affine 0 (Lin lin')

    p = IM.foldl' (+) p0 s'

    {-
    lin' = IM.foldlWithKey'
             (\lin' i sub ->
                 case Affine 0 (Lin lin') + sub of
                   Affine 0 (Lin lin'') -> IM.delete i lin''
                   Const 0              -> IM.empty
                   _                    -> error "affine equations not yet supported")
             lin s'
    -}
applySolution _ _ = error "only linear equations supported"

-- |Apply substitution rules to all components of a tensor.
solveTensor :: Solution -> T (Poly Rational) -> T (Poly Rational)
solveTensor sol = removeZerosT . fmap (applySolution sol)

-- |Solve a linear system and apply solution to the tensorial
-- indeterminants.
solveSystem ::
     [T (Poly Rational)] -- ^ Tensorial linear system
  -> [T (Poly Rational)] -- ^ List of indeterminant tensors
  -> [T (Poly Rational)] -- ^ Solved indeterminant tensors
solveSystem system indets
    | wrongSolution = error "Wrong solution found. May be an Int64 overflow."
    | otherwise     = indets'
  where
    mat = HM.fromLists $ tensorsToMat @HM.Z system
    ref = rref mat
    wrongSolution = not (isrref ref && verify mat ref)
    sol = fromRref ref
    indets' = fmap (solveTensor sol) indets

-- |Relabelling of the indeterminants present in a list of tensors.
-- Redefines the labels of @n@ indeterminants as @[1..n]@, preserving
-- the previous order.
redefineIndets :: [T (Poly v)] -> [T (Poly v)]
redefineIndets indets = fmap (fmap (\case
                                       Const c -> Const c
                                       NotSupported -> NotSupported
                                       Affine a (Lin lin) ->
                                         Affine a (Lin (IM.mapKeys (varMap IM.!) lin)))) indets
  where
    comps = snd <$> concatMap toListT indets
    vars = nub $ concat $ mapMaybe (\case
                                       Affine _ (Lin lin) -> Just $ IM.keys lin
                                       _                  -> Nothing) comps
    varMap = IM.fromList $ zip vars [(1::Int)..]
