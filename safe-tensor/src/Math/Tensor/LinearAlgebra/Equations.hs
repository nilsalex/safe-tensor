-----------------------------------------------------------------------------
{-|
Module      : Math.Tensor.LinearAlgebra.Equations
Description : Linear tensor equations.
Copyright   : (c) Nils Alex, 2020
License     : MIT
Maintainer  : nils.alex@fau.de
Stability   : experimental

Linear tensor equations.
-}
-----------------------------------------------------------------------------
module Math.Tensor.LinearAlgebra.Equations
  ( tensorToEquations
  , equationFromRational
  , equationsToSparseMat
  , equationsToMat
  , tensorsToSparseMat
  , tensorsToMat
  , equationRank
  , systemRank
  , Solution(..)
  , fromRref
  , fromRow
  , applySolution
  , solveTensor
  , solveSystem
  , redefineIndets
  ) where

import Math.Tensor
import Math.Tensor.LinearAlgebra.Scalar
import Math.Tensor.LinearAlgebra.Matrix

import qualified Numeric.LinearAlgebra.Data as HM
import Numeric.LinearAlgebra (rank)

import Data.Maybe (mapMaybe)
import qualified Data.IntMap.Strict as IM
import Data.List (nub,sort)
import Data.Ratio

tensorToEquations :: Integral a => T (Poly Rational) -> [IM.IntMap a]
tensorToEquations = nub . sort . fmap (equationFromRational . normalize . snd) . toListT

equationFromRational :: Integral a => Poly Rational -> IM.IntMap a
equationFromRational (Affine x (Lin lin))
    | x == 0 = lin'
    | otherwise = error "affine equation not supported for the moment!"
  where
    fac = IM.foldl' (\acc v -> lcm (fromIntegral (denominator v)) acc) 1 lin
    lin' = IM.map (\v -> fromIntegral (numerator (fromIntegral fac * v))) lin
equationFromRational _ = error "equation can only be extracted from linear scalar!"

equationsToSparseMat :: Integral a => [IM.IntMap a] -> [((Int,Int), a)]
equationsToSparseMat xs = concat $ zipWith (\i m -> fmap (\(j,v) -> ((i,j),v)) (IM.assocs m)) [1..] xs

equationsToMat :: Integral a => [IM.IntMap a] -> [[a]]
equationsToMat eqns = mapMaybe (\m -> if IM.null m
                                      then Nothing
                                      else Just $ fmap (\j -> IM.findWithDefault 0 j m) [1..maxVar]) eqns
  where
    maxVar = maximum $ mapMaybe ((fmap fst) . IM.lookupMax) eqns

tensorsToSparseMat :: Integral a => [T (Poly Rational)] -> [((Int,Int), a)]
tensorsToSparseMat = equationsToSparseMat . concat . fmap tensorToEquations

tensorsToMat :: Integral a => [T (Poly Rational)] -> [[a]]
tensorsToMat = equationsToMat . concat . fmap tensorToEquations

equationRank :: T (Poly Rational) -> Int
equationRank t = rank (mat :: HM.Matrix HM.R)
  where
    iMat = case equationsToMat $ tensorToEquations t of
             [] -> [[0]]
             xs -> xs
    mat = HM.fromLists $ fmap (fmap fromIntegral) iMat

systemRank :: [T (Poly Rational)] -> Int
systemRank sys = rank (mat :: HM.Matrix HM.R)
  where
    iMat = case tensorsToMat sys of
             [] -> [[0]]
             xs -> xs
    mat = HM.fromLists $ fmap (fmap fromIntegral) iMat

type Solution = IM.IntMap (Poly Rational)

fromRref :: HM.Matrix HM.Z -> Solution
fromRref ref = IM.fromList assocs
  where
    rows   = HM.toLists ref
    assocs = mapMaybe fromRow rows

fromRow :: Integral a => [a] -> Maybe (Int, Poly Rational)
fromRow xs = case assocs of
               []             -> Nothing
               [(i,_)]        -> Just (i, Const 0)
               (i, v):assocs' -> let assocs'' = fmap (\(i,v') -> (i, - (fromIntegral v') / (fromIntegral v))) assocs'
                                 in Just (i, Affine 0 (Lin (IM.fromList assocs'')))
  where
    assocs = filter ((/=0). snd) $ zip [1..] xs

applySolution :: Solution -> Poly Rational -> Poly Rational
applySolution s p@(Affine x (Lin lin))
    | x == 0 = case p of
                 Affine x (Lin linFin) -> if IM.null linFin
                                          then Const x
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

solveTensor :: Solution -> T (Poly Rational) -> T (Poly Rational)
solveTensor sol = removeZerosT . fmap (applySolution sol)

solveSystem :: [T (Poly Rational)] -> [T (Poly Rational)] -> [T (Poly Rational)]
solveSystem system indets
    | wrongSolution = error "Wrong solution found. May be an Int64 overflow."
    | otherwise     = indets'
  where
    mat = HM.fromLists $ tensorsToMat system
    ref = rref mat
    wrongSolution = not (isrref ref && verify mat ref)
    sol = fromRref ref
    indets' = fmap (solveTensor sol) indets

redefineIndets :: [T (Poly v)] -> [T (Poly v)]
redefineIndets indets = fmap (fmap (\v -> case v of
                                            Const c -> Const c
                                            NotSupported -> NotSupported
                                            Affine a (Lin lin) ->
                                              Affine a (Lin (IM.mapKeys (varMap IM.!) lin)))) indets
  where
    comps = fmap snd $ concat $ fmap toListT indets
    vars = nub $ concat $ mapMaybe (\v -> case v of
                                            Affine _ (Lin lin) -> Just $ IM.keys lin
                                            _                  -> Nothing) comps
    varMap = IM.fromList $ zip vars [1..]
