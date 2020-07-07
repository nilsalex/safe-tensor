{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}

-----------------------------------------------------------------------------
{-|
Module      : Math.Tensor.LinearAlgebra.Matrix
Description : Gaussian elimination subroutines.
Copyright   : (c) Nils Alex, 2020
License     : MIT
Maintainer  : nils.alex@fau.de
Stability   : experimental

Gaussian elimination subroutines.
-}
-----------------------------------------------------------------------------
module Math.Tensor.LinearAlgebra.Matrix
  ( gaussianST
  , gaussianFFST
  , gaussian
  , gaussianFF
  , rrefST
  , rref
  , independentColumns
  , independentColumnsFF
  , independentColumnsRREF
  , independentColumnsVerifiedFF
  , independentColumnsMat
  , independentColumnsMatFF
  , independentColumnsMatRREF
  , pivotsU
  , pivotsUFF
  , findPivotMax
  , findPivotMaxFF
  , findRowPivot
  , isref
  , isrref
  , isrref'
  , verify
  ) where

import Numeric.LinearAlgebra
  ( Matrix
  , Vector
  , Container
  , Extractor (All, Take, Drop)
  , Z
  , toLists
  , rows
  , cols
  , find
  , (¿)
  , (??)
  , (><)
  , (===)
  , rank
  , fromZ
  )
import Numeric.LinearAlgebra.Devel
  ( STMatrix
  , RowOper (AXPY, SCAL, SWAP)
  , ColRange (FromCol)
  , RowRange (Row)
  , freezeMatrix
  , thawMatrix
  , modifyMatrix
  , readMatrix
  , rowOper
  )

import Data.List (maximumBy)

import Control.Monad (foldM)
import Control.Monad.ST
  ( ST
  , runST
  )

-- | Returns the pivot columns of an upper triangular matrix.
--
-- @
-- &#x3BB; let mat = (3 >< 4) [1, 0, 2, -3, 0, 0, 1, 0, 0, 0, 0, 0]
-- &#x3BB; mat
-- (3><4)
--  [ 1.0, 0.0, 2.0, -3.0
--  , 0.0, 0.0, 1.0,  0.0
--  , 0.0, 0.0, 0.0,  0.0 ]
-- &#x3BB; pivotsU mat
-- [0,2]
-- @
--
pivotsU :: Matrix Double -> [Int]
pivotsU mat = go (0,0)
  where
    go (i,j)
      = case findPivot mat e (i,j) of
          Nothing       -> []
          Just (i', j') -> j' : go (i'+1, j'+1)
    maxAbs = maximum $ map (maximum . map abs) $ toLists mat
    e = eps * maxAbs

pivotsUFF :: Matrix Z -> [Int]
pivotsUFF mat = go (0,0)
  where
    go (i,j)
      = case findPivotFF mat (i,j) of
          Nothing       -> []
          Just (i', j') -> j' : go (i'+1, j'+1)

eps :: Double
eps = 1e-12

-- find next pivot in upper triangular matrix
findPivotFF :: Matrix Z -> (Int, Int) -> Maybe (Int, Int)
findPivotFF mat (i, j)
    | n == j = Nothing
    | m == i = Nothing
    | otherwise = case nonZeros of
                    []           -> if n == j+1
                                    then Nothing
                                    else findPivotFF mat (i, j+1)
                    (pi_, pj):_  -> Just (pi_, pj+j)
    where
        m = rows mat
        n = cols mat
        col = mat ¿ [j]
        nonZeros = filter (\(i', _) -> i' >= i) $ find (/= 0) col

findPivot :: Matrix Double -> Double -> (Int, Int) -> Maybe (Int, Int)
findPivot mat e (i, j)
    | n == j = Nothing
    | m == i = Nothing
    | otherwise = case nonZeros of
                    []           -> if n == j+1
                                    then Nothing
                                    else findPivot mat e (i, j+1)
                    (pi_, pj):_  -> Just (pi_, pj+j)
    where
        m = rows mat
        n = cols mat
        col = mat ¿ [j]
        nonZeros = filter (\(i', _) -> i' >= i) $ find ((>= e) . abs) col

-- | Find pivot element below position (i, j) with greatest absolute value in the ST monad.
findPivotMaxFF :: Int -> Int -> Int -> Int -> STMatrix s Z -> ST s (Maybe (Int, Int))
findPivotMaxFF m n i j mat
    | n == j = return Nothing
    | m == i = return Nothing
    | otherwise =
        do
          col      <- mapM (\i' -> do
                                    x <- readMatrix mat i' j
                                    return (i', x))
                      [i..m-1]
          let nonZeros = filter ((/= 0) . snd) col
          case nonZeros of
            []         -> if n == j+1
                          then return Nothing
                          else findPivotMaxFF m n i (j+1) mat
            (pi_,_):_  -> return $ Just (pi_, j)

findPivotMax :: Int -> Int -> Int -> Int -> STMatrix s Double -> ST s (Maybe (Int, Int))
findPivotMax m n i j mat
    | n == j = return Nothing
    | m == i = return Nothing
    | otherwise =
        do
          col      <- mapM (\i' -> do
                                    x <- readMatrix mat i' j
                                    return (i', abs x))
                      [i..m-1]
          let nonZeros = filter ((>= eps) . abs . snd) col
          let (pi_, _) = maximumBy (\(_, x) (_, y) -> x `compare` y) nonZeros
          case nonZeros of
            [] -> if n == j+1
                  then return Nothing
                  else findPivotMax m n i (j+1) mat
            _  -> return $ Just (pi_, j)

findRowPivot :: Int -> Int -> Int -> Int -> STMatrix s Z -> ST s (Maybe Int)
findRowPivot m n i j mat
    | j + 1 > n       = error "out of bounds" -- return Nothing
    | i + 1 > min m n = error "out of bounds" -- return Nothing
    | otherwise =
        do
         row <- mapM (\j' -> do
                              x <- readMatrix mat i j'
                              return (j', x))
                [0 .. j]
         let nonZeros = filter ((/=0) . snd) row
         case nonZeros of
           []        -> return Nothing
           (pj, _):_ -> return $ Just pj

backwardFF' :: Int -> Int -> Int -> Int -> STMatrix s Z -> ST s ()
backwardFF' m n i j mat
      | i == 0 = return ()
      | otherwise = do
    iPivot' <- findRowPivot m n i j mat
    case iPivot' of
        Nothing -> backwardFF' m n (i-1) j mat
        Just pj -> do
                    pv <- readMatrix mat i pj
                    mapM_ (reduce pv pj) [0 .. i-1]
                    backwardFF' m n (i-1) (pj-1) mat
  where
    reduce pv pj r = do
                      Just pr <- findRowPivot m n r pj mat
                      -- prv <- readMatrix mat r pr
                      pjv <- readMatrix mat r pj
                      if pjv == 0
                        then return ()
                        else
                         let op1 = SCAL pv (Row r) (FromCol pr)
                             op2 = AXPY (-pjv) i r (FromCol pj)
                         in do
                             rowOper op1 mat
                             rowOper op2 mat
                             g <- foldM (\acc c -> gcd acc <$> readMatrix mat r c) 0 [pr .. n-1]
                             if g == 0
                               then return()
                               else mapM_ (\c -> modifyMatrix mat r c (`quot` g)) [pr .. n-1]

gaussianFF' :: Int -> Int -> Int -> Int -> STMatrix s Z -> ST s ()
gaussianFF' m n i j mat = do
    iPivot' <- findPivotMaxFF m n i j mat
    case iPivot' of
        Nothing     -> return ()
        Just (r, p) -> do
                          rowOper (SWAP i r (FromCol j)) mat
                          pv <- readMatrix mat i p
                          mapM_ (reduce pv p) [i+1 .. m-1]
                          gaussianFF' m n (i+1) (p+1) mat
  where
    reduce pv p r = do
                      rv <- readMatrix mat r p
                      if rv == 0
                        then return ()
                        else
                         let op1 = SCAL pv (Row r) (FromCol p)
                             op2 = AXPY (-rv) i r (FromCol p)
                         in do
                             rowOper op1 mat
                             rowOper op2 mat
                             g <- foldM (\acc c -> gcd acc <$> readMatrix mat r c) 0 [p .. n-1]
                             if g == 0
                               then return()
                               else mapM_ (\c -> modifyMatrix mat r c (`quot` g)) [p .. n-1]

-- gaussian elimination of sub matrix below position (i, j)
gaussian' :: Int -> Int -> Int -> Int -> STMatrix s Double -> ST s ()
gaussian' m n i j mat = do
    iPivot' <- findPivotMax m n i j mat
    case iPivot' of
        Nothing     -> return ()
        Just (r, p) -> do
                          rowOper (SWAP i r (FromCol j)) mat
                          pv <- readMatrix mat i p
                          mapM_ (reduce pv p) [i+1 .. m-1]
                          gaussian' m n (i+1) (p+1) mat
  where
    reduce pv p r = do
                      rv <- readMatrix mat r p
                      if abs rv < eps
                        then return ()
                        else
                         let frac = -rv / pv
                             op = AXPY frac i r (FromCol p)
                         in do
                             rowOper op mat
                             mapM_ (\j' -> modifyMatrix mat r j' (\x -> if abs x < eps then 0 else x)) [p..n-1]

gaussianFFST :: Int -> Int -> STMatrix s Z -> ST s ()
gaussianFFST m n = gaussianFF' m n 0 0

-- | Gaussian elimination perfomed in-place in the @'ST'@ monad.
gaussianST :: Int -> Int -> STMatrix s Double -> ST s ()
gaussianST m n = gaussian' m n 0 0

rrefST :: Int -> Int -> STMatrix s Z -> ST s ()
rrefST m n mat = do
                    gaussianFF' m n 0 0 mat
                    backwardFF' m n (r'-1) (n-1) mat
    where
        r' = min m n

isref :: (Num a, Ord a, Container Vector a) => Matrix a -> Bool
isref mat = case pivot of
              []      -> True
              (r,p):_ -> (r <= 0)
                           &&
                             (let leftMat  = mat ?? (Drop 1, Take (p+1))
                                  rightMat = mat ?? (Drop 1, Drop (p+1))
                                  leftZero = null $ find (/=0) leftMat
                                  rightRef = isref rightMat
                              in leftZero && rightRef)
    where
        pivot = find (/=0) mat

isrref' :: (Num a, Ord a, Container Vector a) => Int -> Matrix a -> Bool
isrref' r mat = case pivot of
              []       -> True
              (r',p):_ -> (r' <= 0)
                           && (let leftMat  = subMat ?? (Drop 1, Take (p+1))
                                   col      = mat ¿ [p]
                                   colSingleton = case find (/=0) col of
                                                    [_] -> True
                                                    _   -> False
                                   leftZero = null $ find (/=0) leftMat
                                   nextRref = isrref' (r+1) mat
                               in leftZero && colSingleton && nextRref)
    where
        subMat = mat ?? (Drop r, All)
        pivot  = find (/=0) subMat

isrref :: (Num a, Ord a, Container Vector a) => Matrix a -> Bool
isrref = isrref' 0

rref :: Matrix Z -> Matrix Z
rref mat = runST $ do
    matST <- thawMatrix mat
    rrefST m n matST
    freezeMatrix matST
  where
    m = rows mat
    n = cols mat

gaussianFF :: Matrix Z -> Matrix Z
gaussianFF mat = runST $ do
    matST <- thawMatrix mat
    gaussianFFST m n matST
    freezeMatrix matST
  where
    m = rows mat
    n = cols mat

-- | Gaussian elimination as pure function. Involves a copy of the input matrix.
--
-- @
-- &#x3BB; let mat = (3 >< 4) [1, 1, -2, 0, 0, 2, -6, -4, 3, 0, 3, 1]
-- &#x3BB; mat
-- (3><4)
--  [ 1.0, 1.0, -2.0,  0.0
--  , 0.0, 2.0, -6.0, -4.0
--  , 3.0, 0.0,  3.0,  1.0 ]
-- &#x3BB; gaussian mat
-- (3><4)
--  [ 3.0, 0.0,  3.0,                1.0
--  , 0.0, 2.0, -6.0,               -4.0
--  , 0.0, 0.0,  0.0, 1.6666666666666667 ]
-- @
--
gaussian :: Matrix Double -> Matrix Double
gaussian mat = runST $ do
    matST <- thawMatrix mat
    gaussianST m n matST
    freezeMatrix matST
  where
    m = rows mat
    n = cols mat

independentColumnsRREF :: Matrix Z -> [Int]
independentColumnsRREF mat = pivotsUFF mat'
    where
        mat' = rref mat

independentColumnsFF :: Matrix Z -> [Int]
independentColumnsFF mat = pivotsUFF mat'
    where
        mat' = gaussianFF mat

independentColumnsVerifiedFF :: Matrix Z -> [Int]
independentColumnsVerifiedFF mat
        | isref mat' && verify mat mat'
                     = pivotsUFF mat'
        | otherwise  = error "could not verify row echelon form"
    where
        mat' = gaussianFF mat

-- | Returns the indices of a maximal linearly independent subset of the columns
--   in the matrix.
--
-- @
-- &#x3BB; let mat = (3 >< 4) [1, 1, -2, 0, 0, 2, -6, -4, 3, 0, 3, 1]
-- &#x3BB; mat
-- (3><4)
--  [ 1.0, 1.0, -2.0,  0.0
--  , 0.0, 2.0, -6.0, -4.0
--  , 3.0, 0.0,  3.0,  1.0 ]
-- &#x3BB; independentColumns mat
-- [0,1,3]
-- @
--
independentColumns :: Matrix Double -> [Int]
independentColumns mat = pivotsU mat'
    where
        mat' = gaussian mat

verify :: Matrix Z -> Matrix Z -> Bool
verify mat ref = rank1 == rank2 && rank1 == rank3
    where
        matD = fromZ mat :: Matrix Double
        refD = fromZ ref :: Matrix Double
        rank1 = rank matD
        rank2 = rank refD
        rank3 = rank $ matD === refD

independentColumnsMatRREF :: Matrix Z -> Matrix Z
independentColumnsMatRREF mat =
  case independentColumnsRREF mat of
    [] -> (rows mat >< 1) $ repeat 0
    cs -> mat ¿ cs

independentColumnsMatFF :: Matrix Z -> Matrix Z
independentColumnsMatFF mat =
  case independentColumnsFF mat of
    [] -> (rows mat >< 1) $ repeat 0
    cs -> mat ¿ cs

-- | Returns a sub matrix containing a maximal linearly independent subset of
--   the columns in the matrix.
--
-- @
-- &#x3BB; let mat = (3 >< 4) [1, 1, -2, 0, 0, 2, -6, -4, 3, 0, 3, 1]
-- &#x3BB; mat
-- (3><4)
--  [ 1.0, 1.0, -2.0,  0.0
--  , 0.0, 2.0, -6.0, -4.0
--  , 3.0, 0.0,  3.0,  1.0 ]
-- &#x3BB; independentColumnsMat mat
-- (3><3)
--  [ 1.0, 1.0,  0.0
--  , 0.0, 2.0, -4.0
--  , 3.0, 0.0,  1.0 ]
-- @
--
independentColumnsMat :: Matrix Double -> Matrix Double
independentColumnsMat mat =
  case independentColumns mat of
    [] -> (rows mat >< 1) $ repeat 0
    cs -> mat ¿ cs
