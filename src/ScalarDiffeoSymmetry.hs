{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}

module ScalarDiffeoSymmetry where

import TH
import Tensor
import Scalar
import Area
import Sym2
import Epsilon
import Delta

import Data.Singletons
import Data.Singletons.Prelude

import Control.Monad.Except
import Data.Ratio

import Data.List.NonEmpty (NonEmpty(..))

someScalarAns0 :: (Num v, Eq v) =>
                  T (Poly v)
someScalarAns0 = scalar (singletonPoly 0 1 1)

someScalarAns4 :: (MonadError String m, Eq v, Num v) =>
                  Demote Symbol -> m (T (Poly v))
someScalarAns4 a = do
    eps  <- someEpsilon "ST" 4 ["a","b","c","d"]
    eac  <- someEta "ST" 4 "a" "c"
    ebd  <- someEta "ST" 4 "b" "d"

    i    <- someInjAreaCon "ST" "a" "b" "c" "d" a
  
    a1   <- fmap (fmap (\v -> if denominator v == 1
                              then singletonPoly 0 2 (fromIntegral (numerator v))
                              else error "")) $ fmap contractT $ i .* eps

    a2_  <- eac .* ebd
    a2   <- fmap (fmap (\v -> if denominator v == 1
                              then singletonPoly 0 3 (fromIntegral (numerator v))
                              else error "")) $ fmap contractT $ i .* a2_

    a1 .+ a2

scalarDiffeoEqn :: (Num v, Eq v, MonadError String m) =>
                   T v -> T v -> m (T v)
scalarDiffeoEqn ansatz0 ansatz4 = do
    e  <- fmap contractT $ (ansatz4 .*) =<< (c .* n)
    case rankT e of
      [(VSpace "ST" 4, ConCov ("m" :| []) ("n" :| []))] -> return e
      _ -> throwError $ "scalarDiffeoEqn: inconsistent ansatz ranks\n" ++
                        show (rankT ansatz0) ++ "\n" ++
                        show (rankT ansatz4)
  where
    c = someInterAreaCon "ST" "m" "n" "A" "B"
    n = someFlatAreaCon "ST" "B"

densityDiffeoEqn :: (Num v, Eq v, MonadError String m) =>
                    T v -> T v -> m (T v)
densityDiffeoEqn ansatz0 ansatz4 = do
    e1 <- fmap contractT $ (ansatz4 .*) =<< (c .* n)
    e2 <- (scalar (-1) .*) =<< (ansatz0 .* someDelta "ST" 4 "m" "n")
    e  <- e1 .+ e2
    case rankT e of
      [(VSpace "ST" 4, ConCov ("m" :| []) ("n" :| []))] -> return e
      _ -> throwError $ "densityDensDiffeoEqn: inconsistent ansatz ranks\n" ++
                        show (rankT ansatz0) ++ "\n" ++
                        show (rankT ansatz4)
  where
    c = someInterAreaCon "ST" "m" "n" "A" "B"
    n = someFlatAreaCon "ST" "B"
