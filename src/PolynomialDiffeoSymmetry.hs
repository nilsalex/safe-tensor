{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}

module PolynomialDiffeoSymmetry where

import TH
import Tensor
import Scalar
import Delta
import Area
import Sym2
import Epsilon

import Data.Singletons
import Data.Singletons.Prelude

import Control.Monad.Except
import Data.Ratio

import Data.List.NonEmpty (NonEmpty(..))

somePolyAns0 :: (MonadError String m, Num v, Eq v) =>
                Demote Symbol -> Demote Symbol -> m (T (Poly v))
somePolyAns0 p q = do
    e  <- someEtaInv "ST" 4 p q
    scalar (singletonPoly 0 1 1) .* e

somePolyAns4 :: (MonadError String m, Eq v, Num v) =>
                Demote Symbol -> Demote Symbol -> Demote Symbol -> m (T (Poly v))
somePolyAns4 a p q = do
    epq  <- someEtaInv "ST" 4 p q
    eps  <- someEpsilon "ST" 4 ["a","b","c","d"]
    eac  <- someEta "ST" 4 "a" "c"
    ebd  <- someEta "ST" 4 "b" "d"

    i    <- someInjAreaCon "ST" "a" "b" "c" "d" a
  
    a1_  <- epq .* eps
    a1   <- fmap (fmap (\v -> if denominator v == 1
                              then singletonPoly 0 2 (fromIntegral (numerator v))
                              else error "")) $ fmap contractT $ i .* a1_

    a2_  <- (epq .*) =<< (eac .* ebd)
    a2   <- fmap (fmap (\v -> if denominator v == 1
                              then singletonPoly 0 3 (fromIntegral (numerator v))
                              else error "")) $ fmap contractT $ i .* a2_

    a3_  <- (eac .*) =<< (dpd .* dqb)
    a3   <- fmap (fmap (\v -> if denominator v == 1
                              then singletonPoly 0 4 (fromIntegral (numerator v))
                              else error "")) $ fmap contractT $ i .* a3_

    (a1 .+) =<< (a2 .+ a3)



  where
    dpd = someDelta "ST" 4 p "d"
    dqb = someDelta "ST" 4 q "b"

polyDensDiffeoEqn :: (Num v, Eq v, MonadError String m) =>
                     T v -> T v -> m (T v)
polyDensDiffeoEqn ansatz0 ansatz4 = do
    e1 <- fmap contractT $ (ansatz4 .*) =<< (c .* n)
    dp <- d .* ansatz0
    e2 <- scalar (-1) .* dp
    e3 <- transposeT (VSpace "ST" 4) (ICon "m") (ICon "p") dp
    e4 <- transposeT (VSpace "ST" 4) (ICon "m") (ICon "q") dp
    res <- (e1 .+) =<< ((e2 .+) =<< (e3 .+ e4))
    case rankT res of
      [(VSpace "ST" 4, ConCov ("m" :| ["p","q"]) ("n" :| []))] -> return res
      _ -> throwError $ "polyDensDiffeoEqn: inconsistent ansatz ranks\n" ++
                        show (rankT ansatz0) ++ "\n" ++
                        show (rankT ansatz4)
  where
    c = someInterAreaCon "ST" "m" "n" "A" "B"
    d = someDelta "ST" 4 "m" "n"
    n = someFlatAreaCon "ST" "B"

polyScalarDiffeoEqn :: (Num v, Eq v, MonadError String m) =>
                       T v -> T v -> m (T v)
polyScalarDiffeoEqn ansatz0 ansatz4 = do
    e1 <- fmap contractT $ (ansatz4 .*) =<< (c .* n)
    dp <- d .* ansatz0
    e2 <- transposeT (VSpace "ST" 4) (ICon "m") (ICon "p") dp
    e3 <- transposeT (VSpace "ST" 4) (ICon "m") (ICon "q") dp
    res <- (e1 .+) =<< (e2 .+ e3)
    case rankT res of
      [(VSpace "ST" 4, ConCov ("m" :| ["p","q"]) ("n" :| []))] -> return res
      _ -> throwError $ "polyDensDiffeoEqn: inconsistent ansatz ranks\n" ++
                        show (rankT ansatz0) ++ "\n" ++
                        show (rankT ansatz4)
  where
    c = someInterAreaCon "ST" "m" "n" "A" "B"
    d = someDelta "ST" 4 "m" "n"
    n = someFlatAreaCon "ST" "B"
