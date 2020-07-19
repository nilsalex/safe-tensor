{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}

module EOM where

import Math.Tensor
import Math.Tensor.Safe.TH
import Math.Tensor.Basic

import DiffeoSymmetry

import Data.List.NonEmpty (NonEmpty(..))
import Control.Monad.Except

massive :: Num v => T v -> T v
massive ansatz8 = res
  where
    Right res = runExcept $ scalarT 2 .* ansatz8

kinetic :: (Num v, Eq v, MonadError String m) =>
           T v -> T v -> m (T v)
kinetic ansatz10_1 ansatz10_2 =
    do
      i <- someInjSym2Cov "ST" 4 "p" "q" "I"
      let e1 = ansatz10_1
      e2 <- transposeT (VSpace "STArea" 21) (ICov "A") (ICov "B") ansatz10_1
      e3 <- (scalarT (-2) .*) =<< fmap contractT (i .* ansatz10_2)
      fmap removeZerosT $ (e1 .+) =<< (e2 .+ e3)

noether1 :: (Num v, Eq v, MonadError String m) =>
            T v -> T v -> m (T v)
noether1 ansatz4 ansatz8 = do
    ansatz4' <- relabelT (VSpace "STArea" 21) [("A","B")] ansatz4
    n1 <- (scalarT 2 .*) =<< fmap contractT ((n .*) =<< (ansatz8 .* c2))
    n2 <- (scalarT (-1) .*) =<< fmap contractT (ansatz4' .* c1)
    n3 <- (scalarT (-1) .*) =<< (ansatz4 .* d)
    res <- fmap removeZerosT $ (n3 .+) =<< (n1 .+ n2)
    case rankT res of
      [(VSpace "ST" 4, ConCov ("m" :| []) ("n" :| [])),
       (VSpace "STArea" 21, Cov ("A" :| []))] -> return res
      _ -> throwError $ "noether1: inconsistent ansatz ranks\n" ++
                        show (rankT ansatz4) ++ "\n" ++
                        show (rankT ansatz8)
  where
    d = someDelta "ST" 4 "m" "n"
    n = someFlatAreaCon "ST" "C"
    c1 = someInterAreaCov "ST" "m" "n" "A" "B"
    c2 = someInterAreaCon "ST" "m" "n" "B" "C"

noether2 :: (Num v, Eq v, MonadError String m) =>
            T v -> T v -> m (T v)
noether2 ansatz10_1 ansatz10_2 = do
    kin <- kinetic ansatz10_1 ansatz10_2
    c <- someInterAreaJet2_3 "ST" "m" "n" "B" "C" "I" "p" "q"
    fmap (removeZerosT . contractT) $ (kin .*) =<< (c .* someFlatAreaCon "ST" "C")
