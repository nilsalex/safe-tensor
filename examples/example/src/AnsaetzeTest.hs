{-# LANGUAGE OverloadedStrings #-}

module AnsaetzeTest
  ( calc
  , ans4Test
  , ans6Test
  , ans8Test
  , ans10_1Test
  , ans10_2Test
  , ans12Test
  , ans14_1Test
  , ans14_2Test
  ) where

import DiffeoSymmetry

import Math.Tensor
import Math.Tensor.Safe.TH
import Math.Tensor.Basic
import Math.Tensor.LinearAlgebra

import Math.Tensor.SparseTensor.Ansaetze

import Control.Monad.Except

thrd :: (a,b,c) -> c
thrd (_,_,c) = c

calc :: (Num v, Eq v) => Either String (T v)
calc = runExcept $ do
    e_ab <- someEtaInv "Spacetime" 4 "a" "b"
    e_ac <- someEtaInv "Spacetime" 4 "a" "c"
    prod1 <- e_ab .* d_cp
    prod2 <- e_ac .* d_bp
    prod1 .+ prod2
  where
    d_cp = someDelta "Spacetime" 4 "c" "p"
    d_bp = someDelta "Spacetime" 4 "b" "p"

ans4Test :: (Num v, Eq v) => Either String (T (Poly v))
ans4Test = runExcept $ do
  let c = someInterAreaCon "ST" "m" "n" "A" "B"
  let a = thrd $ someAns4 "ST" "A"
  _eta <- someEtaInv "ST" 4 "p" "n"
  p1 <- c .* a
  p2 <- p1 .* _eta
  let contracted = contractT p2
  trans <- transposeT (VSpace "ST" 4) (ICon "m") (ICon "p") contracted
  fmap removeZerosT $ contracted .- trans

ans6Test :: (Num v, Eq v) => Either String (T (Poly v))
ans6Test = runExcept $ do
  let c = someInterAreaJet2 "ST" "m" "n" "A" "B" "I" "J"
  let a = thrd $ someAns6 "ST" "A" "I"
  _eta <- someEtaInv "ST" 4 "p" "n"
  p1 <- c .* a
  p2 <- p1 .* _eta
  let contracted = contractT p2
  trans <- transposeT (VSpace "ST" 4) (ICon "m") (ICon "p") contracted
  fmap removeZerosT $ contracted .- trans

ans8Test :: (Num v, Eq v) => Either String (T (Poly v))
ans8Test = runExcept $ do
  let c = someInterAreaCon "ST" "m" "n" "A" "C"
  a <- fmap thrd $ someAns8 "ST" "A" "B"
  _eta <- someEtaInv "ST" 4 "p" "n"
  p1 <- c .* a
  p2 <- p1 .* _eta
  let contracted = contractT p2
  trans <- transposeT (VSpace "ST" 4) (ICon "m") (ICon "p") contracted
  sym1 <- contracted .- trans
  trans' <- transposeT (VSpace "STArea" 21) (ICov "B") (ICov "C") sym1
  fmap removeZerosT $ sym1 .+ trans'

ans10_1Test :: (Num v, Eq v) => Either String (T (Poly v))
ans10_1Test = runExcept $ do
  let c1 = someInterAreaCon "ST" "m" "n" "C" "A"
  let c2 = someInterAreaJet2 "ST" "m" "n" "C" "B" "J" "I"
  _eta <- someEtaInv "ST" 4 "x" "n"
  a1 <- fmap thrd $ someAns10_1 "ST" "C" "B" "I"
  a2 <- fmap thrd $ someAns10_1 "ST" "A" "C" "J"
  t1 <- fmap contractT $ a1 .* c1
  t2 <- fmap contractT $ a2 .* c2
  tens <- fmap contractT $ (_eta .*) =<< (t1 .+ t2)
  fmap removeZerosT $ (tens .-) =<< transposeT (VSpace "ST" 4) (ICon "m") (ICon "x") tens

ans10_2Test :: (Num v, Eq v) => Either String (T (Poly v))
ans10_2Test = runExcept $ do
  c <- someInterAreaJet1 "ST" "m" "n" "A" "C" "p" "r"
  a <- fmap thrd $ someAns10_2 "ST" "A" "B" "p" "q"
  _eta <- someEtaInv "ST" 4 "x" "n"
  t <- fmap contractT $ (a .*) =<< (c .* _eta)
  t' <- (t .-) =<< transposeT (VSpace "ST" 4) (ICon "m") (ICon "x") t
  fmap removeZerosT $ (t' .+) =<< (transposeT (VSpace "STArea" 21) (ICov "B") (ICov "C") =<<
                      transposeT (VSpace "ST" 4) (ICon "q") (ICon "r") t')

ans12Test :: (Num v, Eq v) => Either String (T (Poly v))
ans12Test = runExcept $ do
  let c = someInterAreaCon "ST" "m" "n" "D" "A"
  a <- fmap thrd $ someAns12 "ST" "B" "C" "D"
  _eta <- someEtaInv "ST" 4 "p" "n"
  p1 <- c .* a
  p2 <- p1 .* _eta
  let contracted = contractT p2
  trans <- transposeT (VSpace "ST" 4) (ICon "m") (ICon "p") contracted
  sym1 <- contracted .- trans
  trans1 <- transposeMultT (VSpace "STArea" 21) [] [("A","A"),("B","C"),("C","B")] sym1
  trans2 <- transposeMultT (VSpace "STArea" 21) [] [("A","B"),("B","A"),("C","C")] sym1
  trans3 <- transposeMultT (VSpace "STArea" 21) [] [("A","B"),("B","C"),("C","A")] sym1
  trans4 <- transposeMultT (VSpace "STArea" 21) [] [("A","C"),("B","A"),("C","B")] sym1
  trans5 <- transposeMultT (VSpace "STArea" 21) [] [("A","C"),("B","B"),("C","A")] sym1
  fmap removeZerosT $ (trans5 .+) =<< (trans4 .+) =<< (trans3 .+) =<< (trans2 .+) =<< (trans1 .+ sym1)

ans14_1Test :: (Num v, Eq v) => Either String (T (Poly v))
ans14_1Test = runExcept $ do
  let c1 = someInterAreaCon "ST" "m" "n" "D" "B"
  a1 <- fmap thrd $ someAns14_1 "ST" "A" "D" "C" "I"
  let c2 = someInterAreaJet2 "ST" "m" "n" "D" "C" "J" "I"
  a2 <- fmap thrd $ someAns14_1 "ST" "A" "B" "D" "J"
  _eta <- someEtaInv "ST" 4 "x" "n"
  t1 <- fmap contractT $ a1 .* c1
  t1' <- (t1 .+) =<< transposeT (VSpace "STArea" 21) (ICov "A") (ICov "B") t1
  t2 <- fmap contractT $ (_eta .*) =<< ((t1' .+) . contractT =<< (a2 .* c2))
  fmap removeZerosT $ (t2 .-) =<< transposeT (VSpace "ST" 4) (ICon "m") (ICon "x") t2

ans14_2Test :: (Num v, Eq v) => Either String (T (Poly v))
ans14_2Test = runExcept $ do
  let c1 = someInterAreaCon "ST" "m" "n" "D" "A"
  a1 <- fmap thrd $ someAns14_2 "ST" "D" "B" "C" "q" "r"
  c2 <- someInterAreaJet1 "ST" "m" "n" "D" "B" "p" "q"
  a2 <- fmap thrd $ someAns14_2 "ST" "A" "D" "C" "p" "r"
  c3 <- someInterAreaJet1 "ST" "m" "n" "D" "C" "p" "r"
  a3 <- fmap thrd $ someAns14_2 "ST" "A" "D" "B" "p" "q"
  _eta <- someEtaInv "ST" 4 "x" "n"
  t1 <- fmap contractT $ a1 .* c1
  t2 <- fmap contractT $ a2 .* c2
  t3 <- fmap contractT $ a3 .* c3
  t  <- fmap contractT $ (_eta .*) =<< ((t3 .+) =<< (t1 .+ t2))
  fmap removeZerosT $ (t .-) =<< transposeT (VSpace "ST" 4) (ICon "m") (ICon "x") t
