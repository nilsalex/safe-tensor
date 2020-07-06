{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

-----------------------------------------------------------------------------
{-|
Module      : Math.Tensor.Example
Description : Example calculation.
Copyright   : (c) Nils Alex, 2020
License     : MIT
Maintainer  : nils.alex@fau.de
Stability   : experimental

Example calculation.
-}
-----------------------------------------------------------------------------

module Math.Tensor.Example
  ( sol
  , ansatzAI
  , ansatzAB
  , ansatzABI
  , ansatzApBq
  ) where

import Math.Tensor
import Math.Tensor.Safe.TH
import Math.Tensor.Basic
import Math.Tensor.LinearAlgebra

import qualified Data.IntMap.Strict as IM
import Data.Ratio
import Control.Monad.Except

sol :: Solution
sol = IM.fromList $ fmap (fmap (\as' -> Affine 0 $ Lin (IM.fromList as'))) as
  where
    as = [

           (1, [(1, 1%2), (2, 1), (3, 1%3)]),
           (2, [(1, (-3)), (2, (-12)), (3, (-4))]),
           (3, [(1, 1), (2, 6), (3, 2)]),
           (4, [(1, 1)]),
           (5, [(2, 1)]),
           (6, [(3, 1)]),
           (7, [(4, 3%2), (5, (-2)), (6, 12), (7, 8), (8, 4), (15, (-1%32)), (16, 5%8)]),
           (8, [(4, 1%4), (6, 1), (7, 2%3), (8, 1%3), (15, (-7%384)), (16, 1%16)]),
           (9, [(4, (-9%4)), (5, 3), (6, (-18)), (7, (-12)), (8, (-6)), (15, 1%32), (16, (-3%4))]),
           (10, [(4, 3), (5, (-4)), (6, 24), (7, 16), (8, 8), (15, (-1%8)), (16, 1)]),
           (11, [(4, (-3%4)), (5, (-1)), (6, (-6)), (7, (-4)), (8, (-2)), (15, 7%64)]),
           (12, [(4, 3%4), (5, (-1)), (6, 6), (7, 4), (8, 2), (15, (-1%16)), (16, 1%4)]),
           (13, [(4, (-1)), (5, 4), (6, (-24)), (7, (-16)), (8, (-8)), (16, (-1))]),
           (14, [(4, 1)]),
           (15, [(5, 1)]),
           (16, [(7, (-2)), (16, (-1%16))]),
           (17, [(6, 1)]),
           (18, [(7, (-6))]),
           (19, [(7, (-2))]),
           (20, [(7, 1)]),
           (21, [(8, 1)]),
           (22, [(9, (-1%12)), (10, 1%2), (11, 1), (12, 1%3), (13, 1%2), (14, 2), (16, 1%12)]),
           (23, [(9, 1%3), (11, (-2)), (13, (-2%3)), (16, (-1%12))]),
           (24, [(9, 1%2), (10, (-3)), (12, (-4)), (13, (-2)), (14, (-24)), (15, 1%16)]),
           (25, [(9, (-1)), (15, (-1%16))]),
           (26, [(9, 1)]),
           (27, [(15, (-1%32)), (16, (-1%8))]),
           (28, [(9, (-1%4)), (10, 1), (12, 2), (13, 1), (14, 12), (16, 1%8)]),
           (29, [(9, 1)]),
           (30, [(10, 1)]),
           (31, [(11, (-1%2)), (13, (-1%12)), (14, 1), (16, (-1%48))]),
           (32, [(11, 1)]),
           (33, [(12, 1)]),
           (34, [(13, 1), (16, 1%8)]),
           (35, [(16, (-1%4))]),
           (36, [(13, 1)]),
           (37, [(14, 1)]),
           (38, [(15, (-1%2)), (16, (-2))]),
           (39, [(15, 1)]),
           (40, [(16, 1)])

         ]

ansatzAI :: (Num v, Eq v, MonadError String m) =>
            m (T (Poly v))
ansatzAI = do
    t1 <- prod4 (k 38) (someEta "ST" 4 "a" "c") (someEta "ST" 4 "b" "d") (someEta "ST" 4 "e" "f")
    t2 <- (t1 .+) =<< prod4 (k 39) (someEta "ST" 4 "a" "c") (someEta "ST" 4 "b" "e") (someEta "ST" 4 "d" "f")
    t3 <- (t2 .+) =<< prod3 (k 40) (someEpsilon "ST" 4 ["a","b","c","d"]) (someEta "ST" 4 "e" "f")
    i1 <- (scalar 8 .*) =<< someInjAreaCon "ST" "a" "b" "c" "d" "A"
    i2 <- (scalar 2 .*) =<< someInjSym2Cov "ST" 4 "p" "q" "I"
    e1 <- someEtaInv "ST" 4 "e" "p"
    e2 <- someEtaInv "ST" 4 "f" "q"
    fmap contractT $ (i1 .*) =<< ((i2 .*) =<< ((e1 .*) =<< ((e2 .* t3))))
  where
    k i = scalar (singletonPoly 0 i 1)
    prod4 t mt1 mt2 mt3 = do
      _t1 <- mt1
      _t2 <- mt2
      _t3 <- mt3
      (t .*) =<< ((_t1 .*) =<< (_t2 .* _t3))
    prod3 t mt1 mt2 = do
      _t1 <- mt1
      _t2 <- mt2
      (t .*) =<< (_t1 .* _t2)

ansatzAB :: (Num v, Eq v, MonadError String m) =>
            m (T (Poly v))
ansatzAB = do
    t1 <- prod5 (k 1) (someEta "ST" 4 "a" "c") (someEta "ST" 4 "b" "d") (someEta "ST" 4 "e" "g") (someEta "ST" 4 "f" "h")
    t2 <- (t1 .+) =<< prod5 (k 2) (someEta "ST" 4 "a" "c") (someEta "ST" 4 "b" "e") (someEta "ST" 4 "d" "g") (someEta "ST" 4 "f" "h")
    t3 <- (t2 .+) =<< prod5 (k 3) (someEta "ST" 4 "a" "e") (someEta "ST" 4 "b" "f") (someEta "ST" 4 "c" "g") (someEta "ST" 4 "d" "h")
    t4 <- (t3 .+) =<< prod5 (k 4) (someEta "ST" 4 "a" "e") (someEta "ST" 4 "b" "g") (someEta "ST" 4 "c" "f") (someEta "ST" 4 "d" "h")
    t5 <- (t4 .+) =<< prod4 (k 5) (someEpsilon "ST" 4 ["a","b","c","d"]) (someEta "ST" 4 "e" "g") (someEta "ST" 4 "f" "h")
    t6 <- (t5 .+) =<< prod4 (k 6) (someEpsilon "ST" 4 ["a","b","e","f"]) (someEta "ST" 4 "c" "g") (someEta "ST" 4 "d" "h")
    i1 <- (scalar 8 .*) =<< someInjAreaCon "ST" "a" "b" "c" "d" "A"
    i2 <- (scalar 8 .*) =<< someInjAreaCon "ST" "e" "f" "g" "h" "B"
    res <- fmap contractT $ (i1 .*) =<< (i2 .* t6)
    (res .+) =<< transposeT (VSpace "STArea" 21) (ICov "A") (ICov "B") res

  where
    k i = scalar (singletonPoly 0 i 1)
    prod5 t mt1 mt2 mt3 mt4 = do
      _t1 <- mt1
      _t2 <- mt2
      _t3 <- mt3
      _t4 <- mt4
      (t .*) =<< ((_t1 .*) =<< ((_t2 .*) =<< (_t3 .* _t4)))
    prod4 t mt1 mt2 mt3 = do
      _t1 <- mt1
      _t2 <- mt2
      _t3 <- mt3
      (t .*) =<< ((_t1 .*) =<< (_t2 .* _t3))

ansatzABI :: (Num v, Eq v, MonadError String m) =>
              m (T (Poly v))
ansatzABI = do
    t1 <- prod6 (k 22) (someEta "ST" 4 "a" "c") (someEta "ST" 4 "b" "d") (someEta "ST" 4 "e" "g") (someEta "ST" 4 "f" "h") (someEta "ST" 4 "i" "j")
    t2 <- (t1 .+) =<< prod6 (k 23) (someEta "ST" 4 "a" "c") (someEta "ST" 4 "b" "d") (someEta "ST" 4 "e" "g") (someEta "ST" 4 "f" "i") (someEta "ST" 4 "h" "j")
    t3 <- (t2 .+) =<< prod6 (k 24) (someEta "ST" 4 "a" "c") (someEta "ST" 4 "b" "e") (someEta "ST" 4 "d" "g") (someEta "ST" 4 "f" "h") (someEta "ST" 4 "i" "j")
    t4 <- (t3 .+) =<< prod6 (k 25) (someEta "ST" 4 "a" "c") (someEta "ST" 4 "b" "e") (someEta "ST" 4 "d" "g") (someEta "ST" 4 "f" "i") (someEta "ST" 4 "h" "j")
    t5 <- (t4 .+) =<< prod6 (k 26) (someEta "ST" 4 "a" "c") (someEta "ST" 4 "b" "e") (someEta "ST" 4 "d" "i") (someEta "ST" 4 "f" "g") (someEta "ST" 4 "h" "j")
    t6 <- (t5 .+) =<< prod6 (k 27) (someEta "ST" 4 "a" "c") (someEta "ST" 4 "b" "i") (someEta "ST" 4 "d" "j") (someEta "ST" 4 "e" "g") (someEta "ST" 4 "f" "h")
    t7 <- (t6 .+) =<< prod6 (k 28) (someEta "ST" 4 "a" "e") (someEta "ST" 4 "b" "f") (someEta "ST" 4 "c" "g") (someEta "ST" 4 "d" "h") (someEta "ST" 4 "i" "j")
    t8 <- (t7 .+) =<< prod6 (k 29) (someEta "ST" 4 "a" "e") (someEta "ST" 4 "b" "f") (someEta "ST" 4 "c" "g") (someEta "ST" 4 "d" "i") (someEta "ST" 4 "h" "j")
    t9 <- (t8 .+) =<< prod6 (k 30) (someEta "ST" 4 "a" "e") (someEta "ST" 4 "b" "g") (someEta "ST" 4 "c" "f") (someEta "ST" 4 "d" "h") (someEta "ST" 4 "i" "j")
    t10 <- (t9 .+) =<< prod5 (k 31) (someEpsilon "ST" 4 ["a","b","c","d"]) (someEta "ST" 4 "e" "g") (someEta "ST" 4 "f" "h") (someEta "ST" 4 "i" "j")
    t11 <- (t10 .+) =<< prod5 (k 32) (someEpsilon "ST" 4 ["a","b","c","d"]) (someEta "ST" 4 "e" "g") (someEta "ST" 4 "f" "i") (someEta "ST" 4 "h" "j")
    t12 <- (t11 .+) =<< prod5 (k 33) (someEpsilon "ST" 4 ["a","b","e","f"]) (someEta "ST" 4 "c" "g") (someEta "ST" 4 "d" "h") (someEta "ST" 4 "i" "j")
    t13 <- (t12 .+) =<< prod5 (k 34) (someEpsilon "ST" 4 ["a","b","e","f"]) (someEta "ST" 4 "c" "g") (someEta "ST" 4 "d" "i") (someEta "ST" 4 "h" "j")
    t14 <- (t13 .+) =<< prod5 (k 35) (someEpsilon "ST" 4 ["a","b","e","i"]) (someEta "ST" 4 "c" "f") (someEta "ST" 4 "d" "g") (someEta "ST" 4 "h" "j")
    t15 <- (t14 .+) =<< prod5 (k 36) (someEpsilon "ST" 4 ["a","b","e","i"]) (someEta "ST" 4 "c" "g") (someEta "ST" 4 "d" "h") (someEta "ST" 4 "f" "j")
    t16 <- (t15 .+) =<< prod5 (k 37) (someEpsilon "ST" 4 ["e","f","g","h"]) (someEta "ST" 4 "a" "c") (someEta "ST" 4 "b" "d") (someEta "ST" 4 "i" "j")
    i1 <- (scalar 8 .*) =<< someInjAreaCon "ST" "a" "b" "c" "d" "A"
    i2 <- (scalar 8 .*) =<< someInjAreaCon "ST" "e" "f" "g" "h" "B"
    i3 <- (scalar 2 .*) =<< someInjSym2Cov "ST" 4 "p" "q" "I"
    e1 <- someEtaInv "ST" 4 "i" "p"
    e2 <- someEtaInv "ST" 4 "j" "q"
    fmap contractT $ (i1 .*) =<< ((i2 .*) =<< ((i3 .*) =<< ((e1 .*) =<< (e2 .* t16))))
  where
    k i = scalar (singletonPoly 0 i 1)
    prod6 t mt1 mt2 mt3 mt4 mt5 = do
      _t1 <- mt1
      _t2 <- mt2
      _t3 <- mt3
      _t4 <- mt4
      _t5 <- mt5
      (t .*) =<< ((_t1 .*) =<< ((_t2 .*) =<< ((_t3 .*) =<< (_t4 .* _t5))))
    prod5 t mt1 mt2 mt3 mt4 = do
      _t1 <- mt1
      _t2 <- mt2
      _t3 <- mt3
      _t4 <- mt4
      (t .*) =<< ((_t1 .*) =<< ((_t2 .*) =<< (_t3 .* _t4)))

ansatzApBq :: (Num v, Eq v, MonadError String m) =>
              m (T (Poly v))
ansatzApBq = do
    t1 <- prod6 (k 7) (someEta "ST" 4 "a" "c") (someEta "ST" 4 "b" "d") (someEta "ST" 4 "e" "f") (someEta "ST" 4 "g" "h") (someEta "ST" 4 "i" "j")
    t2 <- (t1 .+) =<< prod6 (k 8) (someEta "ST" 4 "a" "c") (someEta "ST" 4 "b" "d") (someEta "ST" 4 "e" "j") (someEta "ST" 4 "f" "h") (someEta "ST" 4 "g" "i")
    t3 <- (t2 .+) =<< prod6 (k 9) (someEta "ST" 4 "a" "c") (someEta "ST" 4 "b" "e") (someEta "ST" 4 "d" "f") (someEta "ST" 4 "g" "h") (someEta "ST" 4 "i" "j")
    t4 <- (t3 .+) =<< prod6 (k 10) (someEta "ST" 4 "a" "c") (someEta "ST" 4 "b" "f") (someEta "ST" 4 "d" "h") (someEta "ST" 4 "e" "g") (someEta "ST" 4 "i" "j")
    t5 <- (t4 .+) =<< prod6 (k 11) (someEta "ST" 4 "a" "c") (someEta "ST" 4 "b" "f") (someEta "ST" 4 "d" "h") (someEta "ST" 4 "e" "j") (someEta "ST" 4 "g" "i")
    t6 <- (t5 .+) =<< prod6 (k 12) (someEta "ST" 4 "a" "c") (someEta "ST" 4 "b" "f") (someEta "ST" 4 "d" "j") (someEta "ST" 4 "e" "h") (someEta "ST" 4 "g" "i")
    t7 <- (t6 .+) =<< prod6 (k 13) (someEta "ST" 4 "a" "e") (someEta "ST" 4 "b" "f") (someEta "ST" 4 "c" "g") (someEta "ST" 4 "d" "h") (someEta "ST" 4 "i" "j")
    t8 <- (t7 .+) =<< prod6 (k 14) (someEta "ST" 4 "a" "e") (someEta "ST" 4 "b" "f") (someEta "ST" 4 "c" "h") (someEta "ST" 4 "d" "i") (someEta "ST" 4 "g" "j")
    t9 <- (t8 .+) =<< prod6 (k 15) (someEta "ST" 4 "a" "f") (someEta "ST" 4 "b" "g") (someEta "ST" 4 "c" "h") (someEta "ST" 4 "d" "i") (someEta "ST" 4 "e" "j")
    t10 <- (t9 .+) =<< prod5 (k 16) (someEpsilon "ST" 4 ["a","b","c","d"]) (someEta "ST" 4 "e" "f") (someEta "ST" 4 "g" "h") (someEta "ST" 4 "i" "j")
    t11 <- (t10 .+) =<< prod5 (k 17) (someEpsilon "ST" 4 ["a","b","c","d"]) (someEta "ST" 4 "e" "j") (someEta "ST" 4 "f" "h") (someEta "ST" 4 "g" "i")
    t12 <- (t11 .+) =<< prod5 (k 18) (someEpsilon "ST" 4 ["a","b","e","f"]) (someEta "ST" 4 "c" "g") (someEta "ST" 4 "d" "h") (someEta "ST" 4 "i" "j")
    t13 <- (t12 .+) =<< prod5 (k 19) (someEpsilon "ST" 4 ["a","b","e","f"]) (someEta "ST" 4 "c" "h") (someEta "ST" 4 "d" "j") (someEta "ST" 4 "g" "i")
    t14 <- (t13 .+) =<< prod5 (k 20) (someEpsilon "ST" 4 ["a","b","f","g"]) (someEta "ST" 4 "c" "e") (someEta "ST" 4 "d" "h") (someEta "ST" 4 "i" "j")
    t15 <- (t14 .+) =<< prod5 (k 21) (someEpsilon "ST" 4 ["a","b","f","g"]) (someEta "ST" 4 "c" "h") (someEta "ST" 4 "d" "i") (someEta "ST" 4 "e" "j")
    i1 <- (scalar 8 .*) =<< someInjAreaCon "ST" "a" "b" "c" "d" "A"
    i2 <- (scalar 8 .*) =<< someInjAreaCon "ST" "f" "g" "h" "i" "B"
    e1 <- someEtaInv "ST" 4 "e" "p"
    e2 <- someEtaInv "ST" 4 "j" "q"
    res <- fmap contractT $ (i1 .*) =<< ((i2 .*) =<< ((e1 .*) =<< (e2 .* t15)))
    (res .+) =<< (transposeT (VSpace "STArea" 21) (ICov "A") (ICov "B") =<< transposeT (VSpace "ST" 4) (ICon "p") (ICon "q") res)
  where
    k i = scalar (singletonPoly 0 i 1)
    prod6 t mt1 mt2 mt3 mt4 mt5 = do
      _t1 <- mt1
      _t2 <- mt2
      _t3 <- mt3
      _t4 <- mt4
      _t5 <- mt5
      (t .*) =<< ((_t1 .*) =<< ((_t2 .*) =<< ((_t3 .*) =<< (_t4 .* _t5))))
    prod5 t mt1 mt2 mt3 mt4 = do
      _t1 <- mt1
      _t2 <- mt2
      _t3 <- mt3
      _t4 <- mt4
      (t .*) =<< ((_t1 .*) =<< ((_t2 .*) =<< (_t3 .* _t4)))
