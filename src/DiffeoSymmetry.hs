{-# LANGUAGE OverloadedStrings #-}

module DiffeoSymmetry where

import Tensor
import Area
import Sym2

import Control.Monad.Except

someInterAreaJet2 :: (Num v, MonadError String m) =>
                     Label ->
                     Label -> Label ->
                     Label -> Label ->
                     Label -> Label ->
                     m (T v)
someInterAreaJet2 id m n a b i j =
  do
    i1 <- c .* someDeltaSym2 id 4 j i
    i2 <- k .* someDeltaArea id a b
    res :: T Int <- i1 .+ i2
    return $ fmap fromIntegral res
  where
    c = someInterAreaCon id m n a b
    k = someInterSym2Cov id 4 m n i j
