{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}

module DiffeoSymmetry where

import Tensor
import Area
import Sym2
import Delta

import Control.Monad.Except

someInterAreaJet1 :: (Num v, MonadError String m) =>
                     Label ->
                     Label -> Label ->
                     Label -> Label ->
                     Label -> Label ->
                     m (T v)
someInterAreaJet1 id m n a b p q = do
    i1 <- c .* someDelta id 4 q p
    i2 <- (someDeltaArea id a b .* ) =<< (someDelta id 4 m p .* someDelta id 4 q n)
    res :: T Int <- i1 .+ i2
    return $ fmap fromIntegral res
  where
    c = someInterAreaCon id m n a b

someInterAreaJet2 :: Num v =>
                     Label ->
                     Label -> Label ->
                     Label -> Label ->
                     Label -> Label ->
                     T v
someInterAreaJet2 id m n a b i j = int
  where
    c = someInterAreaCon id m n a b
    k = someInterSym2Cov id 4 m n i j
    Right int = runExcept $
      do
        i1 <- c .* someDeltaSym2 id 4 j i
        i2 <- k .* someDeltaArea id a b
        res :: T Int <- i1 .+ i2
        return $ fmap fromIntegral res
