{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Example
import Tensor
import Scalar
import DiffeoSymmetry
import Equations
import Ansaetze

import Data.List (nub,sort)
import Control.Parallel.Strategies
import Control.Monad.Except

main' :: IO ()
main' = do
  mapM_ print (tests `using` parList rseq)
  where
    tests = [
             --ans4Test,
             --ans6Test,
             --ans8Test,
             --ans10_1Test,
             --ans10_2Test,
             --ans12Test,
             --ans14_1Test,
             ans14_2Test
            ]

main :: IO (Either String ())
main = runExceptT $
 do
  as :: [T (Poly Rational)] <- sndOrderAnsaetze
  eqns <- sndOrderDiffeoEqns as
  let as' = solveSystem eqns as
  eqns' <- sndOrderDiffeoEqns as'
  let as'' = redefineIndets as'
  lift $ print $ nub $ sort $ concat $ fmap (getVars . snd) $ concat $ fmap toListT as''
