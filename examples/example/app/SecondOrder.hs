{-# LANGUAGE ScopedTypeVariables #-}

module SecondOrder where

import Math.Tensor
import Math.Tensor.LinearAlgebra

import Math.Tensor.SparseTensor.Ansaetze

import DiffeoSymmetry
import EOM

import Control.Monad.Except

thrd :: (a,b,c) -> c
thrd (_,_,c) = c

secondOrder :: IO (Either String ())
secondOrder =
  runExceptT $
      do
        as@[a4,a0,a6,a8,a10_1,a10_2] :: [T (Poly Rational)] <- fmap (fmap thrd) sndOrderAnsaetze

        lift $ putStrLn $ "vars in ansaetze        : " ++ show (systemRank as)

        eqns <- sndOrderDiffeoEqns as

        lift $ putStrLn $ "rank of eqns            : " ++ show (systemRank eqns)

        let as'@[a4',a0',a6',a8',a10_1',a10_2'] = solveSystem eqns as

        lift $ putStrLn $ "vars in solved ansaetze : " ++ show (systemRank as')
        lift $ putStrLn ""

        eqns' <- sndOrderDiffeoEqns as'

        lift $ putStrLn $ "eqns on solution space  :"
        lift $ mapM_ print eqns'

        lift $ putStrLn ""

        lift $ putStrLn $ "independent vars in massive eom : " ++
                          show (systemRank [a8'])

        k <- kinetic a10_1' a10_2'
        lift $ putStrLn $ "independent vars in kinetic eom : " ++
                          show (systemRank [k])

        lift $ putStrLn ""

        n1 <- noether1 a4' a8'
        n2 <- noether2 a10_1' a10_2'
        lift $ putStrLn $ "noether identity 1 : " ++
                          show n1
        lift $ putStrLn $ "noether identity 2 : " ++
                          show n2
