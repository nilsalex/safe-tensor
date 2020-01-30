{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Example
import Tensor
import Scalar
import DiffeoSymmetry
import Equations
import Ansaetze
import EOM

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
main =
  runExceptT $
      do
        as@[a4,a0,a6,a8,a10_1,a10_2] :: [T (Poly Rational)] <- sndOrderAnsaetze

        lift $ putStrLn $ "vars in ansaetze        : " ++ show (systemRank as)

        eqns <- sndOrderDiffeoEqns as

        lift $ putStrLn $ "rank of eqns           : " ++ show (systemRank eqns)

        let as'@[a4',a0',a6',a8',a10_1',a10_2'] = solveSystem eqns as

        lift $ putStrLn $ "vars in solved ansaetze : " ++ show (systemRank as')
        lift $ putStrLn ""

        eqns' <- sndOrderDiffeoEqns as'

        lift $ putStrLn $ "eqns on solution space  :"
        lift $ mapM_ print $ eqns'

        lift $ putStrLn ""

        lift $ putStrLn $ "independent vars in massive eom : " ++
                          show (equationRank a8')

        k <- kinetic a10_1' a10_2'
        lift $ putStrLn $ "independent vars in kinetic eom : " ++
                          show (equationRank k)

        lift $ putStrLn ""

        n1 <- noether1 a4' a8'
        n2 <- noether2 a10_1' a10_2'
        lift $ putStrLn $ "noether identity 1 : " ++
                          show n1
        lift $ putStrLn $ "noether identity 2 : " ++
                          show n2
