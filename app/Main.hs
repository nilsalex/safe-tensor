module Main where

import Example
import Control.Parallel.Strategies

main :: IO ()
main = do
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
