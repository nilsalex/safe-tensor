{-# LANGUAGE TypeApplications #-}

module Main where

import AnsaetzeTest
import SecondOrder

main :: IO ()
main = do
        putStrLn "###### Test ansaetze ######"
        putStrLn "Get ansaetze up to third order from sparse-tensor and verify that the ansatz equations are solved."
        mapM_ print tests
        putStrLn ""
        putStrLn "###### Test diffeo equations, eom and noether ######"
        putStrLn "Using the ansaetze up to second order from sparse-tensor, solve the diffeo equations, count independent vars in the eom and verify the noether theorem."
        res <- secondOrder
        case res of
          Right _  -> return ()
          Left err -> putStrLn err
  where
    tests = [ ans4Test    @Int
            , ans6Test    @Int
            , ans8Test    @Int
            , ans10_1Test @Int
            , ans10_2Test @Int
            , ans12Test   @Int
            , ans14_1Test @Int
            , ans14_2Test @Int
            ]
