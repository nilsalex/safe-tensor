{-# LANGUAGE TypeApplications #-}

module Main where

import AnsaetzeTest
import SecondOrder

main :: IO ()
main = do
        -- mapM_ print tests
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
