{-# LANGUAGE TypeApplications #-}

module Main where

import AnsaetzeTest

main :: IO ()
main = mapM_ print tests
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
