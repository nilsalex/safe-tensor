{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}

module Main where

import Tensor
import TH

import Control.Monad
import System.Exit

main :: IO ()
main = runTests [
                  test1
                , test2
                , test3
                , test4
                , test5
                ]

runTests :: [Either String ()] -> IO ()
runTests ts = putStrLn "" >> go 1 ts
  where
    go i [] = return ()
    go i (t:ts) = case t of
                    Right () -> putStrLn ("test " ++ show i ++ " passed") >> go (i+1) ts
                    Left e   -> putStrLn ("test " ++ show i ++ " failed") >> putStrLn e >> go (i+1) ts

delta_pa :: Tensor '[ '(V4, UpDown "p" "a") ] Rational
delta_pa = delta

delta_pb :: Tensor '[ '(V4, UpDown "p" "b") ] Rational
delta_pb = delta

delta_qa :: Tensor '[ '(V4, UpDown "q" "a") ] Rational
delta_qa = delta

delta_qb :: Tensor '[ '(V4, UpDown "q" "b") ] Rational
delta_qb = delta

test1 :: Either String ()
test1
    | l == toList t = Right ()
    | otherwise = Left $ show t ++ "\ndoes not yield assocs\n" ++ show l
  where
    t = delta_pa
    l = [([0,0],1), ([1,1],1), ([2,2],1), ([3,3],1)]

test2 :: Either String ()
test2
    | l == toList t = Right ()
    | otherwise = Left $ show t ++ "\ndoes not yield assocs\n" ++ show l
  where
    t = eta :: Tensor '[ '(V4, Up2 "a" "b") ] Rational
    l = [([0,0],1), ([1,1],-1), ([2,2],-1), ([3,3],-1)]

test3 :: Either String ()
test3 = case fmap (t1 &-) t2 of
          Right ZeroTensor -> Right ()
          Right t -> Left $ show t ++ "\nis not ZeroTensor"
          Left  e -> Left e
  where
    t1 = delta_pa &* delta_qb
    t2 = transpose (VSpace "Spacetime" 4) (ICon "p") (ICon "q") $ delta_pb &* delta_qa

test4 :: Either String ()
test4 =
    do
      symmetrizer <- transpose (VSpace "Spacetime" 4) (ICon "p") (ICon "q") t1
      case contract (symmetrizer &* a1) &+ a2 of
        ZeroTensor -> return ()
        t          -> Left $ show t ++ "\nis not ZeroTensor"
  where
    t1 = delta_pa &* delta_qb
    a1 = asym :: Tensor '[ '(V4, Up2 "a" "b") ] Rational
    a2 = asym :: Tensor '[ '(V4, Up2 "p" "q") ] Rational
 
test5 :: Either String ()
test5 = case fmap (t3 &-) t2 of
          Right ZeroTensor -> Right ()
          Right t -> Left $ show t ++ "\nis not ZeroTensor"
          Left  e -> Left e
  where
    eta_ab = eta :: Tensor '[ '(V4, Up2 "a" "b") ] Rational
    eta_cd = eta :: Tensor '[ '(V4, Up2 "c" "d") ] Rational
    eta_ad = eta :: Tensor '[ '(V4, Up2 "a" "d") ] Rational
    eta_bc = eta :: Tensor '[ '(V4, Up2 "b" "c") ] Rational

    t1 = (eta_cd &* eta_ab) &+ (eta_ab &* eta_cd)
    t2 = transpose (VSpace "Spacetime" 4) (ICon "b") (ICon "d") t1
    t3 = (eta_ad &* eta_bc) &+ (eta_ad &* eta_bc)
