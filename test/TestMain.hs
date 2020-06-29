{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}

module Main where

import Safe
import Tensor
import Basic
import TH

import Control.Monad
import Control.Monad.Except
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
    l = [(0 `VCons` (0 `VCons` VNil),1), (1 `VCons` (1 `VCons` VNil),1), (2 `VCons` (2 `VCons` VNil),1), (3 `VCons` (3 `VCons` VNil),1)]

test2 :: Either String ()
test2
    | l == toList t = Right ()
    | otherwise = Left $ show t ++ "\ndoes not yield assocs\n" ++ show l
  where
    t = etaInv :: Tensor '[ '(V4, Up2 "a" "b") ] Rational
    l = [(0 `VCons` (0 `VCons` VNil),1), (1 `VCons` (1 `VCons` VNil),-1), (2 `VCons` (2 `VCons` VNil),-1), (3 `VCons` (3 `VCons` VNil),-1)]

test3 :: Either String ()
test3 = runExcept $
        do
         let t1  = T $ delta_pa &* delta_qb
         let t2' = T $ delta_pb &* delta_qa
         t2 <- transposeT (VSpace "Spacetime" 4) (ICon "p") (ICon "q") t2'
         diff <- t1 .- t2
         case diff of
           T ZeroTensor -> return ()
           t            -> throwError $ show t ++ "\nis not ZeroTensor"

test4 :: Either String ()
test4 =
    do
     let t1 = T _t1
     let a1 = T _a1
     let a2 = T _a2
     symmetrizer <- transposeT (VSpace "Spacetime" 4) (ICon "p") (ICon "q") t1
     p <- symmetrizer .* a1
     s <- contractT p .+ a2
     case s of
       T ZeroTensor -> return ()
       t            -> Left $ show t ++ "\n is not ZeroTensor"
  where
    _t1 = delta_pa &* delta_qb
    _a1 = asym :: Tensor '[ '(V4, Up2 "a" "b") ] Rational
    _a2 = asym :: Tensor '[ '(V4, Up2 "p" "q") ] Rational

test5 :: Either String ()
test5 =
    do
      eta_cd_eta_ab <- eta_cd .* eta_ab
      eta_ab_eta_cd <- eta_ab .* eta_cd
      eta_ad_eta_bc <- eta_ad .* eta_bc

      t1 <- eta_cd_eta_ab .+ eta_ab_eta_cd
      t2 <- transposeT (VSpace "Spacetime" 4) (ICon "b") (ICon "d") t1
      t3 <- eta_ad_eta_bc .+ eta_ad_eta_bc

      r <- t3 .- t2
      case r of
        T ZeroTensor -> return ()
        t            -> Left $ show t ++ "\nis not ZeroTensor"
  where
    eta_ab = T (etaInv :: Tensor '[ '(V4, Up2 "a" "b") ] Rational)
    eta_cd = T (etaInv :: Tensor '[ '(V4, Up2 "c" "d") ] Rational)
    eta_ad = T (etaInv :: Tensor '[ '(V4, Up2 "a" "d") ] Rational)
    eta_bc = T (etaInv :: Tensor '[ '(V4, Up2 "b" "c") ] Rational)
