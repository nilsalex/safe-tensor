{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}

module Scalar where

import qualified Data.IntMap.Strict as IM
import Control.Applicative (liftA2)
import Data.Ratio (numerator,denominator)

import qualified Math.Tensor as T (AnsVar(..), AnsVarR, SField(..))

newtype SField a = SField { sVal :: a } deriving (Show, Read, Eq, Ord)
type SFieldR = SField Rational

instance Functor SField where
  fmap f = SField . f . sVal

instance Applicative SField where
  pure = SField
  (<*>) (SField f) = fmap f

instance Num a => Num (SField a) where
  (+) = liftA2 (+)
  (-) = liftA2 (-)
  (*) = liftA2 (*)
  negate = fmap negate
  abs = fmap abs
  signum = fmap signum
  fromInteger = pure . fromInteger

instance Fractional a => Fractional (SField a) where
  (/) = liftA2 (/)
  recip = fmap recip
  fromRational = pure . fromRational

class Algebra a b p | p -> a b where
  prod :: a -> b -> p

instance Num a => Algebra (SField a) (SField a) (SField a) where
  prod = (*)

newtype Lin a = Lin (IM.IntMap a) deriving (Show, Ord, Eq)

data Poly a = Const !a |
              Affine !a !(Lin a) |
              NotSupported
  deriving (Show, Ord, Eq)

singletonPoly :: a -> Int -> a -> Poly a
singletonPoly a i v = Affine a $ Lin $ IM.singleton i v

polyFromAnsVarR :: Num a => T.AnsVarR -> Poly a
polyFromAnsVarR (T.AnsVar im)
  | IM.null im = Const 0
  | otherwise   = Affine 0 (Lin $ IM.map (\(T.SField x) -> if   denominator x == 1
                                                         then fromIntegral (numerator x)
                                                         else error "Cannot convert from rational.") im)

polyMap :: (a -> b) -> Poly a -> Poly b
polyMap f (Const a) = Const (f a)
polyMap f (Affine a (Lin lin)) = Affine (f a) $ Lin $ IM.map f lin
polyMap _ _ = NotSupported

instance (Num a, Eq a) => Num (Poly a) where
  Const a + Const b = Const $ a + b
  Const a + Affine b lin = Affine (a+b) lin
  Affine a lin + Const b = Affine (a+b) lin
  Affine a (Lin m1) + Affine b (Lin m2)
      | IM.null m' = Const $ a + b
      | otherwise  = Affine (a+b) (Lin m')
    where
      m' = IM.filter (/=0) $ IM.unionWith (+) m1 m2
  NotSupported + _ = NotSupported 
  _ + NotSupported = NotSupported

  negate = polyMap negate

  abs (Const a) = Const $ abs a
  abs _         = NotSupported

  signum (Const a) = Const $ signum a
  signum _      = NotSupported

  fromInteger   = Const . fromInteger

  Const a * Const b = Const $ a * b
  Const a * Affine b (Lin lin)
    | a == 0    = Const 0
    | otherwise = Affine (a*b) $ Lin $ IM.map (a*) lin
  Affine a (Lin lin) * Const b
    | b == 0    = Const 0
    | otherwise = Affine (a*b) $ Lin $ IM.map (*b) lin
  _       * _            = NotSupported

getVars :: Poly a -> [Int]
getVars (Const _) = []
getVars NotSupported = []
getVars (Affine _ (Lin lm)) = IM.keys lm

shiftVars :: Int -> Poly a -> Poly a
shiftVars _ (Const a) = Const a
shiftVars _ NotSupported = NotSupported
shiftVars s (Affine a (Lin lin)) =
  Affine a $ Lin $ IM.mapKeysMonotonic (+s) lin

normalize :: Poly Rational -> Poly Rational
normalize (Const _) = Const 1
normalize NotSupported = NotSupported
normalize (Affine a (Lin lin)) = Affine (a/v) $ Lin $ IM.map (/v) lin
  where
    (_,v) = IM.findMin lin

