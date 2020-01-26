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

newtype Lin a = Lin { linMap :: IM.IntMap a } deriving (Show, Ord, Eq)

instance Functor Lin where
  fmap f = Lin . fmap f . linMap

data Poly a = Const !a |
              Affine !a !(Lin a) |
              NotSupported
  deriving (Show, Ord, Eq)

polyFromAnsVarR :: Num a => T.AnsVarR -> Poly a
polyFromAnsVarR (T.AnsVar im)
  | IM.null im = Const 0
  | otherwise   = Affine 0 (Lin $ fmap (\(T.SField x) -> if   denominator x == 1
                                                         then fromIntegral (numerator x)
                                                         else error "Cannot convert from rational.") im)

instance Functor Poly where
  fmap f (Const a)      = Const (f a)
  fmap f (Affine a lin) = Affine (f a) $ fmap f lin
  fmap f _              = NotSupported

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

  negate = fmap negate

  abs (Const a) = Const $ abs a
  abs _         = NotSupported

  signum (Const a) = Const $ signum a
  signum _      = NotSupported

  fromInteger   = Const . fromInteger

  Const a * Const b = Const $ a * b
  Const a * Affine b lin = Affine (a*b) $ fmap (a*) lin
  Affine a lin * Const b = Affine (a*b) $ fmap (*b) lin
  _       * _            = NotSupported
