{-# LANGUAGE Safe #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-----------------------------------------------------------------------------
{-|
Module      : Math.Tensor.LinearAlgebra.Scalar
Description : Scalar types for usage as Tensor values.
Copyright   : (c) Nils Alex, 2020
License     : MIT
Maintainer  : nils.alex@fau.de

Scalar types for usage as Tensor values.
-}
-----------------------------------------------------------------------------
module Math.Tensor.LinearAlgebra.Scalar
  ( Lin(..)
  , Poly(..)
  , singletonPoly
  , polyMap
  , getVars
  , shiftVars
  , normalize
  ) where

import qualified Data.IntMap.Strict as IM
  ( IntMap
  , singleton
  , null
  , keys
  , map
  , filter
  , mapKeysMonotonic
  , unionWith
  , findMin
  )

-- |Linear combination represented as mapping from
-- variable number to prefactor.
newtype Lin a = Lin (IM.IntMap a) deriving (Show, Ord, Eq)

-- |Polynomial: Can be constant, affine, or something of higher
-- rank which is not yet implemented.
data Poly a = Const !a -- ^ constant value
            | Affine !a !(Lin a) -- ^ constant value plus linear term
            |  NotSupported -- ^ higher rank
  deriving (Show, Ord, Eq)

-- |Produces an affine value \(c + a\cdot x_i\)
singletonPoly :: a       -- ^ constant
              -> Int     -- ^ variable number
              -> a       -- ^ prefactor
              -> Poly a
singletonPoly a i v = Affine a $ Lin $ IM.singleton i v

-- |Maps over 'Poly'
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

-- |Returns list of variable numbers present in the polynomial.
getVars :: Poly a -> [Int]
getVars (Const _) = []
getVars NotSupported = []
getVars (Affine _ (Lin lm)) = IM.keys lm

-- |Shifts variable numbers in the polynomial by a constant value.
shiftVars :: Int -> Poly a -> Poly a
shiftVars _ (Const a) = Const a
shiftVars _ NotSupported = NotSupported
shiftVars s (Affine a (Lin lin)) =
  Affine a $ Lin $ IM.mapKeysMonotonic (+s) lin

-- |Normalizes a polynomial:
-- \[
--    \mathrm{normalize}(c) = 1 \\
--    \mathrm{normalize}(c + a_1\cdot x_1 + a_2\cdot x_2 + \dots + a_n\cdot x_n) = \frac{c}{a_1} + 1\cdot x_1 + \frac{a_2}{a_1}\cdot x_2 + \dots + \frac{a_n}{a_1}\cdot x_n
-- \]
normalize :: Fractional a => Poly a -> Poly a
normalize (Const _) = Const 1
normalize NotSupported = NotSupported
normalize (Affine a (Lin lin)) = Affine (a/v) $ Lin $ IM.map (/v) lin
  where
    (_,v) = IM.findMin lin

