-----------------------------------------------------------------------------
{-|
Module      : Math.Tensor.LinearAlgebra
Description : Linear algebra for tensor equations.
Copyright   : (c) Nils Alex, 2020
License     : MIT
Maintainer  : nils.alex@fau.de
Stability   : experimental

Linear algebra for tensor equations.
-}
-----------------------------------------------------------------------------
module Math.Tensor.LinearAlgebra
  ( -- * Linear combinations and polynomials
    Lin(..)
  , Poly(..)
  , singletonPoly
  , polyMap
  , getVars
  , shiftVars
  , normalize
  ) where

import Math.Tensor.LinearAlgebra.Scalar
import Math.Tensor.LinearAlgebra.Matrix
