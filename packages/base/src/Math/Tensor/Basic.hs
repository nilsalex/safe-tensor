-----------------------------------------------------------------------------
{-|
Module      : Math.Tensor.Basic
Description : Definitions of basic tensors.
Copyright   : (c) Nils Alex, 2020
License     : MIT
Maintainer  : nils.alex@fau.de
Stability   : experimental

Definitions of basic tensors, re-exported for convenience.
-}
-----------------------------------------------------------------------------

module Math.Tensor.Basic
  ( -- * Kronecker delta
    module Math.Tensor.Basic.Delta
  , -- * Epsilon tensor densities
    module Math.Tensor.Basic.Epsilon
  , -- * Symmetric tensors
    module Math.Tensor.Basic.Sym2
  , -- * Area-symmetric tensors
    module Math.Tensor.Basic.Area
  ) where

import Math.Tensor.Basic.Delta
import Math.Tensor.Basic.Epsilon
import Math.Tensor.Basic.Sym2
import Math.Tensor.Basic.Area
