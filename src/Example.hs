{-# LANGUAGE OverloadedStrings #-}

module Example where

import Delta
import Sym2
import Tensor
import Control.Monad.Except

calc :: (Num v, Eq v) => ExceptT String IO (T v)
calc = do
  e_ab <- someEtaInv "Spacetime" 4 "a" "b"
  let d_cp = someDelta "Spacetime" 4 "c" "p"
  e_ac <- someEtaInv "Spacetime" 4 "a" "c"
  let d_bp = someDelta "Spacetime" 4 "b" "p"
  prod1 <- e_ab .* d_cp
  prod2 <- e_ac .* d_bp
  prod1 .+ prod2
