{-# LANGUAGE OverloadedStrings #-}

module Example where

import Delta
import Sym2
import Tensor
import Control.Monad.Except

calc :: (Num v, Eq v) => Either String (T v)
calc = runExcept $ do
    e_ab <- someEtaInv "Spacetime" 4 "a" "b"
    e_ac <- someEtaInv "Spacetime" 4 "a" "c"
    prod1 <- e_ab .* d_cp
    prod2 <- e_ac .* d_bp
    prod1 .+ prod2
  where
    d_cp = someDelta "Spacetime" 4 "c" "p"
    d_bp = someDelta "Spacetime" 4 "b" "p"
