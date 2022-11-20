module Data.Number.Flint.NMod.Poly.Factor.Struct (
    NModPolyFactor (..)
  , CNModPolyFactor (..)
) where

import Foreign.ForeignPtr
import Data.Number.Flint.Flint
import Data.Number.Flint.NMod.Poly

data NModPolyFactor = NModPolyFactor {-# UNPACK #-} !(ForeignPtr CNModPoly)
type CNModPolyFactor = CFlint NModPolyFactor

