module Data.Number.Flint.NMod.Poly.Struct (
    NModPoly (..)
  , CNModPoly (..)
  , NModPolyCRT (..)
  , CNModPolyCRT (..)
) where

import Foreign.ForeignPtr
import Data.Number.Flint.Internal

data NModPoly = NModPoly {-# UNPACK #-} !(ForeignPtr CNModPoly)
type CNModPoly = CFlint NModPoly

data NModPolyCRT = NModPolyCRT {-# UNPACK #-} !(ForeignPtr CNModPolyCRT)
type CNModPolyCRT = CFlint NModPolyCRT
