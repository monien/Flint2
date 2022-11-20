module Data.Number.Flint.NMod.Mat.Struct (
    NModMat (..)
  , CNModMat (..)
) where

import Foreign.ForeignPtr
import Data.Number.Flint.Flint.Internal

data NModMat = NModMat {-# UNPACK #-} !(ForeignPtr CNModMat)
type CNModMat = CFlint NModMat
