module Data.Number.Flint.Fq.NMod.Types.FFI where

import Foreign.ForeignPtr

import Data.Number.Flint.Flint

data FqNModPoly = FqNModPoly {-# UNPACK #-} !(ForeignPtr CFqNModPoly)
type CFqNModPoly = CFlint FqNModPoly

data FqNModMat = FqNModMat {-# UNPACK #-} !(ForeignPtr CFqNModMat)
type CFqNModMat = CFlint FqNModMat
