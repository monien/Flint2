module Data.Number.Flint.Fq.Types.FFI where

import Foreign.ForeignPtr

import Data.Number.Flint.Flint

-- fq_poly_t -------------------------------------------------------------------

data FqPoly = FqPoly {-# UNPACK #-} !(ForeignPtr CFqPoly)
type CFqPoly = CFlint FqPoly

-- fq_mat_t --------------------------------------------------------------------

data FqMat = FqMat {-# UNPACK #-} !(ForeignPtr CFqMat)
type CFqMat = CFlint FqMat
