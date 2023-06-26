module Data.Number.Flint.Fq.Zech.Types.FFI where

import Foreign.ForeignPtr

import Data.Number.Flint.Flint

-- fq_poly_t -------------------------------------------------------------------

data FqZechPoly = FqZechPoly {-# UNPACK #-} !(ForeignPtr CFqZechPoly)
type CFqZechPoly = CFlint FqZechPoly

-- fq_mat_t --------------------------------------------------------------------

data FqZechMat = FqZechMat {-# UNPACK #-} !(ForeignPtr CFqZechMat)
type CFqZechMat = CFlint FqZechMat

-- fq_zech_poly_factor_t -------------------------------------------------------

data FqZechPolyFactor = FqZechPolyFactor {-# UNPACK #-} !(ForeignPtr CFqZechPolyFactor)
type CFqZechPolyFactor = CFlint FqZechPolyFactor
