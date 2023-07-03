module Data.Number.Flint.Fq.NMod.Types.FFI where

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.C.Types

import Data.Number.Flint.Flint

-- fq_nmod_poly_t --------------------------------------------------------------

data  FqNModPoly = FqNModPoly {-# UNPACK #-} !(ForeignPtr CFqNModPoly)
type CFqNModPoly = CFlint FqNModPoly

-- fq_nmod_poly_factor_t -------------------------------------------------------

data  FqNModPolyFactor = FqNModPolyFactor {-# UNPACK #-} !(ForeignPtr CFqNModPolyFactor)
data CFqNModPolyFactor = CFqNModPolyFactor (Ptr CFqNModPoly) (Ptr CLong) CLong CLong

-- fq_nmod_mpoly_t -------------------------------------------------------------

data  FqNModMPoly = FqNModMPoly {-# UNPACK #-} !(ForeignPtr CFqNModMPoly)
type CFqNModMPoly = CFlint FqNModMPoly

-- fq_nmod_mat_t ---------------------------------------------------------------

data  FqNModMat = FqNModMat {-# UNPACK #-} !(ForeignPtr CFqNModMat)
type CFqNModMat = CFlint FqNModMat
