{-|
module      :  Data.Number.Flint.Fq.NMod.Types.FFI
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de
-}
module Data.Number.Flint.Fq.NMod.Types.FFI where

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.C.Types
import Foreign.C.String

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.NMod
import Data.Number.Flint.NMod.Types

-- fq_nmod_t -------------------------------------------------------------------

data FqNMod = FqNMod {-# UNPACK #-} !(ForeignPtr CFqNMod)
type CFqNMod = CFlint FqNMod

-- fq_nmod_ctx_t ---------------------------------------------------------------

data FqNModCtx = FqNModCtx {-# UNPACK #-} !(ForeignPtr CFqNModCtx)
data CFqNModCtx = CFqNModCtx (Ptr CFmpz) (Ptr CNMod) CInt CInt (Ptr CMpLimb) (Ptr CLong) (Ptr CLong) (Ptr CNModPoly) (Ptr CNModPoly) CString 

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
data CFqNModMat = CFqNModMat (Ptr CFqNMod) CLong CLong (Ptr (Ptr CFqNMod))
