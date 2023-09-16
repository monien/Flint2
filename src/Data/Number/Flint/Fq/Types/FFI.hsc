{-# OPTIONS_HADDOCK hide, prune, ignore-exports #-}
{-|
module      :  Data.Number.Flint.Fq.Types.FFI
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de
-}
module Data.Number.Flint.Fq.Types.FFI where

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.C.Types

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz.Poly

data Fq = Fq {-# UNPACK #-} !(ForeignPtr CFq)
type CFq = CFmpzPoly

-- fq_poly_t -------------------------------------------------------------------

data FqPoly = FqPoly {-# UNPACK #-} !(ForeignPtr CFqPoly)
type CFqPoly = CFlint FqPoly

-- fq_mat_t --------------------------------------------------------------------

data FqMat = FqMat {-# UNPACK #-} !(ForeignPtr CFqMat)
data CFqMat = CFqMat (Ptr CFq) CLong CLong (Ptr (Ptr CFq))
