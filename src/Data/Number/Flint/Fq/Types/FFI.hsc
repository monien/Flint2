{-|
module      :  Data.Number.Flint.Fq.Types.FFI
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de
-}
module Data.Number.Flint.Fq.Types.FFI where

import Foreign.ForeignPtr

import Data.Number.Flint.Flint

-- fq_poly_t -------------------------------------------------------------------

data FqPoly = FqPoly {-# UNPACK #-} !(ForeignPtr CFqPoly)
type CFqPoly = CFlint FqPoly

-- fq_mat_t --------------------------------------------------------------------

data FqMat = FqMat {-# UNPACK #-} !(ForeignPtr CFqMat)
type CFqMat = CFlint FqMat
