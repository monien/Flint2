{-|
module      :  Data.Number.Flint.Support.Mpfr.Vec.FFI
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de
-}
module Data.Number.Flint.Support.Mpfr.Vec.FFI (
  -- * Vectors of MPFR floating-point numbers
  -- * Memory management
    _mpfr_vec_init
  , _mpfr_vec_clear
  -- * Arithmetic
  , _mpfr_vec_zero
  , _mpfr_vec_set
  , _mpfr_vec_add
  , _mpfr_vec_scalar_mul_mpfr
  , _mpfr_vec_scalar_mul_2exp
  , _mpfr_vec_scalar_product
) where

-- Vectors of MPFR floating-point numbers --------------------------------------

import Data.Number.Flint.Flint

import Foreign.Ptr
import Foreign.C.Types

-- Memory management -----------------------------------------------------------

-- | /_mpfr_vec_init/ /len/ /prec/ 
-- 
-- Returns a vector of the given length of initialised @mpfr@\'s with the
-- given exact precision.
foreign import ccall "mpfr_vec.h _mpfr_vec_init"
  _mpfr_vec_init :: CLong -> CFBitCnt -> IO (Ptr CMpfr)

-- | /_mpfr_vec_clear/ /vec/ /len/ 
-- 
-- Clears the given vector.
foreign import ccall "mpfr_vec.h _mpfr_vec_clear"
  _mpfr_vec_clear :: Ptr CMpfr -> CLong -> IO ()

-- Arithmetic ------------------------------------------------------------------

-- | /_mpfr_vec_zero/ /vec/ /len/ 
-- 
-- Zeros the vector @(vec, len)@.
foreign import ccall "mpfr_vec.h _mpfr_vec_zero"
  _mpfr_vec_zero :: Ptr CMpfr -> CLong -> IO ()

-- | /_mpfr_vec_set/ /vec1/ /vec2/ /len/ 
-- 
-- Copies the vector @vec2@ of the given length into @vec1@. No check is
-- made to ensure @vec1@ and @vec2@ are different.
foreign import ccall "mpfr_vec.h _mpfr_vec_set"
  _mpfr_vec_set :: Ptr CMpfr -> Ptr CMpfr -> CLong -> IO ()

-- | /_mpfr_vec_add/ /res/ /vec1/ /vec2/ /len/ 
-- 
-- Adds the given vectors of the given length together and stores the
-- result in @res@.
foreign import ccall "mpfr_vec.h _mpfr_vec_add"
  _mpfr_vec_add :: Ptr CMpfr -> Ptr CMpfr -> Ptr CMpfr -> CLong -> IO ()

-- | /_mpfr_vec_scalar_mul_mpfr/ /res/ /vec/ /len/ /c/ 
-- 
-- Multiplies the vector with given length by the scalar \(c\) and sets
-- @res@ to the result.
foreign import ccall "mpfr_vec.h _mpfr_vec_scalar_mul_mpfr"
  _mpfr_vec_scalar_mul_mpfr :: Ptr CMpfr -> Ptr CMpfr -> CLong -> Ptr CMpfr -> IO ()

-- | /_mpfr_vec_scalar_mul_2exp/ /res/ /vec/ /len/ /exp/ 
-- 
-- Multiplies the given vector of the given length by @2^exp@.
foreign import ccall "mpfr_vec.h _mpfr_vec_scalar_mul_2exp"
  _mpfr_vec_scalar_mul_2exp :: Ptr CMpfr -> Ptr CMpfr -> CLong -> CFBitCnt -> IO ()

-- | /_mpfr_vec_scalar_product/ /res/ /vec1/ /vec2/ /len/ 
-- 
-- Sets @res@ to the scalar product of @(vec1, len)@ with @(vec2, len)@.
-- Assumes @len > 0@.
foreign import ccall "mpfr_vec.h _mpfr_vec_scalar_product"
  _mpfr_vec_scalar_product :: Ptr CMpfr -> Ptr CMpfr -> Ptr CMpfr -> CLong -> IO ()

