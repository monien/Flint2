{-|
module      :  Data.Number.Flint.Support.Mpf.Vec.FFI
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de
-}
module Data.Number.Flint.Support.Mpf.Vec.FFI (
  -- * Vectors of MPF floating-point numbers
  -- * Memory management
    _mpf_vec_init
  , _mpf_vec_clear
  -- * Randomisation
  , _mpf_vec_randtest
  -- * Assignment and basic manipulation
  , _mpf_vec_zero
  , _mpf_vec_set
  -- * Conversion
  , _mpf_vec_set_fmpz_vec
  -- * Comparison
  , _mpf_vec_equal
  , _mpf_vec_is_zero
  , _mpf_vec_approx_equal
  -- * Addition and subtraction
  , _mpf_vec_add
  , _mpf_vec_sub
  -- * Scalar multiplication
  , _mpf_vec_scalar_mul_mpf
  , _mpf_vec_scalar_mul_2exp
  -- * Dot product and norm
  , _mpf_vec_dot
  , _mpf_vec_norm
  , _mpf_vec_dot2
  , _mpf_vec_norm2
) where 

-- Vectors of MPF floating-point numbers ---------------------------------------

import Foreign.Ptr
import Foreign.C.Types

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz

-- Memory management -----------------------------------------------------------

-- | /_mpf_vec_init/ /len/ 
-- 
-- Returns a vector of the given length of initialised @mpf@\'s with at
-- least the given precision.
foreign import ccall "mpf_vec.h _mpf_vec_init"
  _mpf_vec_init :: CLong -> IO (Ptr CMpf)

-- | /_mpf_vec_clear/ /vec/ /len/ 
-- 
-- Clears the given vector.
foreign import ccall "mpf_vec.h _mpf_vec_clear"
  _mpf_vec_clear :: Ptr CMpf -> CLong -> IO ()

-- Randomisation ---------------------------------------------------------------

-- | /_mpf_vec_randtest/ /f/ /state/ /len/ /bits/ 
-- 
-- Sets the entries of a vector of the given length to random numbers in
-- the interval \([0, 1)\) with @bits@ significant bits in the mantissa or
-- less if their precision is smaller.
foreign import ccall "mpf_vec.h _mpf_vec_randtest"
  _mpf_vec_randtest :: Ptr CMpf -> Ptr CFRandState -> CLong -> CFBitCnt -> IO ()

-- Assignment and basic manipulation -------------------------------------------

-- | /_mpf_vec_zero/ /vec/ /len/ 
-- 
-- Zeros the vector @(vec, len)@.
foreign import ccall "mpf_vec.h _mpf_vec_zero"
  _mpf_vec_zero :: Ptr CMpf -> CLong -> IO ()

-- | /_mpf_vec_set/ /vec1/ /vec2/ /len2/ 
-- 
-- Copies the vector @vec2@ of the given length into @vec1@. A check is
-- made to ensure @vec1@ and @vec2@ are different.
foreign import ccall "mpf_vec.h _mpf_vec_set"
  _mpf_vec_set :: Ptr CMpf -> Ptr CMpf -> CLong -> IO ()

-- Conversion ------------------------------------------------------------------

-- | /_mpf_vec_set_fmpz_vec/ /appv/ /vec/ /len/ 
-- 
-- Export the array of @len@ entries starting at the pointer @vec@ to an
-- array of mpfs @appv@.
foreign import ccall "mpf_vec.h _mpf_vec_set_fmpz_vec"
  _mpf_vec_set_fmpz_vec :: Ptr CMpf -> Ptr CFmpz -> CLong -> IO ()

-- Comparison ------------------------------------------------------------------

-- | /_mpf_vec_equal/ /vec1/ /vec2/ /len/ 
-- 
-- Compares two vectors of the given length and returns \(1\) if they are
-- equal, otherwise returns \(0\).
foreign import ccall "mpf_vec.h _mpf_vec_equal"
  _mpf_vec_equal :: Ptr CMpf -> Ptr CMpf -> CLong -> IO CInt

-- | /_mpf_vec_is_zero/ /vec/ /len/ 
-- 
-- Returns \(1\) if @(vec, len)@ is zero, and \(0\) otherwise.
foreign import ccall "mpf_vec.h _mpf_vec_is_zero"
  _mpf_vec_is_zero :: Ptr CMpf -> CLong -> IO CInt

-- | /_mpf_vec_approx_equal/ /vec1/ /vec2/ /len/ /bits/ 
-- 
-- Compares two vectors of the given length and returns \(1\) if the first
-- @bits@ bits of their entries are equal, otherwise returns \(0\).
foreign import ccall "mpf_vec.h _mpf_vec_approx_equal"
  _mpf_vec_approx_equal :: Ptr CMpf -> Ptr CMpf -> CLong -> CFBitCnt -> IO CInt

-- Addition and subtraction ----------------------------------------------------

-- | /_mpf_vec_add/ /res/ /vec1/ /vec2/ /len2/ 
-- 
-- Adds the given vectors of the given length together and stores the
-- result in @res@.
foreign import ccall "mpf_vec.h _mpf_vec_add"
  _mpf_vec_add :: Ptr CMpf -> Ptr CMpf -> Ptr CMpf -> CLong -> IO ()

-- | /_mpf_vec_sub/ /res/ /vec1/ /vec2/ /len2/ 
-- 
-- Sets @(res, len2)@ to @(vec1, len2)@ minus @(vec2, len2)@.
foreign import ccall "mpf_vec.h _mpf_vec_sub"
  _mpf_vec_sub :: Ptr CMpf -> Ptr CMpf -> Ptr CMpf -> CLong -> IO ()

-- Scalar multiplication -------------------------------------------------------

-- | /_mpf_vec_scalar_mul_mpf/ /res/ /vec/ /len/ /c/ 
-- 
-- Multiplies the vector with given length by the scalar \(c\) and sets
-- @res@ to the result.
foreign import ccall "mpf_vec.h _mpf_vec_scalar_mul_mpf"
  _mpf_vec_scalar_mul_mpf :: Ptr CMpf -> Ptr CMpf -> CLong -> Ptr CMpf -> IO ()

-- | /_mpf_vec_scalar_mul_2exp/ /res/ /vec/ /len/ /exp/ 
-- 
-- Multiplies the given vector of the given length by @2^exp@.
foreign import ccall "mpf_vec.h _mpf_vec_scalar_mul_2exp"
  _mpf_vec_scalar_mul_2exp :: Ptr CMpf -> Ptr CMpf -> CLong -> CFBitCnt -> IO ()

-- Dot product and norm --------------------------------------------------------

-- | /_mpf_vec_dot/ /res/ /vec1/ /vec2/ /len2/ 
-- 
-- Sets @res@ to the dot product of @(vec1, len2)@ with @(vec2, len2)@.
foreign import ccall "mpf_vec.h _mpf_vec_dot"
  _mpf_vec_dot :: Ptr CMpf -> Ptr CMpf -> Ptr CMpf -> CLong -> IO ()

-- | /_mpf_vec_norm/ /res/ /vec/ /len/ 
-- 
-- Sets @res@ to the square of the Euclidean norm of @(vec, len)@.
foreign import ccall "mpf_vec.h _mpf_vec_norm"
  _mpf_vec_norm :: Ptr CMpf -> Ptr CMpf -> CLong -> IO ()

-- | /_mpf_vec_dot2/ /res/ /vec1/ /vec2/ /len2/ /prec/ 
-- 
-- Sets @res@ to the dot product of @(vec1, len2)@ with @(vec2, len2)@. The
-- temporary variable used has its precision set to be at least @prec@
-- bits. Returns 0 if a probable cancellation is detected, and otherwise
-- returns a non-zero value.
foreign import ccall "mpf_vec.h _mpf_vec_dot2"
  _mpf_vec_dot2 :: Ptr CMpf -> Ptr CMpf -> Ptr CMpf -> CLong -> CFBitCnt -> IO CInt

-- | /_mpf_vec_norm2/ /res/ /vec/ /len/ /prec/ 
-- 
-- Sets @res@ to the square of the Euclidean norm of @(vec, len)@. The
-- temporary variable used has its precision set to be at least @prec@
-- bits.
foreign import ccall "mpf_vec.h _mpf_vec_norm2"
  _mpf_vec_norm2 :: Ptr CMpf -> Ptr CMpf -> CLong -> CFBitCnt -> IO ()

