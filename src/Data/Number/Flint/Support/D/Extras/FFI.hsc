{-|
module      :  Data.Number.Flint.Support.D.Extras.FFI
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de
-}
module Data.Number.Flint.Support.D.Extras.FFI (
  -- * Support functions for double arithmetic
  -- * Random functions
    d_randtest
  , d_randtest_signed
  , d_randtest_special
  -- * Arithmetic
  , d_polyval
  -- * Special functions
  , d_lambertw
  , d_is_nan
  , d_log2
) where

-- Support functions for double arithmetic -------------------------------------

import Foreign.Ptr
import Foreign.C.Types

import Data.Number.Flint.Flint

-- Random functions ------------------------------------------------------------

-- | /d_randtest/ /state/ 
--
-- Returns a random number in the interval \([0.5, 1)\).
foreign import ccall "double_extras.h d_randtest"
  d_randtest :: Ptr CFRandState -> IO CDouble

-- | /d_randtest_signed/ /state/ /minexp/ /maxexp/ 
--
-- Returns a random signed number with exponent between @minexp@ and
-- @maxexp@ or zero.
foreign import ccall "double_extras.h d_randtest_signed"
  d_randtest_signed :: Ptr CFRandState -> CLong -> CLong -> IO CDouble

-- | /d_randtest_special/ /state/ /minexp/ /maxexp/ 
--
-- Returns a random signed number with exponent between @minexp@ and
-- @maxexp@, zero, @D_NAN@ or \(\pm\)@D_INF@.
foreign import ccall "double_extras.h d_randtest_special"
  d_randtest_special :: Ptr CFRandState -> CLong -> CLong -> IO CDouble

-- Arithmetic ------------------------------------------------------------------

-- | /d_polyval/ /poly/ /len/ /x/ 
--
-- Uses Horner\'s rule to evaluate the polynomial defined by the given
-- @len@ coefficients. Requires that @len@ is nonzero.
foreign import ccall "double_extras.h d_polyval"
  d_polyval :: Ptr CDouble -> CInt -> CDouble -> IO CDouble

-- Special functions -----------------------------------------------------------

-- | /d_lambertw/ /x/ 
--
-- Computes the principal branch of the Lambert W function, solving the
-- equation \(x = W(x) \exp(W(x))\). If \(x < -1/e\), the solution is
-- complex, and NaN is returned.
-- 
-- Depending on the magnitude of \(x\), we start from a piecewise rational
-- approximation or a zeroth-order truncation of the asymptotic expansion
-- at infinity, and perform 0, 1 or 2 iterations with Halley\'s method to
-- obtain full accuracy.
-- 
-- A test of \(10^7\) random inputs showed a maximum relative error smaller
-- than 0.95 times @DBL_EPSILON@ (2^{-52}) for positive \(x\). Accuracy for
-- negative \(x\) is slightly worse, and can grow to about 10 times
-- @DBL_EPSILON@ close to \(-1/e\). However, accuracy may be worse
-- depending on compiler flags and the accuracy of the system libm
-- functions.
foreign import ccall "double_extras.h d_lambertw"
  d_lambertw :: CDouble -> IO CDouble

-- | /d_is_nan/ /x/ 
--
-- Returns a nonzero integral value if @x@ is @D_NAN@, and otherwise
-- returns 0.
foreign import ccall "double_extras.h d_is_nan"
  d_is_nan :: CDouble -> IO CInt

-- | /d_log2/ /x/ 
--
-- Returns the base 2 logarithm of @x@ provided @x@ is positive. If a
-- domain or pole error occurs, the appropriate error value is returned.
foreign import ccall "double_extras.h d_log2"
  d_log2 :: CDouble -> IO CDouble

