module Data.Number.Flint.Support.D.Interval.FFI (
  -- * Double-precision interval arithmetic and helpers
    Di (..)
  , CDi (..)
  -- * Basic manipulation
  , di_interval
  , arb_get_di
  , arb_set_di
  , di_print
  -- , d_randtest2
  -- , di_randtest
  -- -- * Arithmetic
  -- , di_neg
  -- -- * Fast arithmetic
  -- , di_fast_add
  -- , di_fast_sub
  -- , di_fast_mul
  -- , di_fast_div
  -- , di_fast_sqr
  -- , di_fast_add_d
  -- , di_fast_sub_d
  -- , di_fast_mul_d
  -- , di_fast_div_d
  -- , di_fast_log_nonnegative
  -- , di_fast_mid
  -- , di_fast_ubound_radius
) where

-- Double-precision interval arithmetic and helpers ----------------------------

import System.IO.Unsafe

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.C.Types
import Foreign.C.String
import Foreign.Storable

import Text.Printf

import Data.Number.Flint.Flint
import Data.Number.Flint.Arb
import Data.Number.Flint.Arb.Types
import Data.Number.Flint.Arb.Arf

#include <flint/double_interval.h>

-- di_t ------------------------------------------------------------------------

data Di = Di {-# UNPACK #-} !(ForeignPtr CDi)
data CDi = CDi CDouble CDouble deriving Show

instance Storable CDi where
  sizeOf    _ = #{size      di_t}
  alignment _ = #{alignment di_t}
  peek ptr = CDi
    <$> #{peek di_t, a} ptr
    <*> #{peek di_t, b} ptr
  poke ptr (CDi a b) = do
    #{poke di_t, a} ptr a
    #{poke di_t, b} ptr b
    

-- Basic manipulation ----------------------------------------------------------

-- | /di_interval/ /a/ /b/ 
--
-- Returns the interval \([a, b]\). We require that the endpoints are
-- ordered and not NaN.
di_interval :: CDouble -> CDouble -> CDi
di_interval a b =
  if a <= b
    then CDi a b
    else error $ printf "di_interval endpoints %g, %g not ordered.\n"
                        (realToFrac a :: Double)
                        (realToFrac b :: Double)
    
-- | /arb_get_di/ /x/ 
--
-- Returns the ball /x/ converted to a double-precision interval.
arb_get_di :: Ptr CArb -> IO CDi
arb_get_di x = do
  (_, result) <- withNewArf $ \t -> do
    arb_get_lbound_arf t x 53
    a <- arf_get_d t arf_rnd_floor
    arb_get_ubound_arf t x 53
    b <- arf_get_d t arf_rnd_ceil
    return $ CDi a b
  return result

-- | /arb_set_di/ /res/ /x/ /prec/ 
--
-- Sets the ball /res/ to the double-precision interval /x/, rounded to
-- /prec/ bits.
arb_set_di :: Ptr CArb -> CDi -> CLong -> IO ()
arb_set_di res (CDi a b) prec = do
  withNewArf $ \t -> do
    withNewArf $ \u -> do
      arf_set_d t a
      arf_set_d u b
      arb_set_interval_arf res t u prec
  return ()

-- | /di_print/ /x/ 
--
-- Prints /x/ to standard output. This simply prints decimal
-- representations of the floating-point endpoints; the decimals are not
-- guaranteed to be rounded outward.
di_print :: CDi -> IO ()
di_print (CDi a b) = do
  putStr $ printf "[%.17g, %.17g]" (realToFrac a :: Double)
                                   (realToFrac b :: Double)
  
-- -- | /d_randtest2/ /state/ 
-- --
-- -- Returns a random non-NaN @double@ with any exponent. The value can be
-- -- infinite or subnormal.
-- foreign import ccall "double_interval.h d_randtest2"
--   d_randtest2 :: Ptr CFRandState -> IO CDouble

-- -- | /di_randtest/ /state/ 
-- --
-- -- Returns an interval with random endpoints.
-- foreign import ccall "double_interval.h di_randtest"
--   di_randtest :: Ptr CFRandState -> IO CDi

-- -- Arithmetic ------------------------------------------------------------------

-- -- | /di_neg/ /x/ 
-- --
-- -- Returns the exact negation of /x/.
-- foreign import ccall "double_interval.h di_neg"
--   di_neg :: CDi -> IO CDi

-- -- Fast arithmetic -------------------------------------------------------------

-- -- The following methods perform fast but sloppy interval arithmetic: we
-- -- manipulate the endpoints with default rounding and then add or subtract
-- -- generic perturbations regardless of whether the operations were exact.
-- -- It is currently assumed that the CPU rounding mode is to nearest.
-- --
-- -- | /di_fast_add/ /x/ /y/ 
-- foreign import ccall "double_interval.h di_fast_add"
--   di_fast_add :: CDi -> CDi -> IO CDi
-- -- | /di_fast_sub/ /x/ /y/ 
-- foreign import ccall "double_interval.h di_fast_sub"
--   di_fast_sub :: CDi -> CDi -> IO CDi
-- -- | /di_fast_mul/ /x/ /y/ 
-- foreign import ccall "double_interval.h di_fast_mul"
--   di_fast_mul :: CDi -> CDi -> IO CDi
-- -- | /di_fast_div/ /x/ /y/ 
-- --
-- -- Returns the sum, difference, product or quotient of /x/ and /y/.
-- -- Division by zero is currently defined to return \([-\infty, +\infty]\).
-- foreign import ccall "double_interval.h di_fast_div"
--   di_fast_div :: CDi -> CDi -> IO CDi

-- -- | /di_fast_sqr/ /x/ 
-- --
-- -- Returns the square of /x/. The output is clamped to be nonnegative.
-- foreign import ccall "double_interval.h di_fast_sqr"
--   di_fast_sqr :: CDi -> IO CDi

-- -- | /di_fast_add_d/ /x/ /y/ 
-- foreign import ccall "double_interval.h di_fast_add_d"
--   di_fast_add_d :: CDi -> CDouble -> IO CDi
-- -- | /di_fast_sub_d/ /x/ /y/ 
-- foreign import ccall "double_interval.h di_fast_sub_d"
--   di_fast_sub_d :: CDi -> CDouble -> IO CDi
-- -- | /di_fast_mul_d/ /x/ /y/ 
-- foreign import ccall "double_interval.h di_fast_mul_d"
--   di_fast_mul_d :: CDi -> CDouble -> IO CDi
-- -- | /di_fast_div_d/ /x/ /y/ 
-- --
-- -- Arithmetic with an exact @double@ operand.
-- foreign import ccall "double_interval.h di_fast_div_d"
--   di_fast_div_d :: CDi -> CDouble -> IO CDi

-- -- | /di_fast_log_nonnegative/ /x/ 
-- --
-- -- Returns an enclosure of \(\log(x)\). The lower endpoint of /x/ is
-- -- rounded up to 0 if it is negative.
-- foreign import ccall "double_interval.h di_fast_log_nonnegative"
--   di_fast_log_nonnegative :: CDi -> IO CDi

-- -- | /di_fast_mid/ /x/ 
-- --
-- -- Returns an enclosure of the midpoint of /x/.
-- foreign import ccall "double_interval.h di_fast_mid"
--   di_fast_mid :: CDi -> IO CDi

-- -- | /di_fast_ubound_radius/ /x/ 
-- --
-- -- Returns an upper bound for the radius of /x/.
-- foreign import ccall "double_interval.h di_fast_ubound_radius"
--   di_fast_ubound_radius :: CDi -> IO CDouble

