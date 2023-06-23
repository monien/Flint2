module Data.Number.Flint.Support.D.Interval.FFI (
  -- * Double-precision interval arithmetic and helpers
    Di (..)
  , CDi (..)
  -- * Basic manipulation
  , di_interval
  , arb_get_di
  , arb_set_di
  , di_print
  , di_print'
  , di_fprint
  , di_get_str
  , d_randtest2
  , di_randtest
  -- * Arithmetic
  , di_neg
  -- * Fast arithmetic
  , di_fast_add
  , di_fast_sub
  , di_fast_mul
  , di_fast_div
  , di_fast_sqr
  , di_fast_add_d
  , di_fast_sub_d
  , di_fast_mul_d
  , di_fast_div_d
  , di_fast_log_nonnegative
  , di_fast_mid
  , di_fast_ubound_radius
) where

-- Double-precision interval arithmetic and helpers ----------------------------

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.C.Types
import Foreign.C.String
import Foreign.Storable

import Data.Number.Flint.Flint
import Data.Number.Flint.Arb.Types

#include <flint/double_interval.h>

-- di_t ------------------------------------------------------------------------

data Di = Di {-# UNPACK #-} !(ForeignPtr CDi)
data CDi = CDi CDouble CDouble

instance Storable CDi where
  sizeOf    _ = #{size      di_t}
  alignment _ = #{alignment di_t}
  peek = undefined
  poke = undefined

-- Basic manipulation ----------------------------------------------------------

-- | /di_interval/ /a/ /b/ 
--
-- Returns the interval \([a, b]\). We require that the endpoints are
-- ordered and not NaN.
foreign import ccall "double_interval.h di_interval"
  di_interval :: CDouble -> CDouble -> IO (Ptr CDi)

-- | /arb_get_di/ /x/ 
--
-- Returns the ball /x/ converted to a double-precision interval.
foreign import ccall "double_interval.h arb_get_di"
  arb_get_di :: Ptr CArb -> IO (Ptr CDi)

-- | /arb_set_di/ /res/ /x/ /prec/ 
--
-- Sets the ball /res/ to the double-precision interval /x/, rounded to
-- /prec/ bits.
foreign import ccall "double_interval.h arb_set_di"
  arb_set_di :: Ptr CArb -> Ptr CDi -> CLong -> IO ()

foreign import ccall "double_interval.h di_print"
  di_get_str :: Ptr CDi -> IO CString

foreign import ccall "double_interval.h di_print"
  di_fprint :: Ptr CFile -> Ptr CDi -> IO ()

-- | /di_print/ /x/ 
--
-- Prints /x/ to standard output. This simply prints decimal
-- representations of the floating-point endpoints; the decimals are not
-- guaranteed to be rounded outward.
foreign import ccall "double_interval.h di_print"
  di_print :: Ptr CDi -> IO ()


di_print' :: Ptr CDi -> IO ()
di_print' x = do
  printCStr di_get_str x
  return ()
  
-- | /d_randtest2/ /state/ 
--
-- Returns a random non-NaN @double@ with any exponent. The value can be
-- infinite or subnormal.
foreign import ccall "double_interval.h d_randtest2"
  d_randtest2 :: Ptr CFRandState -> IO CDouble

-- | /di_randtest/ /state/ 
--
-- Returns an interval with random endpoints.
foreign import ccall "double_interval.h di_randtest"
  di_randtest :: Ptr CFRandState -> IO (Ptr CDi)

-- Arithmetic ------------------------------------------------------------------

-- | /di_neg/ /x/ 
--
-- Returns the exact negation of /x/.
foreign import ccall "double_interval.h di_neg"
  di_neg :: Ptr CDi -> IO (Ptr CDi)

-- Fast arithmetic -------------------------------------------------------------

-- The following methods perform fast but sloppy interval arithmetic: we
-- manipulate the endpoints with default rounding and then add or subtract
-- generic perturbations regardless of whether the operations were exact.
-- It is currently assumed that the CPU rounding mode is to nearest.
--
-- | /di_fast_add/ /x/ /y/ 
foreign import ccall "double_interval.h di_fast_add"
  di_fast_add :: Ptr CDi -> Ptr CDi -> IO (Ptr CDi)
-- | /di_fast_sub/ /x/ /y/ 
foreign import ccall "double_interval.h di_fast_sub"
  di_fast_sub :: Ptr CDi -> Ptr CDi -> IO (Ptr CDi)
-- | /di_fast_mul/ /x/ /y/ 
foreign import ccall "double_interval.h di_fast_mul"
  di_fast_mul :: Ptr CDi -> Ptr CDi -> IO (Ptr CDi)
-- | /di_fast_div/ /x/ /y/ 
--
-- Returns the sum, difference, product or quotient of /x/ and /y/.
-- Division by zero is currently defined to return \([-\infty, +\infty]\).
foreign import ccall "double_interval.h di_fast_div"
  di_fast_div :: Ptr CDi -> Ptr CDi -> IO (Ptr CDi)

-- | /di_fast_sqr/ /x/ 
--
-- Returns the square of /x/. The output is clamped to be nonnegative.
foreign import ccall "double_interval.h di_fast_sqr"
  di_fast_sqr :: Ptr CDi -> IO (Ptr CDi)

-- | /di_fast_add_d/ /x/ /y/ 
foreign import ccall "double_interval.h di_fast_add_d"
  di_fast_add_d :: Ptr CDi -> CDouble -> IO (Ptr CDi)
-- | /di_fast_sub_d/ /x/ /y/ 
foreign import ccall "double_interval.h di_fast_sub_d"
  di_fast_sub_d :: Ptr CDi -> CDouble -> IO (Ptr CDi)
-- | /di_fast_mul_d/ /x/ /y/ 
foreign import ccall "double_interval.h di_fast_mul_d"
  di_fast_mul_d :: Ptr CDi -> CDouble -> IO (Ptr CDi)
-- | /di_fast_div_d/ /x/ /y/ 
--
-- Arithmetic with an exact @double@ operand.
foreign import ccall "double_interval.h di_fast_div_d"
  di_fast_div_d :: Ptr CDi -> CDouble -> IO (Ptr CDi)

-- | /di_fast_log_nonnegative/ /x/ 
--
-- Returns an enclosure of \(\log(x)\). The lower endpoint of /x/ is
-- rounded up to 0 if it is negative.
foreign import ccall "double_interval.h di_fast_log_nonnegative"
  di_fast_log_nonnegative :: Ptr CDi -> IO (Ptr CDi)

-- | /di_fast_mid/ /x/ 
--
-- Returns an enclosure of the midpoint of /x/.
foreign import ccall "double_interval.h di_fast_mid"
  di_fast_mid :: Ptr CDi -> IO (Ptr CDi)

-- | /di_fast_ubound_radius/ /x/ 
--
-- Returns an upper bound for the radius of /x/.
foreign import ccall "double_interval.h di_fast_ubound_radius"
  di_fast_ubound_radius :: Ptr CDi -> IO CDouble

