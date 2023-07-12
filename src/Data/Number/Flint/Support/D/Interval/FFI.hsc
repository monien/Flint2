module Data.Number.Flint.Support.D.Interval.FFI (
  -- * Double-precision interval arithmetic and helpers
    Di (..)
  , CDi (..)
  -- * Basic manipulation
  , di_interval
  , arb_get_di
  , arb_set_di
  , di_print
  , di_randtest2
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
import Data.Number.Flint.Arb.Mag
import Data.Number.Flint.Support.D.Extras

#include <flint/double_interval.h>
#include <flint/double_extras.h>

d_inf = 1/0 :: CDouble 

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

_di_below x =
  if x <= 1e300 then
    x - (1e-300 + if x < 0 then -x else x) * 4.440892098500626e-16
  else
    if x /= x then -d_inf else 1e300

_di_above x =
  if x >= -1e300 then
    x + (1e-300 + if x < 0 then -x else x) * 4.440892098500626e-16
  else
    if x /= x then d_inf else -1e300
    
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
  
-- | /d_randtest2/ /state/ 
--
-- Returns a random non-NaN @double@ with any exponent. The value can be
-- infinite or subnormal.
di_randtest2 :: Ptr CFRandState -> IO CDouble
di_randtest2 state = do
  x <- d_randtest state
  return x
  
-- | /di_randtest/ /state/ 
--
-- Returns an interval with random endpoints.
di_randtest :: Ptr CFRandState -> IO CDi
di_randtest state = do
  a <- d_randtest state
  b <- d_randtest state
  return $ if a > b then CDi b a else CDi a b
    

-- Arithmetic ------------------------------------------------------------------

-- | /di_neg/ /x/ 
--
-- Returns the exact negation of /x/.
di_neg :: CDi -> CDi
di_neg (CDi a b) = CDi (-b) a

-- Fast arithmetic -------------------------------------------------------------

-- The following methods perform fast but sloppy interval arithmetic: we
-- manipulate the endpoints with default rounding and then add or subtract
-- generic perturbations regardless of whether the operations were exact.
-- It is currently assumed that the CPU rounding mode is to nearest.
--
-- | /di_fast_add/ /x/ /y/ 
di_fast_add :: CDi -> CDi -> CDi
di_fast_add (CDi a b) (CDi a' b') = CDi (_di_below (a+a')) (_di_above (b+b'))
  
-- | /di_fast_sub/ /x/ /y/ 
di_fast_sub :: CDi -> CDi -> CDi
di_fast_sub (CDi a b) (CDi a' b') = CDi (_di_below (a-b')) (_di_above (b-a'))

-- | /di_fast_mul/ /x/ /y/ 
di_fast_mul :: CDi -> CDi -> CDi
di_fast_mul (CDi xa xb) (CDi ya yb) = CDi (_di_below u) (_di_above v) where
  (u, v) 
    | xa > 0 && ya > 0 = (xa*ya, xb*yb)
    | xa > 0 && yb < 0 = (xb*ya, xa*yb)
    | xb < 0 && ya > 0 = (xa*yb, xb*ya)
    | xb < 0 && yb < 0 = (xb*yb, xa*ya)
    | a /= a || b /= b || c /= c || d /= d = (-d_inf, d_inf)
    | otherwise = (min (min a b) (min c d), max (max a b) (max c d))
    where
      a = xa * ya
      b = xa * yb
      c = xb * ya
      d = xb * yb
  
-- | /di_fast_div/ /x/ /y/ 
--
-- Returns the sum, difference, product or quotient of /x/ and /y/.
-- Division by zero is currently defined to return \([-\infty, +\infty]\).
di_fast_div :: CDi -> CDi -> CDi
di_fast_div (CDi xa xb) (CDi ya yb) = CDi (_di_below u) (_di_above v) where
  (u, v)
    | ya > 0 && xa >= 0 = (xa/yb, xb/ya)
    | ya > 0 && xb <= 0 = (xa/ya, xb/yb)
    | ya > 0            = (xa/ya, xb/ya)
    | yb < 0 && xa >= 0 = (xb/yb, xa/ya)
    | yb < 0 && xb <= 0 = (xb/ya, xa/yb)
    | yb <0             = (xb/yb, xa/yb)
    | otherwise = (-d_inf, d_inf)

-- | /di_fast_sqr/ /x/ 
--
-- Returns the square of /x/. The output is clamped to be nonnegative.
di_fast_sqr ::  CDi -> CDi
di_fast_sqr (CDi a b) =
  CDi (if a /= 0 then _di_below u else u) (_di_above b) where
  (u, v)
    | a >= 0 = (a*a, b*b)
    | b <= 0 = (b*b, a*a)
    | otherwise = (0, max (a*a) (b*b))

-- | /di_fast_add_d/ /x/ /y/ 
di_fast_add_d :: CDi -> CDouble -> CDi
di_fast_add_d x y = di_fast_add x (di_interval y y)
-- -- | /di_fast_sub_d/ /x/ /y/ 
di_fast_sub_d :: CDi -> CDouble -> CDi
di_fast_sub_d x y = di_fast_sub x (di_interval y y)
-- | /di_fast_mul_d/ /x/ /y/
di_fast_mul_d :: CDi -> CDouble -> CDi
di_fast_mul_d x y = di_fast_mul x (di_interval y y)
-- | /di_fast_div_d/ /x/ /y/
-- Arithmetic with an exact @double@ operand.
di_fast_div_d :: CDi -> CDouble -> CDi
di_fast_div_d x y = di_fast_div x (di_interval y y)

-- | /di_fast_log_nonnegative/ /x/ 
--
-- Returns an enclosure of \(\log(x)\). The lower endpoint of /x/ is
-- rounded up to 0 if it is negative.
di_fast_log_nonnegative :: CDi -> CDi
di_fast_log_nonnegative (CDi a b) = CDi a' b' where
  a' = if a <= 0 then (-d_inf) else mag_d_log_lower_bound a
  b' = mag_d_log_upper_bound b

-- | /di_fast_mid/ /x/ 
--
-- Returns an enclosure of the midpoint of /x/.
di_fast_mid :: CDi -> CDi
di_fast_mid (CDi a b)
  | a == -d_inf || b == d_inf = di_interval (-d_inf) d_inf
  | otherwise = di_fast_mul_d (di_fast_add (di_interval a a)
                                           (di_interval b b)) 0.5
                                           
-- | /di_fast_ubound_radius/ /x/ 
--
-- Returns an upper bound for the radius of /x/.
di_fast_ubound_radius :: CDi -> CDouble
di_fast_ubound_radius (CDi a b) = _di_above (0.5 * (b -a))
