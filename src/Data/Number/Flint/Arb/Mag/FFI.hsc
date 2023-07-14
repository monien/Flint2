{-|
module      :  Data.Number.Flint.Arb.Mag.FFI
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de
-}
module Data.Number.Flint.Arb.Mag.FFI (
  -- * Fixed-precision unsigned floating-point numbers for bounds
  -- * Types
    Mag (..)
  , CMag (..)
  , newMag
  , withMag
  , withNewMag
  -- * Memory management
  , mag_init
  , mag_clear
  , mag_swap
  , _mag_vec_init
  , _mag_vec_clear
  , mag_allocated_bytes
  -- * Special values
  , mag_zero
  , mag_one
  , mag_inf
  , mag_is_special
  , mag_is_zero
  , mag_is_inf
  , mag_is_finite
  , mag_d_log_lower_bound
  , mag_d_log_upper_bound
  -- * Assignment and conversions
  , mag_init_set
  , mag_set
  , mag_set_d
  , mag_set_ui
  , mag_set_fmpz
  , mag_set_d_lower
  , mag_set_ui_lower
  , mag_set_fmpz_lower
  , mag_set_d_2exp_fmpz
  , mag_set_fmpz_2exp_fmpz
  , mag_set_ui_2exp_si
  , mag_set_d_2exp_fmpz_lower
  , mag_set_fmpz_2exp_fmpz_lower
  , mag_get_d
  , mag_get_d_log2_approx
  , mag_get_fmpq
  , mag_get_fmpz
  , mag_get_fmpz_lower
  -- * Comparisons
  , mag_equal
  , mag_cmp
  , mag_cmp_2exp_si
  , mag_min
  , mag_max
  -- * Input and output
  , mag_print
  , mag_fprint
  , mag_dump_str
  , mag_load_str
  , mag_dump_file
  , mag_load_file
  -- * Random generation
  , mag_randtest
  , mag_randtest_special
  -- * Arithmetic
  , mag_add
  , mag_add_ui
  , mag_add_lower
  , mag_add_ui_lower
  , mag_add_2exp_fmpz
  , mag_add_ui_2exp_si
  , mag_sub
  , mag_sub_lower
  , mag_mul_2exp_si
  , mag_mul_2exp_fmpz
  , mag_mul
  , mag_mul_ui
  , mag_mul_fmpz
  , mag_mul_lower
  , mag_mul_ui_lower
  , mag_mul_fmpz_lower
  , mag_addmul
  , mag_div
  , mag_div_ui
  , mag_div_fmpz
  , mag_div_lower
  , mag_inv
  , mag_inv_lower
  -- * Fast, unsafe arithmetic
  , mag_fast_init_set
  , mag_fast_zero
  , mag_fast_is_zero
  , mag_fast_mul
  , mag_fast_addmul
  , mag_fast_add_2exp_si
  , mag_fast_mul_2exp_si
  -- * Powers and logarithms
  , mag_pow_ui
  , mag_pow_fmpz
  , mag_pow_ui_lower
  , mag_pow_fmpz_lower
  , mag_sqrt
  , mag_sqrt_lower
  , mag_rsqrt
  , mag_rsqrt_lower
  , mag_hypot
  , mag_root
  , mag_log
  , mag_log_lower
  , mag_neg_log
  , mag_neg_log_lower
  , mag_log_ui
  , mag_log1p
  , mag_exp
  , mag_exp_lower
  , mag_expinv
  , mag_expinv_lower
  , mag_expm1
  , mag_exp_tail
  , mag_binpow_uiui
  , mag_geom_series
  -- * Special functions
  , mag_const_pi
  , mag_const_pi_lower
  , mag_atan
  , mag_atan_lower
  , mag_cosh
  , mag_cosh_lower
  , mag_sinh
  , mag_sinh_lower
  , mag_fac_ui
  , mag_rfac_ui
  , mag_bin_uiui
  , mag_bernoulli_div_fac_ui
  , mag_polylog_tail
  , mag_hurwitz_zeta_uiui
) where

-- Fixed-precision unsigned floating-point numbers for bounds ------------------

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.C.Types
import Foreign.C.String
import Foreign.Storable
import Foreign.Marshal.Alloc (free)

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpq
import Data.Number.Flint.Arb.Types

#include <flint/mag.h>

-- Types -----------------------------------------------------------------------

newMag = do
  x <- mallocForeignPtr
  withForeignPtr x mag_init
  addForeignPtrFinalizer p_mag_clear x
  return $ Mag x

withMag (Mag p) f = do
  withForeignPtr p $ \fp -> (Mag p,) <$> f fp

withNewMag f = do
  x <- newMag
  withMag x f
    
-- Memory management -----------------------------------------------------------

-- | /mag_init/ /x/ 
-- 
-- Initializes the variable /x/ for use. Its value is set to zero.
foreign import ccall "mag.h mag_init"
  mag_init :: Ptr CMag -> IO ()

-- | /mag_clear/ /x/ 
-- 
-- Clears the variable /x/, freeing or recycling its allocated memory.
foreign import ccall "mag.h mag_clear"
  mag_clear :: Ptr CMag -> IO ()

foreign import ccall "mag.h &mag_clear"
  p_mag_clear :: FunPtr (Ptr CMag -> IO ())

-- | /mag_swap/ /x/ /y/ 
-- 
-- Swaps /x/ and /y/ efficiently.
foreign import ccall "mag.h mag_swap"
  mag_swap :: Ptr CMag -> Ptr CMag -> IO ()

-- | /_mag_vec_init/ /n/ 
-- 
-- Allocates a vector of length /n/. All entries are set to zero.
foreign import ccall "mag.h _mag_vec_init"
  _mag_vec_init :: CLong -> IO (Ptr CMag)

-- | /_mag_vec_clear/ /v/ /n/ 
-- 
-- Clears a vector of length /n/.
foreign import ccall "mag.h _mag_vec_clear"
  _mag_vec_clear :: (Ptr CMag) -> CLong -> IO ()

-- | /mag_allocated_bytes/ /x/ 
-- 
-- Returns the total number of bytes heap-allocated internally by this
-- object. The count excludes the size of the structure itself. Add
-- @sizeof(mag_struct)@ to get the size of the object as a whole.
foreign import ccall "mag.h mag_allocated_bytes"
  mag_allocated_bytes :: Ptr CMag -> IO CLong

-- Special values --------------------------------------------------------------

-- | /mag_zero/ /res/ 
-- 
-- Sets /res/ to zero.
foreign import ccall "mag.h mag_zero"
  mag_zero :: Ptr CMag -> IO ()

-- | /mag_one/ /res/ 
-- 
-- Sets /res/ to one.
foreign import ccall "mag.h mag_one"
  mag_one :: Ptr CMag -> IO ()

-- | /mag_inf/ /res/ 
-- 
-- Sets /res/ to positive infinity.
foreign import ccall "mag.h mag_inf"
  mag_inf :: Ptr CMag -> IO ()

-- | /mag_is_special/ /x/ 
-- 
-- Returns nonzero iff /x/ is zero or positive infinity.
foreign import ccall "mag.h mag_is_special"
  mag_is_special :: Ptr CMag -> IO CInt

-- | /mag_is_zero/ /x/ 
-- 
-- Returns nonzero iff /x/ is zero.
foreign import ccall "mag.h mag_is_zero"
  mag_is_zero :: Ptr CMag -> IO CInt

-- | /mag_is_inf/ /x/ 
-- 
-- Returns nonzero iff /x/ is positive infinity.
foreign import ccall "mag.h mag_is_inf"
  mag_is_inf :: Ptr CMag -> IO CInt

-- | /mag_is_finite/ /x/ 
-- 
-- Returns nonzero iff /x/ is not positive infinity (since there is no NaN
-- value, this function is exactly the logical negation of @mag_is_inf@).
foreign import ccall "mag.h mag_is_finite"
  mag_is_finite :: Ptr CMag -> IO CInt

foreign import ccall "mag.h mag_d_log_lower_bound"
  mag_d_log_lower_bound :: CDouble -> CDouble

foreign import ccall "mag.h mag_d_log_upper_bound"
  mag_d_log_upper_bound :: CDouble -> CDouble

-- Assignment and conversions --------------------------------------------------

-- | /mag_init_set/ /res/ /x/ 
-- 
-- Initializes /res/ and sets it to the value of /x/. This operation is
-- always exact.
foreign import ccall "mag.h mag_init_set"
  mag_init_set :: Ptr CMag -> Ptr CMag -> IO ()

-- | /mag_set/ /res/ /x/ 
-- 
-- Sets /res/ to the value of /x/. This operation is always exact.
foreign import ccall "mag.h mag_set"
  mag_set :: Ptr CMag -> Ptr CMag -> IO ()

foreign import ccall "mag.h mag_set_d"
  mag_set_d :: Ptr CMag -> CDouble -> IO ()

foreign import ccall "mag.h mag_set_ui"
  mag_set_ui :: Ptr CMag -> CULong -> IO ()

-- | /mag_set_fmpz/ /res/ /x/ 
-- 
-- Sets /res/ to an upper bound for \(|x|\). The operation may be inexact
-- even if /x/ is exactly representable.
foreign import ccall "mag.h mag_set_fmpz"
  mag_set_fmpz :: Ptr CMag -> Ptr CFmpz -> IO ()

foreign import ccall "mag.h mag_set_d_lower"
  mag_set_d_lower :: Ptr CMag -> CDouble -> IO ()

foreign import ccall "mag.h mag_set_ui_lower"
  mag_set_ui_lower :: Ptr CMag -> CULong -> IO ()

-- | /mag_set_fmpz_lower/ /res/ /x/ 
-- 
-- Sets /res/ to a lower bound for \(|x|\). The operation may be inexact
-- even if /x/ is exactly representable.
foreign import ccall "mag.h mag_set_fmpz_lower"
  mag_set_fmpz_lower :: Ptr CMag -> Ptr CFmpz -> IO ()

foreign import ccall "mag.h mag_set_d_2exp_fmpz"
  mag_set_d_2exp_fmpz :: Ptr CMag -> CDouble -> Ptr CFmpz -> IO ()

foreign import ccall "mag.h mag_set_fmpz_2exp_fmpz"
  mag_set_fmpz_2exp_fmpz :: Ptr CMag -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /mag_set_ui_2exp_si/ /res/ /x/ /y/ 
-- 
-- Sets /res/ to an upper bound for \(|x| \cdot 2^y\).
foreign import ccall "mag.h mag_set_ui_2exp_si"
  mag_set_ui_2exp_si :: Ptr CMag -> CULong -> CLong -> IO ()

foreign import ccall "mag.h mag_set_d_2exp_fmpz_lower"
  mag_set_d_2exp_fmpz_lower :: Ptr CMag -> CDouble -> Ptr CFmpz -> IO ()

-- | /mag_set_fmpz_2exp_fmpz_lower/ /res/ /x/ /y/ 
-- 
-- Sets /res/ to a lower bound for \(|x| \cdot 2^y\).
foreign import ccall "mag.h mag_set_fmpz_2exp_fmpz_lower"
  mag_set_fmpz_2exp_fmpz_lower :: Ptr CMag -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /mag_get_d/ /x/ 
-- 
-- Returns a /double/ giving an upper bound for /x/.
foreign import ccall "mag.h mag_get_d"
  mag_get_d :: Ptr CMag -> IO CDouble

-- | /mag_get_d_log2_approx/ /x/ 
-- 
-- Returns a /double/ approximating \(\log_2(x)\), suitable for estimating
-- magnitudes (warning: not a rigorous bound). The value is clamped between
-- /COEFF_MIN/ and /COEFF_MAX/.
foreign import ccall "mag.h mag_get_d_log2_approx"
  mag_get_d_log2_approx :: Ptr CMag -> IO CDouble

foreign import ccall "mag.h mag_get_fmpq"
  mag_get_fmpq :: Ptr CFmpq -> Ptr CMag -> IO ()

foreign import ccall "mag.h mag_get_fmpz"
  mag_get_fmpz :: Ptr CFmpz -> Ptr CMag -> IO ()

-- | /mag_get_fmpz_lower/ /res/ /x/ 
-- 
-- Sets /res/, respectively, to the exact rational number represented by
-- /x/, the integer exactly representing the ceiling function of /x/, or
-- the integer exactly representing the floor function of /x/.
-- 
-- These functions are unsafe: the user must check in advance that /x/ is
-- of reasonable magnitude. If /x/ is infinite or has a bignum exponent, an
-- abort will be raised. If the exponent otherwise is too large or too
-- small, the available memory could be exhausted resulting in undefined
-- behavior.
foreign import ccall "mag.h mag_get_fmpz_lower"
  mag_get_fmpz_lower :: Ptr CFmpz -> Ptr CMag -> IO ()

-- Comparisons -----------------------------------------------------------------

-- | /mag_equal/ /x/ /y/ 
-- 
-- Returns nonzero iff /x/ and /y/ have the same value.
foreign import ccall "mag.h mag_equal"
  mag_equal :: Ptr CMag -> Ptr CMag -> IO CInt

-- | /mag_cmp/ /x/ /y/ 
-- 
-- Returns negative, zero, or positive, depending on whether /x/ is
-- smaller, equal, or larger than /y/.
foreign import ccall "mag.h mag_cmp"
  mag_cmp :: Ptr CMag -> Ptr CMag -> IO CInt

-- | /mag_cmp_2exp_si/ /x/ /y/ 
-- 
-- Returns negative, zero, or positive, depending on whether /x/ is
-- smaller, equal, or larger than \(2^y\).
foreign import ccall "mag.h mag_cmp_2exp_si"
  mag_cmp_2exp_si :: Ptr CMag -> CLong -> IO CInt

foreign import ccall "mag.h mag_min"
  mag_min :: Ptr CMag -> Ptr CMag -> Ptr CMag -> IO ()

-- | /mag_max/ /res/ /x/ /y/ 
-- 
-- Sets /res/ respectively to the smaller or the larger of /x/ and /y/.
foreign import ccall "mag.h mag_max"
  mag_max :: Ptr CMag -> Ptr CMag -> Ptr CMag -> IO ()

-- Input and output ------------------------------------------------------------

-- | /mag_print/ /x/ 
-- 
-- Prints /x/ to standard output.
mag_print x = do
  cs <- mag_get_str x
  s <- peekCString cs
  free cs
  putStr s
  
-- | /mag_fprint/ /file/ /x/ 
-- 
-- Prints /x/ to the stream /file/.
foreign import ccall "mag.h mag_fprint"
  mag_fprint :: Ptr CFile -> Ptr CMag -> IO ()

-- | /mag_get_str/ /x/
-- Returns a string representation of /x/. The memory needs to be deallocated
-- with /flint_free/
foreign import ccall "mag.h mag_get_str"
  mag_get_str :: Ptr CMag -> IO CString
  
-- | /mag_dump_str/ /x/ 
-- 
-- Allocates a string and writes a binary representation of /x/ to it that
-- can be read by @mag_load_str@. The returned string needs to be
-- deallocated with /flint_free/.
foreign import ccall "mag.h mag_dump_str"
  mag_dump_str :: Ptr CMag -> IO CString

-- | /mag_load_str/ /x/ /str/ 
-- 
-- Parses /str/ into /x/. Returns a nonzero value if /str/ is not formatted
-- correctly.
foreign import ccall "mag.h mag_load_str"
  mag_load_str :: Ptr CMag -> CString -> IO CInt

-- | /mag_dump_file/ /stream/ /x/ 
-- 
-- Writes a binary representation of /x/ to /stream/ that can be read by
-- @mag_load_file@. Returns a nonzero value if the data could not be
-- written.
foreign import ccall "mag.h mag_dump_file"
  mag_dump_file :: Ptr CFile -> Ptr CMag -> IO CInt

-- | /mag_load_file/ /x/ /stream/ 
-- 
-- Reads /x/ from /stream/. Returns a nonzero value if the data is not
-- formatted correctly or the read failed. Note that the data is assumed to
-- be delimited by a whitespace or end-of-file, i.e., when writing multiple
-- values with @mag_dump_file@ make sure to insert a whitespace to separate
-- consecutive values.
foreign import ccall "mag.h mag_load_file"
  mag_load_file :: Ptr CMag -> Ptr CFile -> IO CInt

-- Random generation -----------------------------------------------------------

-- | /mag_randtest/ /res/ /state/ /expbits/ 
-- 
-- Sets /res/ to a random finite value, with an exponent up to /expbits/
-- bits large.
foreign import ccall "mag.h mag_randtest"
  mag_randtest :: Ptr CMag -> Ptr CFRandState -> CLong -> IO ()

-- | /mag_randtest_special/ /res/ /state/ /expbits/ 
-- 
-- Like @mag_randtest@, but also sometimes sets /res/ to infinity.
foreign import ccall "mag.h mag_randtest_special"
  mag_randtest_special :: Ptr CMag -> Ptr CFRandState -> CLong -> IO ()

-- Arithmetic ------------------------------------------------------------------

foreign import ccall "mag.h mag_add"
  mag_add :: Ptr CMag -> Ptr CMag -> Ptr CMag -> IO ()

-- | /mag_add_ui/ /res/ /x/ /y/ 
-- 
-- Sets /res/ to an upper bound for \(x + y\).
foreign import ccall "mag.h mag_add_ui"
  mag_add_ui :: Ptr CMag -> Ptr CMag -> CULong -> IO ()

foreign import ccall "mag.h mag_add_lower"
  mag_add_lower :: Ptr CMag -> Ptr CMag -> Ptr CMag -> IO ()

-- | /mag_add_ui_lower/ /res/ /x/ /y/ 
-- 
-- Sets /res/ to a lower bound for \(x + y\).
foreign import ccall "mag.h mag_add_ui_lower"
  mag_add_ui_lower :: Ptr CMag -> Ptr CMag -> CULong -> IO ()

-- | /mag_add_2exp_fmpz/ /res/ /x/ /e/ 
-- 
-- Sets /res/ to an upper bound for \(x + 2^e\).
foreign import ccall "mag.h mag_add_2exp_fmpz"
  mag_add_2exp_fmpz :: Ptr CMag -> Ptr CMag -> Ptr CFmpz -> IO ()

-- | /mag_add_ui_2exp_si/ /res/ /x/ /y/ /e/ 
-- 
-- Sets /res/ to an upper bound for \(x + y 2^e\).
foreign import ccall "mag.h mag_add_ui_2exp_si"
  mag_add_ui_2exp_si :: Ptr CMag -> Ptr CMag -> CULong -> CLong -> IO ()

-- | /mag_sub/ /res/ /x/ /y/ 
-- 
-- Sets /res/ to an upper bound for \(\max(x-y, 0)\).
foreign import ccall "mag.h mag_sub"
  mag_sub :: Ptr CMag -> Ptr CMag -> Ptr CMag -> IO ()

-- | /mag_sub_lower/ /res/ /x/ /y/ 
-- 
-- Sets /res/ to a lower bound for \(\max(x-y, 0)\).
foreign import ccall "mag.h mag_sub_lower"
  mag_sub_lower :: Ptr CMag -> Ptr CMag -> Ptr CMag -> IO ()

foreign import ccall "mag.h mag_mul_2exp_si"
  mag_mul_2exp_si :: Ptr CMag -> Ptr CMag -> CLong -> IO ()

-- | /mag_mul_2exp_fmpz/ /res/ /x/ /y/ 
-- 
-- Sets /res/ to \(x \cdot 2^y\). This operation is exact.
foreign import ccall "mag.h mag_mul_2exp_fmpz"
  mag_mul_2exp_fmpz :: Ptr CMag -> Ptr CMag -> Ptr CFmpz -> IO ()

foreign import ccall "mag.h mag_mul"
  mag_mul :: Ptr CMag -> Ptr CMag -> Ptr CMag -> IO ()

foreign import ccall "mag.h mag_mul_ui"
  mag_mul_ui :: Ptr CMag -> Ptr CMag -> CULong -> IO ()

-- | /mag_mul_fmpz/ /res/ /x/ /y/ 
-- 
-- Sets /res/ to an upper bound for \(xy\).
foreign import ccall "mag.h mag_mul_fmpz"
  mag_mul_fmpz :: Ptr CMag -> Ptr CMag -> Ptr CFmpz -> IO ()

foreign import ccall "mag.h mag_mul_lower"
  mag_mul_lower :: Ptr CMag -> Ptr CMag -> Ptr CMag -> IO ()

foreign import ccall "mag.h mag_mul_ui_lower"
  mag_mul_ui_lower :: Ptr CMag -> Ptr CMag -> CULong -> IO ()

-- | /mag_mul_fmpz_lower/ /res/ /x/ /y/ 
-- 
-- Sets /res/ to a lower bound for \(xy\).
foreign import ccall "mag.h mag_mul_fmpz_lower"
  mag_mul_fmpz_lower :: Ptr CMag -> Ptr CMag -> Ptr CFmpz -> IO ()

-- | /mag_addmul/ /z/ /x/ /y/ 
-- 
-- Sets /z/ to an upper bound for \(z + xy\).
foreign import ccall "mag.h mag_addmul"
  mag_addmul :: Ptr CMag -> Ptr CMag -> Ptr CMag -> IO ()

foreign import ccall "mag.h mag_div"
  mag_div :: Ptr CMag -> Ptr CMag -> Ptr CMag -> IO ()

foreign import ccall "mag.h mag_div_ui"
  mag_div_ui :: Ptr CMag -> Ptr CMag -> CULong -> IO ()

-- | /mag_div_fmpz/ /res/ /x/ /y/ 
-- 
-- Sets /res/ to an upper bound for \(x / y\).
foreign import ccall "mag.h mag_div_fmpz"
  mag_div_fmpz :: Ptr CMag -> Ptr CMag -> Ptr CFmpz -> IO ()

-- | /mag_div_lower/ /res/ /x/ /y/ 
-- 
-- Sets /res/ to a lower bound for \(x / y\).
foreign import ccall "mag.h mag_div_lower"
  mag_div_lower :: Ptr CMag -> Ptr CMag -> Ptr CMag -> IO ()

-- | /mag_inv/ /res/ /x/ 
-- 
-- Sets /res/ to an upper bound for \(1 / x\).
foreign import ccall "mag.h mag_inv"
  mag_inv :: Ptr CMag -> Ptr CMag -> IO ()

-- | /mag_inv_lower/ /res/ /x/ 
-- 
-- Sets /res/ to a lower bound for \(1 / x\).
foreign import ccall "mag.h mag_inv_lower"
  mag_inv_lower :: Ptr CMag -> Ptr CMag -> IO ()

-- Fast, unsafe arithmetic -----------------------------------------------------

-- The following methods assume that all inputs are finite and that all
-- exponents (in all inputs as well as the final result) fit as /fmpz/
-- inline values. They also assume that the output variables do not have
-- promoted exponents, as they will be overwritten directly (thus leaking
-- memory).
--
-- | /mag_fast_init_set/ /x/ /y/ 
-- 
-- Initialises /x/ and sets it to the value of /y/.
foreign import ccall "mag.h mag_fast_init_set"
  mag_fast_init_set :: Ptr CMag -> Ptr CMag -> IO ()

-- | /mag_fast_zero/ /res/ 
-- 
-- Sets /res/ to zero.
foreign import ccall "mag.h mag_fast_zero"
  mag_fast_zero :: Ptr CMag -> IO ()

-- | /mag_fast_is_zero/ /x/ 
-- 
-- Returns nonzero iff /x/ to zero.
foreign import ccall "mag.h mag_fast_is_zero"
  mag_fast_is_zero :: Ptr CMag -> IO CInt

-- | /mag_fast_mul/ /res/ /x/ /y/ 
-- 
-- Sets /res/ to an upper bound for \(xy\).
foreign import ccall "mag.h mag_fast_mul"
  mag_fast_mul :: Ptr CMag -> Ptr CMag -> Ptr CMag -> IO ()

-- | /mag_fast_addmul/ /z/ /x/ /y/ 
-- 
-- Sets /z/ to an upper bound for \(z + xy\).
foreign import ccall "mag.h mag_fast_addmul"
  mag_fast_addmul :: Ptr CMag -> Ptr CMag -> Ptr CMag -> IO ()

-- | /mag_fast_add_2exp_si/ /res/ /x/ /e/ 
-- 
-- Sets /res/ to an upper bound for \(x + 2^e\).
foreign import ccall "mag.h mag_fast_add_2exp_si"
  mag_fast_add_2exp_si :: Ptr CMag -> Ptr CMag -> CLong -> IO ()

-- | /mag_fast_mul_2exp_si/ /res/ /x/ /e/ 
-- 
-- Sets /res/ to an upper bound for \(x 2^e\).
foreign import ccall "mag.h mag_fast_mul_2exp_si"
  mag_fast_mul_2exp_si :: Ptr CMag -> Ptr CMag -> CLong -> IO ()

-- Powers and logarithms -------------------------------------------------------

foreign import ccall "mag.h mag_pow_ui"
  mag_pow_ui :: Ptr CMag -> Ptr CMag -> CULong -> IO ()

-- | /mag_pow_fmpz/ /res/ /x/ /e/ 
-- 
-- Sets /res/ to an upper bound for \(x^e\).
foreign import ccall "mag.h mag_pow_fmpz"
  mag_pow_fmpz :: Ptr CMag -> Ptr CMag -> Ptr CFmpz -> IO ()

foreign import ccall "mag.h mag_pow_ui_lower"
  mag_pow_ui_lower :: Ptr CMag -> Ptr CMag -> CULong -> IO ()

-- | /mag_pow_fmpz_lower/ /res/ /x/ /e/ 
-- 
-- Sets /res/ to a lower bound for \(x^e\).
foreign import ccall "mag.h mag_pow_fmpz_lower"
  mag_pow_fmpz_lower :: Ptr CMag -> Ptr CMag -> Ptr CFmpz -> IO ()

-- | /mag_sqrt/ /res/ /x/ 
-- 
-- Sets /res/ to an upper bound for \(\sqrt{x}\).
foreign import ccall "mag.h mag_sqrt"
  mag_sqrt :: Ptr CMag -> Ptr CMag -> IO ()

-- | /mag_sqrt_lower/ /res/ /x/ 
-- 
-- Sets /res/ to a lower bound for \(\sqrt{x}\).
foreign import ccall "mag.h mag_sqrt_lower"
  mag_sqrt_lower :: Ptr CMag -> Ptr CMag -> IO ()

-- | /mag_rsqrt/ /res/ /x/ 
-- 
-- Sets /res/ to an upper bound for \(1/\sqrt{x}\).
foreign import ccall "mag.h mag_rsqrt"
  mag_rsqrt :: Ptr CMag -> Ptr CMag -> IO ()

-- | /mag_rsqrt_lower/ /res/ /x/ 
-- 
-- Sets /res/ to an lower bound for \(1/\sqrt{x}\).
foreign import ccall "mag.h mag_rsqrt_lower"
  mag_rsqrt_lower :: Ptr CMag -> Ptr CMag -> IO ()

-- | /mag_hypot/ /res/ /x/ /y/ 
-- 
-- Sets /res/ to an upper bound for \(\sqrt{x^2 + y^2}\).
foreign import ccall "mag.h mag_hypot"
  mag_hypot :: Ptr CMag -> Ptr CMag -> Ptr CMag -> IO ()

-- | /mag_root/ /res/ /x/ /n/ 
-- 
-- Sets /res/ to an upper bound for \(x^{1/n}\).
foreign import ccall "mag.h mag_root"
  mag_root :: Ptr CMag -> Ptr CMag -> CULong -> IO ()

-- | /mag_log/ /res/ /x/ 
-- 
-- Sets /res/ to an upper bound for \(\log(\max(1,x))\).
foreign import ccall "mag.h mag_log"
  mag_log :: Ptr CMag -> Ptr CMag -> IO ()

-- | /mag_log_lower/ /res/ /x/ 
-- 
-- Sets /res/ to a lower bound for \(\log(\max(1,x))\).
foreign import ccall "mag.h mag_log_lower"
  mag_log_lower :: Ptr CMag -> Ptr CMag -> IO ()

-- | /mag_neg_log/ /res/ /x/ 
-- 
-- Sets /res/ to an upper bound for \(-\log(\min(1,x))\), i.e. an upper
-- bound for \(|\log(x)|\) for \(x \le 1\).
foreign import ccall "mag.h mag_neg_log"
  mag_neg_log :: Ptr CMag -> Ptr CMag -> IO ()

-- | /mag_neg_log_lower/ /res/ /x/ 
-- 
-- Sets /res/ to a lower bound for \(-\log(\min(1,x))\), i.e. a lower bound
-- for \(|\log(x)|\) for \(x \le 1\).
foreign import ccall "mag.h mag_neg_log_lower"
  mag_neg_log_lower :: Ptr CMag -> Ptr CMag -> IO ()

-- | /mag_log_ui/ /res/ /n/ 
-- 
-- Sets /res/ to an upper bound for \(\log(n)\).
foreign import ccall "mag.h mag_log_ui"
  mag_log_ui :: Ptr CMag -> CULong -> IO ()

-- | /mag_log1p/ /res/ /x/ 
-- 
-- Sets /res/ to an upper bound for \(\log(1+x)\). The bound is computed
-- accurately for small /x/.
foreign import ccall "mag.h mag_log1p"
  mag_log1p :: Ptr CMag -> Ptr CMag -> IO ()

-- | /mag_exp/ /res/ /x/ 
-- 
-- Sets /res/ to an upper bound for \(\exp(x)\).
foreign import ccall "mag.h mag_exp"
  mag_exp :: Ptr CMag -> Ptr CMag -> IO ()

-- | /mag_exp_lower/ /res/ /x/ 
-- 
-- Sets /res/ to a lower bound for \(\exp(x)\).
foreign import ccall "mag.h mag_exp_lower"
  mag_exp_lower :: Ptr CMag -> Ptr CMag -> IO ()

-- | /mag_expinv/ /res/ /x/ 
-- 
-- Sets /res/ to an upper bound for \(\exp(-x)\).
foreign import ccall "mag.h mag_expinv"
  mag_expinv :: Ptr CMag -> Ptr CMag -> IO ()

-- | /mag_expinv_lower/ /res/ /x/ 
-- 
-- Sets /res/ to a lower bound for \(\exp(-x)\).
foreign import ccall "mag.h mag_expinv_lower"
  mag_expinv_lower :: Ptr CMag -> Ptr CMag -> IO ()

-- | /mag_expm1/ /res/ /x/ 
-- 
-- Sets /res/ to an upper bound for \(\exp(x) - 1\). The bound is computed
-- accurately for small /x/.
foreign import ccall "mag.h mag_expm1"
  mag_expm1 :: Ptr CMag -> Ptr CMag -> IO ()

-- | /mag_exp_tail/ /res/ /x/ /N/ 
-- 
-- Sets /res/ to an upper bound for \(\sum_{k=N}^{\infty} x^k / k!\).
foreign import ccall "mag.h mag_exp_tail"
  mag_exp_tail :: Ptr CMag -> Ptr CMag -> CULong -> IO ()

-- | /mag_binpow_uiui/ /res/ /m/ /n/ 
-- 
-- Sets /res/ to an upper bound for \((1 + 1/m)^n\).
foreign import ccall "mag.h mag_binpow_uiui"
  mag_binpow_uiui :: Ptr CMag -> CULong -> CULong -> IO ()

-- | /mag_geom_series/ /res/ /x/ /N/ 
-- 
-- Sets /res/ to an upper bound for \(\sum_{k=N}^{\infty} x^k\).
foreign import ccall "mag.h mag_geom_series"
  mag_geom_series :: Ptr CMag -> Ptr CMag -> CULong -> IO ()

-- Special functions -----------------------------------------------------------

foreign import ccall "mag.h mag_const_pi"
  mag_const_pi :: Ptr CMag -> IO ()

-- | /mag_const_pi_lower/ /res/ 
-- 
-- Sets /res/ to an upper (respectively lower) bound for \(\pi\).
foreign import ccall "mag.h mag_const_pi_lower"
  mag_const_pi_lower :: Ptr CMag -> IO ()

foreign import ccall "mag.h mag_atan"
  mag_atan :: Ptr CMag -> Ptr CMag -> IO ()

-- | /mag_atan_lower/ /res/ /x/ 
-- 
-- Sets /res/ to an upper (respectively lower) bound for
-- \(\operatorname{atan}(x)\).
foreign import ccall "mag.h mag_atan_lower"
  mag_atan_lower :: Ptr CMag -> Ptr CMag -> IO ()

foreign import ccall "mag.h mag_cosh"
  mag_cosh :: Ptr CMag -> Ptr CMag -> IO ()

foreign import ccall "mag.h mag_cosh_lower"
  mag_cosh_lower :: Ptr CMag -> Ptr CMag -> IO ()

foreign import ccall "mag.h mag_sinh"
  mag_sinh :: Ptr CMag -> Ptr CMag -> IO ()

-- | /mag_sinh_lower/ /res/ /x/ 
-- 
-- Sets /res/ to an upper or lower bound for \(\cosh(x)\) or \(\sinh(x)\).
foreign import ccall "mag.h mag_sinh_lower"
  mag_sinh_lower :: Ptr CMag -> Ptr CMag -> IO ()

-- | /mag_fac_ui/ /res/ /n/ 
-- 
-- Sets /res/ to an upper bound for \(n!\).
foreign import ccall "mag.h mag_fac_ui"
  mag_fac_ui :: Ptr CMag -> CULong -> IO ()

-- | /mag_rfac_ui/ /res/ /n/ 
-- 
-- Sets /res/ to an upper bound for \(1/n!\).
foreign import ccall "mag.h mag_rfac_ui"
  mag_rfac_ui :: Ptr CMag -> CULong -> IO ()

-- | /mag_bin_uiui/ /res/ /n/ /k/ 
-- 
-- Sets /res/ to an upper bound for the binomial coefficient
-- \({n \choose k}\).
foreign import ccall "mag.h mag_bin_uiui"
  mag_bin_uiui :: Ptr CMag -> CULong -> CULong -> IO ()

-- | /mag_bernoulli_div_fac_ui/ /res/ /n/ 
-- 
-- Sets /res/ to an upper bound for \(|B_n| / n!\) where \(B_n\) denotes a
-- Bernoulli number.
foreign import ccall "mag.h mag_bernoulli_div_fac_ui"
  mag_bernoulli_div_fac_ui :: Ptr CMag -> CULong -> IO ()

-- | /mag_polylog_tail/ /res/ /z/ /s/ /d/ /N/ 
-- 
-- Sets /res/ to an upper bound for
-- 
-- \[`\]
-- \[\sum_{k=N}^{\infty} \frac{z^k \log^d(k)}{k^s}.\]
-- 
-- The bounding strategy is described in @algorithms_polylogarithms@. Note:
-- in applications where \(s\) in this formula may be real or complex, the
-- user can simply substitute any convenient integer \(s'\) such that
-- \(s' \le \operatorname{Re}(s)\).
foreign import ccall "mag.h mag_polylog_tail"
  mag_polylog_tail :: Ptr CMag -> Ptr CMag -> CLong -> CULong -> CULong -> IO ()

-- | /mag_hurwitz_zeta_uiui/ /res/ /s/ /a/ 
-- 
-- Sets /res/ to an upper bound for
-- \(\zeta(s,a) = \sum_{k=0}^{\infty} (k+a)^{-s}\). We use the formula
-- 
-- \[`\]
-- \[\zeta(s,a) \le \frac{1}{a^s} + \frac{1}{(s-1) a^{s-1}}\]
-- 
-- which is obtained by estimating the sum by an integral. If \(s \le 1\)
-- or \(a = 0\), the bound is infinite.
foreign import ccall "mag.h mag_hurwitz_zeta_uiui"
  mag_hurwitz_zeta_uiui :: Ptr CMag -> CULong -> CULong -> IO ()

