
module Data.Number.Flint.Arb.Arf.FFI (
  -- * Arbitrary-precision floating-point numbers
    Arf (..)
  , CArf
  , newArf
  , withArf
  , withNewArf
  -- * Memory management
  , arf_init
  , arf_clear
  , arf_allocated_bytes
  -- * Special values
  , arf_zero
  , arf_one
  , arf_pos_inf
  , arf_neg_inf
  , arf_nan
  , arf_is_zero
  , arf_is_one
  , arf_is_pos_inf
  , arf_is_neg_inf
  , arf_is_nan
  , arf_is_inf
  , arf_is_normal
  , arf_is_special
  , arf_is_finite
  -- * Assignment, rounding and conversions
  , ArfRnd (..)
  -- | Specifies that the result of an operation should be rounded to
  -- the nearest representable number in the direction towards zero.
  , arf_rnd_up
  -- | Specifies that the result of an operation should be rounded to
  -- the nearest representable number in the direction away from zero.
  , arf_rnd_down
  -- | Specifies that the result of an operation should be rounded to
  -- the nearest representable number in the direction towards minus
  -- infinity.
  , arf_rnd_floor
  -- | Specifies that the result of an operation should be rounded to
  -- the nearest representable number in the direction towards plus
  -- infinity.
  , arf_rnd_ceil
  -- | Specifies that the result of an operation should be rounded to
  -- the nearest representable number, rounding to even if there is a
  -- tie between two values.
  , arf_rnd_near
  -- | If passed as the precision parameter to a function, indicates
  -- that no rounding is to be performed. __Warning__: use of this value
  -- is unsafe in general. It must only be passed as input under the
  -- following two conditions:
  -- 
  --  * The operation in question can inherently be viewed as an exact operation
  --    in \(\mathbb{Z}[\tfrac{1}{2}]\) for all possible inputs, provided that
  --    the precision is large enough. Examples include addition,
  --    multiplication, conversion from integer types to arbitrary-precision
  --    floating-point types, and evaluation of some integer-valued functions.
  --
  --  * The exact result of the operation will certainly fit in memory.
  --    Note that, for example, adding two numbers whose exponents are far
  --    apart can easily produce an exact result that is far too large to
  --    store in memory.
  --
  --  The typical use case is to work with small integer values, double
  --  precision constants, and the like. It is also useful when writing
  --  test code. If in doubt, simply try with some convenient high precision
  --  instead of using this special value, and check that the result is exact.
  , arf_prec_exact
  , arf_set
  , arf_set_mpz
  , arf_set_fmpz
  , arf_set_ui
  , arf_set_si
  , arf_set_mpfr
  , arf_set_d
  , arf_swap
  , arf_init_set_ui
  , arf_init_set_si
  , arf_set_round
  , arf_set_round_si
  , arf_set_round_ui
  , arf_set_round_mpz
  , arf_set_round_fmpz
  , arf_set_si_2exp_si
  , arf_set_ui_2exp_si
  , arf_set_fmpz_2exp
  , arf_set_round_fmpz_2exp
  , arf_get_fmpz_2exp
  , arf_frexp
  , arf_get_d
  , arf_get_mpfr
  , arf_get_fmpz
  , arf_get_si
  , arf_get_fmpz_fixed_fmpz
  , arf_get_fmpz_fixed_si
  , arf_floor
  , arf_ceil
  , arf_get_fmpq
  -- * Comparisons and bounds
  , arf_equal
  , arf_equal_si
  , arf_equal_ui
  , arf_equal_d
  , arf_cmp
  , arf_cmp_si
  , arf_cmp_ui
  , arf_cmp_d
  , arf_cmpabs
  , arf_cmpabs_ui
  , arf_cmpabs_d
  , arf_cmpabs_mag
  , arf_cmp_2exp_si
  , arf_cmpabs_2exp_si
  , arf_sgn
  , arf_min
  , arf_max
  , arf_bits
  , arf_is_int
  , arf_is_int_2exp_si
  , arf_abs_bound_lt_2exp_fmpz
  , arf_abs_bound_le_2exp_fmpz
  , arf_abs_bound_lt_2exp_si
  -- * Magnitude functions
  , arf_get_mag
  , arf_get_mag_lower
  , arf_set_mag
  , mag_init_set_arf
  , mag_fast_init_set_arf
  , arf_mag_set_ulp
  , arf_mag_add_ulp
  , arf_mag_fast_add_ulp
  -- * Shallow assignment
  , arf_init_set_shallow
  , arf_init_set_mag_shallow
  , arf_init_neg_shallow
  , arf_init_neg_mag_shallow
  -- * Random number generation
  , arf_randtest
  , arf_randtest_not_zero
  , arf_randtest_special
  , arf_urandom
  -- * Input and output
  , arf_debug
  , arf_print
  , arf_printd
  , arf_get_str
  , arf_fprint
  , arf_fprintd
  , arf_dump_str
  , arf_load_str
  , arf_dump_file
  , arf_load_file
  -- * Addition and multiplication
  , arf_abs
  , arf_neg
  , arf_neg_round
  , arf_add
  , arf_add_si
  , arf_add_ui
  , arf_add_fmpz
  , arf_add_fmpz_2exp
  , arf_sub
  , arf_sub_si
  , arf_sub_ui
  , arf_sub_fmpz
  , arf_mul_2exp_si
  , arf_mul_2exp_fmpz
  , arf_mul
  , arf_mul_ui
  , arf_mul_si
  , arf_mul_mpz
  , arf_mul_fmpz
  , arf_addmul
  , arf_addmul_ui
  , arf_addmul_si
  , arf_addmul_mpz
  , arf_addmul_fmpz
  , arf_submul
  , arf_submul_ui
  , arf_submul_si
  , arf_submul_mpz
  , arf_submul_fmpz
  , arf_fma
  , arf_sosq
  -- * Summation
  , arf_sum
  -- * Dot products
  , arf_approx_dot
  -- * Division
  , arf_div
  , arf_div_ui
  , arf_ui_div
  , arf_div_si
  , arf_si_div
  , arf_div_fmpz
  , arf_fmpz_div
  , arf_fmpz_div_fmpz
  -- * Square roots
  , arf_sqrt
  , arf_sqrt_ui
  , arf_sqrt_fmpz
  , arf_rsqrt
  , arf_root
  -- * Complex arithmetic
  , arf_complex_mul
  , arf_complex_mul_fallback
  , arf_complex_sqr
  -- * Low-level methods
  , _arf_get_integer_mpn
  , _arf_set_mpn_fixed
  , _arf_set_round_ui
  , _arf_set_round_uiui
  , _arf_set_round_mpn
) where 

-- Arbitrary-precision floating-point numbers ----------------------------------

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.Storable
import Foreign.Marshal.Alloc
import Foreign.C.Types
import Foreign.C.String

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpq

import Data.Number.Flint.Arb.Types

#define ARF_INLINES_C
#include <flint/arf.h>

-- arf_t -----------------------------------------------------------------------

-- | Createst a new `CArf` structure encapsulated in `Arf`.
newArf = do
  p <- mallocForeignPtr
  withForeignPtr p arf_init
  addForeignPtrFinalizer p_arf_clear p
  return $ Arf p
  
-- | Access to the C pointer in `Arf` structure.
{-# INLINE withArf #-}
withArf (Arf p) f = withForeignPtr p $ fmap (Arf p,) . f

withNewArf f = do
  x <- newArf
  withArf x $ \x -> f x
  
-- Memory management -----------------------------------------------------------

-- | /arf_init/ /x/ 
--
-- Initializes the variable /x/ for use. Its value is set to zero.
foreign import ccall "arf.h arf_init"
  arf_init :: Ptr CArf -> IO ()

-- | /arf_clear/ /x/ 
--
-- Clears the variable /x/, freeing or recycling its allocated memory.
foreign import ccall "arf.h arf_clear"
  arf_clear :: Ptr CArf -> IO ()

foreign import ccall "arf.h &arf_clear"
  p_arf_clear :: FunPtr (Ptr CArf -> IO ())

-- | /arf_allocated_bytes/ /x/ 
--
-- Returns the total number of bytes heap-allocated internally by this
-- object. The count excludes the size of the structure itself. Add
-- @sizeof(arf_struct)@ to get the size of the object as a whole.
foreign import ccall "arf.h arf_allocated_bytes"
  arf_allocated_bytes :: Ptr CArf -> IO CLong

-- Special values --------------------------------------------------------------

-- | /arf_zero/ /res/ 
--
foreign import ccall "arf.h arf_zero"
  arf_zero :: Ptr CArf -> IO ()

-- | /arf_one/ /res/ 
--
foreign import ccall "arf.h arf_one"
  arf_one :: Ptr CArf -> IO ()

-- | /arf_pos_inf/ /res/ 
--
foreign import ccall "arf.h arf_pos_inf"
  arf_pos_inf :: Ptr CArf -> IO ()

-- | /arf_neg_inf/ /res/ 
--
foreign import ccall "arf.h arf_neg_inf"
  arf_neg_inf :: Ptr CArf -> IO ()

-- | /arf_nan/ /res/ 
--
-- Sets /res/ respectively to 0, 1, \(+\infty\), \(-\infty\), NaN.
foreign import ccall "arf.h arf_nan"
  arf_nan :: Ptr CArf -> IO ()

-- | /arf_is_zero/ /x/ 
--
foreign import ccall "arf.h arf_is_zero"
  arf_is_zero :: Ptr CArf -> IO CInt

-- | /arf_is_one/ /x/ 
--
foreign import ccall "arf.h arf_is_one"
  arf_is_one :: Ptr CArf -> IO CInt

-- | /arf_is_pos_inf/ /x/ 
--
foreign import ccall "arf.h arf_is_pos_inf"
  arf_is_pos_inf :: Ptr CArf -> IO CInt

-- | /arf_is_neg_inf/ /x/ 
--
foreign import ccall "arf.h arf_is_neg_inf"
  arf_is_neg_inf :: Ptr CArf -> IO CInt

-- | /arf_is_nan/ /x/ 
--
-- Returns nonzero iff /x/ respectively equals 0, 1, \(+\infty\),
-- \(-\infty\), NaN.
foreign import ccall "arf.h arf_is_nan"
  arf_is_nan :: Ptr CArf -> IO CInt

-- | /arf_is_inf/ /x/ 
--
-- Returns nonzero iff /x/ equals either \(+\infty\) or \(-\infty\).
foreign import ccall "arf.h arf_is_inf"
  arf_is_inf :: Ptr CArf -> IO CInt

-- | /arf_is_normal/ /x/ 
--
-- Returns nonzero iff /x/ is a finite, nonzero floating-point value, i.e.
-- not one of the special values 0, \(+\infty\), \(-\infty\), NaN.
foreign import ccall "arf.h arf_is_normal"
  arf_is_normal :: Ptr CArf -> IO CInt

-- | /arf_is_special/ /x/ 
--
-- Returns nonzero iff /x/ is one of the special values 0, \(+\infty\),
-- \(-\infty\), NaN, i.e. not a finite, nonzero floating-point value.
foreign import ccall "arf.h arf_is_special"
  arf_is_special :: Ptr CArf -> IO CInt

-- | /arf_is_finite/ /x/ 
--
-- Returns nonzero iff /x/ is a finite floating-point value, i.e. not one
-- of the values \(+\infty\), \(-\infty\), NaN. (Note that this is not
-- equivalent to the negation of @arf_is_inf@.)
foreign import ccall "arf.h arf_is_finite"
  arf_is_finite :: Ptr CArf -> IO CInt

-- Assignment, rounding and conversions ----------------------------------------

-- | /arf_set/ /res/ /x/ 
--
foreign import ccall "arf.h arf_set"
  arf_set :: Ptr CArf -> Ptr CArf -> IO ()

-- | /arf_set_mpz/ /res/ /x/ 
--
foreign import ccall "arf.h arf_set_mpz"
  arf_set_mpz :: Ptr CArf -> Ptr CMpz -> IO ()

-- | /arf_set_fmpz/ /res/ /x/ 
--
foreign import ccall "arf.h arf_set_fmpz"
  arf_set_fmpz :: Ptr CArf -> Ptr CFmpz -> IO ()

-- | /arf_set_ui/ /res/ /x/ 
--
foreign import ccall "arf.h arf_set_ui"
  arf_set_ui :: Ptr CArf -> CULong -> IO ()

-- | /arf_set_si/ /res/ /x/ 
--
foreign import ccall "arf.h arf_set_si"
  arf_set_si :: Ptr CArf -> CLong -> IO ()

-- | /arf_set_mpfr/ /res/ /x/ 
--
foreign import ccall "arf.h arf_set_mpfr"
  arf_set_mpfr :: Ptr CArf -> Ptr CMpfr -> IO ()

-- | /arf_set_d/ /res/ /x/ 
--
-- Sets /res/ to the exact value of /x/.
foreign import ccall "arf.h arf_set_d"
  arf_set_d :: Ptr CArf -> CDouble -> IO ()

-- | /arf_swap/ /x/ /y/ 
--
-- Swaps /x/ and /y/ efficiently.
foreign import ccall "arf.h arf_swap"
  arf_swap :: Ptr CArf -> Ptr CArf -> IO ()

-- | /arf_init_set_ui/ /res/ /x/ 
--
foreign import ccall "arf.h arf_init_set_ui"
  arf_init_set_ui :: Ptr CArf -> CULong -> IO ()

-- | /arf_init_set_si/ /res/ /x/ 
--
-- Initializes /res/ and sets it to /x/ in a single operation.
foreign import ccall "arf.h arf_init_set_si"
  arf_init_set_si :: Ptr CArf -> CLong -> IO ()

-- | /arf_set_round/ /res/ /x/ /prec/ /rnd/ 
--
foreign import ccall "arf.h arf_set_round"
  arf_set_round :: Ptr CArf -> Ptr CArf -> CLong -> ArfRnd -> IO CInt

-- | /arf_set_round_si/ /res/ /x/ /prec/ /rnd/ 
--
foreign import ccall "arf.h arf_set_round_si"
  arf_set_round_si :: Ptr CArf -> CLong -> CLong -> ArfRnd -> IO CInt

-- | /arf_set_round_ui/ /res/ /x/ /prec/ /rnd/ 
--
foreign import ccall "arf.h arf_set_round_ui"
  arf_set_round_ui :: Ptr CArf -> CULong -> CLong -> ArfRnd -> IO CInt

-- | /arf_set_round_mpz/ /res/ /x/ /prec/ /rnd/ 
--
foreign import ccall "arf.h arf_set_round_mpz"
  arf_set_round_mpz :: Ptr CArf -> Ptr CMpz -> CLong -> ArfRnd -> IO CInt

-- | /arf_set_round_fmpz/ /res/ /x/ /prec/ /rnd/ 
--
-- Sets /res/ to /x/, rounded to /prec/ bits in the direction specified by
-- /rnd/.
foreign import ccall "arf.h arf_set_round_fmpz"
  arf_set_round_fmpz :: Ptr CArf -> Ptr CFmpz -> CLong -> ArfRnd -> IO CInt

-- | /arf_set_si_2exp_si/ /res/ /m/ /e/ 
--
foreign import ccall "arf.h arf_set_si_2exp_si"
  arf_set_si_2exp_si :: Ptr CArf -> CLong -> CLong -> IO ()

-- | /arf_set_ui_2exp_si/ /res/ /m/ /e/ 
--
foreign import ccall "arf.h arf_set_ui_2exp_si"
  arf_set_ui_2exp_si :: Ptr CArf -> CULong -> CLong -> IO ()

-- | /arf_set_fmpz_2exp/ /res/ /m/ /e/ 
--
-- Sets /res/ to \(m \cdot 2^e\).
foreign import ccall "arf.h arf_set_fmpz_2exp"
  arf_set_fmpz_2exp :: Ptr CArf -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /arf_set_round_fmpz_2exp/ /res/ /x/ /e/ /prec/ /rnd/ 
--
-- Sets /res/ to \(x \cdot 2^e\), rounded to /prec/ bits in the direction
-- specified by /rnd/.
foreign import ccall "arf.h arf_set_round_fmpz_2exp"
  arf_set_round_fmpz_2exp :: Ptr CArf -> Ptr CFmpz -> Ptr CFmpz -> CLong -> ArfRnd -> IO CInt

-- | /arf_get_fmpz_2exp/ /m/ /e/ /x/ 
--
-- Sets /m/ and /e/ to the unique integers such that \(x = m \cdot 2^e\)
-- and /m/ is odd, provided that /x/ is a nonzero finite fraction. If /x/
-- is zero, both /m/ and /e/ are set to zero. If /x/ is infinite or NaN,
-- the result is undefined.
foreign import ccall "arf.h arf_get_fmpz_2exp"
  arf_get_fmpz_2exp :: Ptr CFmpz -> Ptr CFmpz -> Ptr CArf -> IO ()

-- | /arf_frexp/ /m/ /e/ /x/ 
--
-- Writes /x/ as \(m \cdot 2^e\), where \(0.5 \le |m| < 1\) if /x/ is a
-- normal value. If /x/ is a special value, copies this to /m/ and sets /e/
-- to zero. Note: for the inverse operation (/ldexp/), use
-- @arf_mul_2exp_fmpz@.
foreign import ccall "arf.h arf_frexp"
  arf_frexp :: Ptr CArf -> Ptr CFmpz -> Ptr CArf -> IO ()

-- | /arf_get_d/ /x/ /rnd/ 
--
-- Returns /x/ rounded to a double in the direction specified by /rnd/.
-- This method rounds correctly when overflowing or underflowing the double
-- exponent range (this was not the case in an earlier version).
foreign import ccall "arf.h arf_get_d"
  arf_get_d :: Ptr CArf -> ArfRnd -> IO CDouble

-- | /arf_get_mpfr/ /res/ /x/ /rnd/ 
--
-- Sets the MPFR variable /res/ to the value of /x/. If the precision of
-- /x/ is too small to allow /res/ to be represented exactly, it is rounded
-- in the specified MPFR rounding mode. The return value (-1, 0 or 1)
-- indicates the direction of rounding, following the convention of the
-- MPFR library.
-- 
-- If /x/ has an exponent too large or small to fit in the MPFR type, the
-- result overflows to an infinity or underflows to a (signed) zero, and
-- the corresponding MPFR exception flags are set.
foreign import ccall "arf.h arf_get_mpfr"
  arf_get_mpfr :: Ptr CMpfr -> Ptr CArf -> CMpfrRnd -> IO CInt

-- | /arf_get_fmpz/ /res/ /x/ /rnd/ 
--
-- Sets /res/ to /x/ rounded to the nearest integer in the direction
-- specified by /rnd/. If rnd is /ARFRND_NEAR/, rounds to the nearest even
-- integer in case of a tie. Returns inexact (beware: accordingly returns
-- whether /x/ is /not/ an integer).
-- 
-- This method aborts if /x/ is infinite or NaN, or if the exponent of /x/
-- is so large that allocating memory for the result fails.
-- 
-- Warning: this method will allocate a huge amount of memory to store the
-- result if the exponent of /x/ is huge. Memory allocation could succeed
-- even if the required space is far larger than the physical memory
-- available on the machine, resulting in swapping. It is recommended to
-- check that /x/ is within a reasonable range before calling this method.
foreign import ccall "arf.h arf_get_fmpz"
  arf_get_fmpz :: Ptr CFmpz -> Ptr CArf -> ArfRnd -> IO CInt

-- | /arf_get_si/ /x/ /rnd/ 
--
-- Returns /x/ rounded to the nearest integer in the direction specified by
-- /rnd/. If /rnd/ is /ARFRND_NEAR/, rounds to the nearest even integer in
-- case of a tie. Aborts if /x/ is infinite, NaN, or the value is too large
-- to fit in a slong.
foreign import ccall "arf.h arf_get_si"
  arf_get_si :: Ptr CArf -> ArfRnd -> IO CLong

-- | /arf_get_fmpz_fixed_fmpz/ /res/ /x/ /e/ 
--
foreign import ccall "arf.h arf_get_fmpz_fixed_fmpz"
  arf_get_fmpz_fixed_fmpz :: Ptr CFmpz -> Ptr CArf -> Ptr CFmpz -> IO CInt

-- | /arf_get_fmpz_fixed_si/ /res/ /x/ /e/ 
--
-- Converts /x/ to a mantissa with predetermined exponent, i.e. sets /res/
-- to an integer /y/ such that \(y \times 2^e \approx x\), truncating if
-- necessary. Returns 0 if exact and 1 if truncation occurred.
-- 
-- The warnings for @arf_get_fmpz@ apply.
foreign import ccall "arf.h arf_get_fmpz_fixed_si"
  arf_get_fmpz_fixed_si :: Ptr CFmpz -> Ptr CArf -> CLong -> IO CInt

-- | /arf_floor/ /res/ /x/ 
--
foreign import ccall "arf.h arf_floor"
  arf_floor :: Ptr CArf -> Ptr CArf -> IO ()

-- | /arf_ceil/ /res/ /x/ 
--
-- Sets /res/ to \(\lfloor x \rfloor\) and \(\lceil x \rceil\)
-- respectively. The result is always represented exactly, requiring no
-- more bits to store than the input. To round the result to a
-- floating-point number with a lower precision, call @arf_set_round@
-- afterwards.
foreign import ccall "arf.h arf_ceil"
  arf_ceil :: Ptr CArf -> Ptr CArf -> IO ()

-- | /arf_get_fmpq/ /res/ /x/ 
--
-- Set /res/ to the exact rational value of /x/. This method aborts if /x/
-- is infinite or NaN, or if the exponent of /x/ is so large that
-- allocating memory for the result fails.
foreign import ccall "arf.h arf_get_fmpq"
  arf_get_fmpq :: Ptr CFmpq -> Ptr CArf -> IO ()

-- Comparisons and bounds ------------------------------------------------------

-- | /arf_equal/ /x/ /y/ 
foreign import ccall "arf.h arf_equal"
  arf_equal :: Ptr CArf -> Ptr CArf -> IO CInt
-- | /arf_equal_si/ /x/ /y/ 
foreign import ccall "arf.h arf_equal_si"
  arf_equal_si :: Ptr CArf -> CLong -> IO CInt
-- | /arf_equal_ui/ /x/ /y/ 
foreign import ccall "arf.h arf_equal_ui"
  arf_equal_ui :: Ptr CArf -> CULong -> IO CInt
-- | /arf_equal_d/ /x/ /y/ 
--
-- Returns nonzero iff /x/ and /y/ are exactly equal. NaN is not treated
-- specially, i.e. NaN compares as equal to itself.
-- 
-- For comparison with a /double/, the values -0 and +0 are both treated as
-- zero, and all NaN values are treated as identical.
foreign import ccall "arf.h arf_equal_d"
  arf_equal_d :: Ptr CArf -> CDouble -> IO CInt

-- | /arf_cmp/ /x/ /y/ 
--
foreign import ccall "arf.h arf_cmp"
  arf_cmp :: Ptr CArf -> Ptr CArf -> IO CInt

-- | /arf_cmp_si/ /x/ /y/ 
--
foreign import ccall "arf.h arf_cmp_si"
  arf_cmp_si :: Ptr CArf -> CLong -> IO CInt

-- | /arf_cmp_ui/ /x/ /y/ 
--
foreign import ccall "arf.h arf_cmp_ui"
  arf_cmp_ui :: Ptr CArf -> CULong -> IO CInt

-- | /arf_cmp_d/ /x/ /y/ 
--
-- Returns negative, zero, or positive, depending on whether /x/ is
-- respectively smaller, equal, or greater compared to /y/. Comparison with
-- NaN is undefined.
foreign import ccall "arf.h arf_cmp_d"
  arf_cmp_d :: Ptr CArf -> CDouble -> IO CInt

-- | /arf_cmpabs/ /x/ /y/ 
--
foreign import ccall "arf.h arf_cmpabs"
  arf_cmpabs :: Ptr CArf -> Ptr CArf -> IO CInt

-- | /arf_cmpabs_ui/ /x/ /y/ 
--
foreign import ccall "arf.h arf_cmpabs_ui"
  arf_cmpabs_ui :: Ptr CArf -> CULong -> IO CInt

-- | /arf_cmpabs_d/ /x/ /y/ 
--
foreign import ccall "arf.h arf_cmpabs_d"
  arf_cmpabs_d :: Ptr CArf -> CDouble -> IO CInt

-- | /arf_cmpabs_mag/ /x/ /y/ 
--
-- Compares the absolute values of /x/ and /y/.
foreign import ccall "arf.h arf_cmpabs_mag"
  arf_cmpabs_mag :: Ptr CArf -> Ptr CMag -> IO CInt

-- | /arf_cmp_2exp_si/ /x/ /e/ 
--
foreign import ccall "arf.h arf_cmp_2exp_si"
  arf_cmp_2exp_si :: Ptr CArf -> CLong -> IO CInt

-- | /arf_cmpabs_2exp_si/ /x/ /e/ 
--
-- Compares /x/ (respectively its absolute value) with \(2^e\).
foreign import ccall "arf.h arf_cmpabs_2exp_si"
  arf_cmpabs_2exp_si :: Ptr CArf -> CLong -> IO CInt

-- | /arf_sgn/ /x/ 
--
-- Returns \(-1\), \(0\) or \(+1\) according to the sign of /x/. The sign
-- of NaN is undefined.
foreign import ccall "arf.h arf_sgn"
  arf_sgn :: Ptr CArf -> IO CInt

-- | /arf_min/ /res/ /a/ /b/ 
--
foreign import ccall "arf.h arf_min"
  arf_min :: Ptr CArf -> Ptr CArf -> Ptr CArf -> IO ()

-- | /arf_max/ /res/ /a/ /b/ 
--
-- Sets /res/ respectively to the minimum and the maximum of /a/ and /b/.
foreign import ccall "arf.h arf_max"
  arf_max :: Ptr CArf -> Ptr CArf -> Ptr CArf -> IO ()

-- | /arf_bits/ /x/ 
--
-- Returns the number of bits needed to represent the absolute value of the
-- mantissa of /x/, i.e. the minimum precision sufficient to represent /x/
-- exactly. Returns 0 if /x/ is a special value.
foreign import ccall "arf.h arf_bits"
  arf_bits :: Ptr CArf -> IO CLong

-- | /arf_is_int/ /x/ 
--
-- Returns nonzero iff /x/ is integer-valued.
foreign import ccall "arf.h arf_is_int"
  arf_is_int :: Ptr CArf -> IO CInt

-- | /arf_is_int_2exp_si/ /x/ /e/ 
--
-- Returns nonzero iff /x/ equals \(n 2^e\) for some integer /n/.
foreign import ccall "arf.h arf_is_int_2exp_si"
  arf_is_int_2exp_si :: Ptr CArf -> CLong -> IO CInt

-- | /arf_abs_bound_lt_2exp_fmpz/ /res/ /x/ 
--
-- Sets /res/ to the smallest integer /b/ such that \(|x| < 2^b\). If /x/
-- is zero, infinity or NaN, the result is undefined.
foreign import ccall "arf.h arf_abs_bound_lt_2exp_fmpz"
  arf_abs_bound_lt_2exp_fmpz :: Ptr CFmpz -> Ptr CArf -> IO ()

-- | /arf_abs_bound_le_2exp_fmpz/ /res/ /x/ 
--
-- Sets /res/ to the smallest integer /b/ such that \(|x| \le 2^b\). If /x/
-- is zero, infinity or NaN, the result is undefined.
foreign import ccall "arf.h arf_abs_bound_le_2exp_fmpz"
  arf_abs_bound_le_2exp_fmpz :: Ptr CFmpz -> Ptr CArf -> IO ()

-- | /arf_abs_bound_lt_2exp_si/ /x/ 
--
-- Returns the smallest integer /b/ such that \(|x| < 2^b\), clamping the
-- result to lie between -/ARF_PREC_EXACT/ and /ARF_PREC_EXACT/ inclusive.
-- If /x/ is zero, -/ARF_PREC_EXACT/ is returned, and if /x/ is infinity or
-- NaN, /ARF_PREC_EXACT/ is returned.
foreign import ccall "arf.h arf_abs_bound_lt_2exp_si"
  arf_abs_bound_lt_2exp_si :: Ptr CArf -> IO CLong

-- Magnitude functions ---------------------------------------------------------

-- | /arf_get_mag/ /res/ /x/ 
--
-- Sets /res/ to an upper bound for the absolute value of /x/.
foreign import ccall "arf.h arf_get_mag"
  arf_get_mag :: Ptr CMag -> Ptr CArf -> IO ()

-- | /arf_get_mag_lower/ /res/ /x/ 
--
-- Sets /res/ to a lower bound for the absolute value of /x/.
foreign import ccall "arf.h arf_get_mag_lower"
  arf_get_mag_lower :: Ptr CMag -> Ptr CArf -> IO ()

-- | /arf_set_mag/ /res/ /x/ 
--
-- Sets /res/ to /x/. This operation is exact.
foreign import ccall "arf.h arf_set_mag"
  arf_set_mag :: Ptr CArf -> Ptr CMag -> IO ()

-- | /mag_init_set_arf/ /res/ /x/ 
--
-- Initializes /res/ and sets it to an upper bound for /x/.
foreign import ccall "arf.h mag_init_set_arf"
  mag_init_set_arf :: Ptr CMag -> Ptr CArf -> IO ()

-- | /mag_fast_init_set_arf/ /res/ /x/ 
--
-- Initializes /res/ and sets it to an upper bound for /x/. Assumes that
-- the exponent of /res/ is small (this function is unsafe).
foreign import ccall "arf.h mag_fast_init_set_arf"
  mag_fast_init_set_arf :: Ptr CMag -> Ptr CArf -> IO ()

-- | /arf_mag_set_ulp/ /res/ /x/ /prec/ 
--
-- Sets /res/ to the magnitude of the unit in the last place (ulp) of /x/
-- at precision /prec/.
foreign import ccall "arf.h arf_mag_set_ulp"
  arf_mag_set_ulp :: Ptr CMag -> Ptr CArf -> CLong -> IO ()

-- | /arf_mag_add_ulp/ /res/ /x/ /y/ /prec/ 
--
-- Sets /res/ to an upper bound for the sum of /x/ and the magnitude of the
-- unit in the last place (ulp) of /y/ at precision /prec/.
foreign import ccall "arf.h arf_mag_add_ulp"
  arf_mag_add_ulp :: Ptr CMag -> Ptr CMag -> Ptr CArf -> CLong -> IO ()

-- | /arf_mag_fast_add_ulp/ /res/ /x/ /y/ /prec/ 
--
-- Sets /res/ to an upper bound for the sum of /x/ and the magnitude of the
-- unit in the last place (ulp) of /y/ at precision /prec/. Assumes that
-- all exponents are small.
foreign import ccall "arf.h arf_mag_fast_add_ulp"
  arf_mag_fast_add_ulp :: Ptr CMag -> Ptr CMag -> Ptr CArf -> CLong -> IO ()

-- Shallow assignment ----------------------------------------------------------

-- | /arf_init_set_shallow/ /z/ /x/ 
--
foreign import ccall "arf.h arf_init_set_shallow"
  arf_init_set_shallow :: Ptr CArf -> Ptr CArf -> IO ()

-- | /arf_init_set_mag_shallow/ /z/ /x/ 
--
-- Initializes /z/ to a shallow copy of /x/. A shallow copy just involves
-- copying struct data (no heap allocation is performed).
-- 
-- The target variable /z/ may not be cleared or modified in any way (it
-- can only be used as constant input to functions), and may not be used
-- after /x/ has been cleared. Moreover, after /x/ has been assigned
-- shallowly to /z/, no modification of /x/ is permitted as slong as /z/ is
-- in use.
foreign import ccall "arf.h arf_init_set_mag_shallow"
  arf_init_set_mag_shallow :: Ptr CArf -> Ptr CMag -> IO ()

-- | /arf_init_neg_shallow/ /z/ /x/ 
--
foreign import ccall "arf.h arf_init_neg_shallow"
  arf_init_neg_shallow :: Ptr CArf -> Ptr CArf -> IO ()

-- | /arf_init_neg_mag_shallow/ /z/ /x/ 
--
-- Initializes /z/ shallowly to the negation of /x/.
foreign import ccall "arf.h arf_init_neg_mag_shallow"
  arf_init_neg_mag_shallow :: Ptr CArf -> Ptr CMag -> IO ()

-- Random number generation ----------------------------------------------------

-- | /arf_randtest/ /res/ /state/ /bits/ /mag_bits/ 
--
-- Generates a finite random number whose mantissa has precision at most
-- /bits/ and whose exponent has at most /mag_bits/ bits. The values are
-- distributed non-uniformly: special bit patterns are generated with high
-- probability in order to allow the test code to exercise corner cases.
foreign import ccall "arf.h arf_randtest"
  arf_randtest :: Ptr CArf -> Ptr CFRandState -> CLong -> CLong -> IO ()

-- | /arf_randtest_not_zero/ /res/ /state/ /bits/ /mag_bits/ 
--
-- Identical to @arf_randtest@, except that zero is never produced as an
-- output.
foreign import ccall "arf.h arf_randtest_not_zero"
  arf_randtest_not_zero :: Ptr CArf -> Ptr CFRandState -> CLong -> CLong -> IO ()

-- | /arf_randtest_special/ /res/ /state/ /bits/ /mag_bits/ 
--
-- Identical to @arf_randtest@, except that the output occasionally is set
-- to an infinity or NaN.
foreign import ccall "arf.h arf_randtest_special"
  arf_randtest_special :: Ptr CArf -> Ptr CFRandState -> CLong -> CLong -> IO ()

-- | /arf_urandom/ /res/ /state/ /bits/ /rnd/ 
--
-- Sets /res/ to a uniformly distributed random number in the interval
-- \([0, 1]\). The method uses rounding from integers to floats based on
-- the rounding mode /rnd/.
foreign import ccall "arf.h arf_urandom"
  arf_urandom :: Ptr CArf -> Ptr CFRandState -> CLong -> ArfRnd -> IO ()

-- Input and output ------------------------------------------------------------

-- | /arf_debug/ /x/ 
--
-- Prints information about the internal representation of /x/.
foreign import ccall "arf.h arf_debug"
  arf_debug :: Ptr CArf -> IO ()

-- | /arf_print/ /x/ 
--
-- Prints /x/ as an integer mantissa and exponent.
foreign import ccall "arf.h arf_print"
  arf_print :: Ptr CArf -> IO ()

-- | /arf_printd/ /x/ /d/ 
--
-- Prints /x/ as a decimal floating-point number, rounding to /d/ digits.
-- Rounding is faithful (at most 1 ulp error).
arf_printd :: Ptr CArf -> CLong -> IO ()
arf_printd x digits = do
  cs <- arf_get_str x digits
  s <- peekCString cs
  free cs
  putStr s
  
-- | /arf_get_str/ /x/ /d/ 
--
-- Returns /x/ as a decimal floating-point number, rounding to /d/ digits.
-- Rounding is faithful (at most 1 ulp error).
foreign import ccall "arf.h arf_get_str"
  arf_get_str :: Ptr CArf -> CLong -> IO CString

-- | /arf_fprint/ /file/ /x/ 
--
-- Prints /x/ as an integer mantissa and exponent to the stream /file/.
foreign import ccall "arf.h arf_fprint"
  arf_fprint :: Ptr CFile -> Ptr CArf -> IO ()

-- | /arf_fprintd/ /file/ /y/ /d/ 
--
-- Prints /x/ as a decimal floating-point number to the stream /file/,
-- rounding to /d/ digits. Rounding is faithful (at most 1 ulp error).
foreign import ccall "arf.h arf_fprintd"
  arf_fprintd :: Ptr CFile -> Ptr CArf -> CLong -> IO ()

-- | /arf_dump_str/ /x/ 
--
-- Allocates a string and writes a binary representation of /x/ to it that
-- can be read by @arf_load_str@. The returned string needs to be
-- deallocated with /flint_free/.
foreign import ccall "arf.h arf_dump_str"
  arf_dump_str :: Ptr CArf -> IO CString

-- | /arf_load_str/ /x/ /str/ 
--
-- Parses /str/ into /x/. Returns a nonzero value if /str/ is not formatted
-- correctly.
foreign import ccall "arf.h arf_load_str"
  arf_load_str :: Ptr CArf -> CString -> IO CInt

-- | /arf_dump_file/ /stream/ /x/ 
--
-- Writes a binary representation of /x/ to /stream/ that can be read by
-- @arf_load_file@. Returns a nonzero value if the data could not be
-- written.
foreign import ccall "arf.h arf_dump_file"
  arf_dump_file :: Ptr CFile -> Ptr CArf -> IO CInt

-- | /arf_load_file/ /x/ /stream/ 
--
-- Reads /x/ from /stream/. Returns a nonzero value if the data is not
-- formatted correctly or the read failed. Note that the data is assumed to
-- be delimited by a whitespace or end-of-file, i.e., when writing multiple
-- values with @arf_dump_file@ make sure to insert a whitespace to separate
-- consecutive values.
foreign import ccall "arf.h arf_load_file"
  arf_load_file :: Ptr CArf -> Ptr CFile -> IO CInt

-- Addition and multiplication -------------------------------------------------

-- | /arf_abs/ /res/ /x/ 
--
-- Sets /res/ to the absolute value of /x/ exactly.
foreign import ccall "arf.h arf_abs"
  arf_abs :: Ptr CArf -> Ptr CArf -> IO ()

-- | /arf_neg/ /res/ /x/ 
--
-- Sets /res/ to \(-x\) exactly.
foreign import ccall "arf.h arf_neg"
  arf_neg :: Ptr CArf -> Ptr CArf -> IO ()

-- | /arf_neg_round/ /res/ /x/ /prec/ /rnd/ 
--
-- Sets /res/ to \(-x\).
foreign import ccall "arf.h arf_neg_round"
  arf_neg_round :: Ptr CArf -> Ptr CArf -> CLong -> ArfRnd -> IO CInt

-- | /arf_add/ /res/ /x/ /y/ /prec/ /rnd/ 
--
foreign import ccall "arf.h arf_add"
  arf_add :: Ptr CArf -> Ptr CArf -> Ptr CArf -> CLong -> ArfRnd -> IO CInt

-- | /arf_add_si/ /res/ /x/ /y/ /prec/ /rnd/ 
--
foreign import ccall "arf.h arf_add_si"
  arf_add_si :: Ptr CArf -> Ptr CArf -> CLong -> CLong -> ArfRnd -> IO CInt

-- | /arf_add_ui/ /res/ /x/ /y/ /prec/ /rnd/ 
--
foreign import ccall "arf.h arf_add_ui"
  arf_add_ui :: Ptr CArf -> Ptr CArf -> CULong -> CLong -> ArfRnd -> IO CInt

-- | /arf_add_fmpz/ /res/ /x/ /y/ /prec/ /rnd/ 
--
-- Sets /res/ to \(x + y\).
foreign import ccall "arf.h arf_add_fmpz"
  arf_add_fmpz :: Ptr CArf -> Ptr CArf -> Ptr CFmpz -> CLong -> ArfRnd -> IO CInt

-- | /arf_add_fmpz_2exp/ /res/ /x/ /y/ /e/ /prec/ /rnd/ 
--
-- Sets /res/ to \(x + y 2^e\).
foreign import ccall "arf.h arf_add_fmpz_2exp"
  arf_add_fmpz_2exp :: Ptr CArf -> Ptr CArf -> Ptr CFmpz -> Ptr CFmpz -> CLong -> ArfRnd -> IO CInt

-- | /arf_sub/ /res/ /x/ /y/ /prec/ /rnd/ 
--
foreign import ccall "arf.h arf_sub"
  arf_sub :: Ptr CArf -> Ptr CArf -> Ptr CArf -> CLong -> ArfRnd -> IO CInt

-- | /arf_sub_si/ /res/ /x/ /y/ /prec/ /rnd/ 
--
foreign import ccall "arf.h arf_sub_si"
  arf_sub_si :: Ptr CArf -> Ptr CArf -> CLong -> CLong -> ArfRnd -> IO CInt

-- | /arf_sub_ui/ /res/ /x/ /y/ /prec/ /rnd/ 
--
foreign import ccall "arf.h arf_sub_ui"
  arf_sub_ui :: Ptr CArf -> Ptr CArf -> CULong -> CLong -> ArfRnd -> IO CInt

-- | /arf_sub_fmpz/ /res/ /x/ /y/ /prec/ /rnd/ 
--
-- Sets /res/ to \(x - y\).
foreign import ccall "arf.h arf_sub_fmpz"
  arf_sub_fmpz :: Ptr CArf -> Ptr CArf -> Ptr CFmpz -> CLong -> ArfRnd -> IO CInt

-- | /arf_mul_2exp_si/ /res/ /x/ /e/ 
--
foreign import ccall "arf.h arf_mul_2exp_si"
  arf_mul_2exp_si :: Ptr CArf -> Ptr CArf -> CLong -> IO ()

-- | /arf_mul_2exp_fmpz/ /res/ /x/ /e/ 
--
-- Sets /res/ to \(x 2^e\) exactly.
foreign import ccall "arf.h arf_mul_2exp_fmpz"
  arf_mul_2exp_fmpz :: Ptr CArf -> Ptr CArf -> Ptr CFmpz -> IO ()

-- | /arf_mul/ /res/ /x/ /y/ /prec/ /rnd/ 
--
foreign import ccall "arf.h arf_mul_"
  arf_mul :: Ptr CArf -> Ptr CArf -> Ptr CArf -> CLong -> ArfRnd -> IO CInt

-- | /arf_mul_ui/ /res/ /x/ /y/ /prec/ /rnd/ 
--
foreign import ccall "arf.h arf_mul_ui"
  arf_mul_ui :: Ptr CArf -> Ptr CArf -> CULong -> CLong -> ArfRnd -> IO CInt

-- | /arf_mul_si/ /res/ /x/ /y/ /prec/ /rnd/ 
--
foreign import ccall "arf.h arf_mul_si"
  arf_mul_si :: Ptr CArf -> Ptr CArf -> CLong -> CLong -> ArfRnd -> IO CInt

-- | /arf_mul_mpz/ /res/ /x/ /y/ /prec/ /rnd/ 
--
foreign import ccall "arf.h arf_mul_mpz"
  arf_mul_mpz :: Ptr CArf -> Ptr CArf -> Ptr CMpz -> CLong -> ArfRnd -> IO CInt

-- | /arf_mul_fmpz/ /res/ /x/ /y/ /prec/ /rnd/ 
--
-- Sets /res/ to \(x \cdot y\).
foreign import ccall "arf.h arf_mul_fmpz"
  arf_mul_fmpz :: Ptr CArf -> Ptr CArf -> Ptr CFmpz -> CLong -> ArfRnd -> IO CInt

-- | /arf_addmul/ /z/ /x/ /y/ /prec/ /rnd/ 
--
foreign import ccall "arf.h arf_addmul"
  arf_addmul :: Ptr CArf -> Ptr CArf -> Ptr CArf -> CLong -> ArfRnd -> IO CInt

-- | /arf_addmul_ui/ /z/ /x/ /y/ /prec/ /rnd/ 
--
foreign import ccall "arf.h arf_addmul_ui"
  arf_addmul_ui :: Ptr CArf -> Ptr CArf -> CULong -> CLong -> ArfRnd -> IO CInt

-- | /arf_addmul_si/ /z/ /x/ /y/ /prec/ /rnd/ 
--
foreign import ccall "arf.h arf_addmul_si"
  arf_addmul_si :: Ptr CArf -> Ptr CArf -> CLong -> CLong -> ArfRnd -> IO CInt

-- | /arf_addmul_mpz/ /z/ /x/ /y/ /prec/ /rnd/ 
--
foreign import ccall "arf.h arf_addmul_mpz"
  arf_addmul_mpz :: Ptr CArf -> Ptr CArf -> Ptr CMpz -> CLong -> ArfRnd -> IO CInt

-- | /arf_addmul_fmpz/ /z/ /x/ /y/ /prec/ /rnd/ 
--
-- Performs a fused multiply-add \(z = z + x \cdot y\), updating /z/
-- in-place.
foreign import ccall "arf.h arf_addmul_fmpz"
  arf_addmul_fmpz :: Ptr CArf -> Ptr CArf -> Ptr CFmpz -> CLong -> ArfRnd -> IO CInt

-- | /arf_submul/ /z/ /x/ /y/ /prec/ /rnd/ 
--
foreign import ccall "arf.h arf_submul"
  arf_submul :: Ptr CArf -> Ptr CArf -> Ptr CArf -> CLong -> ArfRnd -> IO CInt

-- | /arf_submul_ui/ /z/ /x/ /y/ /prec/ /rnd/ 
--
foreign import ccall "arf.h arf_submul_ui"
  arf_submul_ui :: Ptr CArf -> Ptr CArf -> CULong -> CLong -> ArfRnd -> IO CInt

-- | /arf_submul_si/ /z/ /x/ /y/ /prec/ /rnd/ 
--
foreign import ccall "arf.h arf_submul_si"
  arf_submul_si :: Ptr CArf -> Ptr CArf -> CLong -> CLong -> ArfRnd -> IO CInt

-- | /arf_submul_mpz/ /z/ /x/ /y/ /prec/ /rnd/ 
--
foreign import ccall "arf.h arf_submul_mpz"
  arf_submul_mpz :: Ptr CArf -> Ptr CArf -> Ptr CMpz -> CLong -> ArfRnd -> IO CInt

-- | /arf_submul_fmpz/ /z/ /x/ /y/ /prec/ /rnd/ 
--
-- Performs a fused multiply-subtract \(z = z - x \cdot y\), updating /z/
-- in-place.
foreign import ccall "arf.h arf_submul_fmpz"
  arf_submul_fmpz :: Ptr CArf -> Ptr CArf -> Ptr CFmpz -> CLong -> ArfRnd -> IO CInt

-- | /arf_fma/ /res/ /x/ /y/ /z/ /prec/ /rnd/ 
--
-- Sets /res/ to \(x \cdot y + z\). This is equivalent to an /addmul/
-- except that /res/ and /z/ can be separate variables.
foreign import ccall "arf.h arf_fma"
  arf_fma :: Ptr CArf -> Ptr CArf -> Ptr CArf -> Ptr CArf -> CLong -> ArfRnd -> IO CInt

-- | /arf_sosq/ /res/ /x/ /y/ /prec/ /rnd/ 
--
-- Sets /res/ to \(x^2 + y^2\), rounded to /prec/ bits in the direction
-- specified by /rnd/.
foreign import ccall "arf.h arf_sosq"
  arf_sosq :: Ptr CArf -> Ptr CArf -> Ptr CArf -> CLong -> ArfRnd -> IO CInt

-- Summation -------------------------------------------------------------------

-- | /arf_sum/ /res/ /terms/ /len/ /prec/ /rnd/ 
--
-- Sets /res/ to the sum of the array /terms/ of length /len/, rounded to
-- /prec/ bits in the direction specified by /rnd/. The sum is computed as
-- if done without any intermediate rounding error, with only a single
-- rounding applied to the final result. Unlike repeated calls to @arf_add@
-- with infinite precision, this function does not overflow if the
-- magnitudes of the terms are far apart. Warning: this function is
-- implemented naively, and the running time is quadratic with respect to
-- /len/ in the worst case.
foreign import ccall "arf.h arf_sum"
  arf_sum :: Ptr CArf -> Ptr CArf -> CLong -> CLong -> ArfRnd -> IO CInt

-- Dot products ----------------------------------------------------------------

-- | /arf_approx_dot/ /res/ /initial/ /subtract/ /x/ /xstep/ /y/ /ystep/ /len/ /prec/ /rnd/ 
--
-- Computes an approximate dot product, with the same meaning of the
-- parameters as @arb_dot@. This operation is not correctly rounded: the
-- final rounding is done in the direction @rnd@ but intermediate roundings
-- are implementation-defined.
foreign import ccall "arf.h arf_approx_dot"
  arf_approx_dot :: Ptr CArf -> Ptr CArf -> CInt -> Ptr CArf -> CLong -> Ptr CArf -> CLong -> CLong -> CLong -> ArfRnd -> IO ()

-- Division --------------------------------------------------------------------

-- | /arf_div/ /res/ /x/ /y/ /prec/ /rnd/ 
--
foreign import ccall "arf.h arf_div"
  arf_div :: Ptr CArf -> Ptr CArf -> Ptr CArf -> CLong -> ArfRnd -> IO CInt

-- | /arf_div_ui/ /res/ /x/ /y/ /prec/ /rnd/ 
--
foreign import ccall "arf.h arf_div_ui"
  arf_div_ui :: Ptr CArf -> Ptr CArf -> CULong -> CLong -> ArfRnd -> IO CInt

-- | /arf_ui_div/ /res/ /x/ /y/ /prec/ /rnd/ 
--
foreign import ccall "arf.h arf_ui_div"
  arf_ui_div :: Ptr CArf -> CULong -> Ptr CArf -> CLong -> ArfRnd -> IO CInt

-- | /arf_div_si/ /res/ /x/ /y/ /prec/ /rnd/ 
--
foreign import ccall "arf.h arf_div_si"
  arf_div_si :: Ptr CArf -> Ptr CArf -> CLong -> CLong -> ArfRnd -> IO CInt

-- | /arf_si_div/ /res/ /x/ /y/ /prec/ /rnd/ 
--
foreign import ccall "arf.h arf_si_div"
  arf_si_div :: Ptr CArf -> CLong -> Ptr CArf -> CLong -> ArfRnd -> IO CInt

-- | /arf_div_fmpz/ /res/ /x/ /y/ /prec/ /rnd/ 
--
foreign import ccall "arf.h arf_div_fmpz"
  arf_div_fmpz :: Ptr CArf -> Ptr CArf -> Ptr CFmpz -> CLong -> ArfRnd -> IO CInt

-- | /arf_fmpz_div/ /res/ /x/ /y/ /prec/ /rnd/ 
--
foreign import ccall "arf.h arf_fmpz_div"
  arf_fmpz_div :: Ptr CArf -> Ptr CFmpz -> Ptr CArf -> CLong -> ArfRnd -> IO CInt

-- | /arf_fmpz_div_fmpz/ /res/ /x/ /y/ /prec/ /rnd/ 
--
-- Sets /res/ to \(x / y\), rounded to /prec/ bits in the direction
-- specified by /rnd/, returning nonzero iff the operation is inexact. The
-- result is NaN if /y/ is zero.
foreign import ccall "arf.h arf_fmpz_div_fmpz"
  arf_fmpz_div_fmpz :: Ptr CArf -> Ptr CFmpz -> Ptr CFmpz -> CLong -> ArfRnd -> IO CInt

-- Square roots ----------------------------------------------------------------

-- | /arf_sqrt/ /res/ /x/ /prec/ /rnd/ 
--
foreign import ccall "arf.h arf_sqrt"
  arf_sqrt :: Ptr CArf -> Ptr CArf -> CLong -> ArfRnd -> IO CInt

-- | /arf_sqrt_ui/ /res/ /x/ /prec/ /rnd/ 
--
foreign import ccall "arf.h arf_sqrt_ui"
  arf_sqrt_ui :: Ptr CArf -> CULong -> CLong -> ArfRnd -> IO CInt

-- | /arf_sqrt_fmpz/ /res/ /x/ /prec/ /rnd/ 
--
-- Sets /res/ to \(\sqrt{x}\). The result is NaN if /x/ is negative.
foreign import ccall "arf.h arf_sqrt_fmpz"
  arf_sqrt_fmpz :: Ptr CArf -> Ptr CFmpz -> CLong -> ArfRnd -> IO CInt

-- | /arf_rsqrt/ /res/ /x/ /prec/ /rnd/ 
--
-- Sets /res/ to \(1/\sqrt{x}\). The result is NaN if /x/ is negative, and
-- \(+\infty\) if /x/ is zero.
foreign import ccall "arf.h arf_rsqrt"
  arf_rsqrt :: Ptr CArf -> Ptr CArf -> CLong -> ArfRnd -> IO CInt

-- | /arf_root/ /res/ /x/ /k/ /prec/ /rnd/ 
--
-- Sets /res/ to \(x^{1/k}\). The result is NaN if /x/ is negative.
-- Warning: this function is a wrapper around the MPFR root function. It
-- gets slow and uses much memory for large /k/. Consider working with
-- @arb_root_ui@ for large /k/ instead of using this function directly.
foreign import ccall "arf.h arf_root"
  arf_root :: Ptr CArf -> Ptr CArf -> CULong -> CLong -> ArfRnd -> IO CInt

-- Complex arithmetic ----------------------------------------------------------

-- | /arf_complex_mul/ /e/ /f/ /a/ /b/ /c/ /d/ /prec/ /rnd/ 
--
foreign import ccall "arf.h arf_complex_mul"
  arf_complex_mul :: Ptr CArf -> Ptr CArf -> Ptr CArf -> Ptr CArf -> Ptr CArf -> Ptr CArf -> CLong -> ArfRnd -> IO CInt

-- | /arf_complex_mul_fallback/ /e/ /f/ /a/ /b/ /c/ /d/ /prec/ /rnd/ 
--
-- Computes the complex product \(e + fi = (a + bi)(c + di)\), rounding
-- both \(e\) and \(f\) correctly to /prec/ bits in the direction specified
-- by /rnd/. The first bit in the return code indicates inexactness of
-- \(e\), and the second bit indicates inexactness of \(f\).
-- 
-- If any of the components /a/, /b/, /c/, /d/ is zero, two real
-- multiplications and no additions are done. This convention is used even
-- if any other part contains an infinity or NaN, and the behavior with
-- infinite\/NaN input is defined accordingly.
-- 
-- The /fallback/ version is implemented naively, for testing purposes. No
-- squaring optimization is implemented.
foreign import ccall "arf.h arf_complex_mul_fallback"
  arf_complex_mul_fallback :: Ptr CArf -> Ptr CArf -> Ptr CArf -> Ptr CArf -> Ptr CArf -> Ptr CArf -> CLong -> ArfRnd -> IO CInt

-- | /arf_complex_sqr/ /e/ /f/ /a/ /b/ /prec/ /rnd/ 
--
-- Computes the complex square \(e + fi = (a + bi)^2\). This function has
-- identical semantics to @arf_complex_mul@ (with \(c = a, b = d\)), but is
-- faster.
foreign import ccall "arf.h arf_complex_sqr"
  arf_complex_sqr :: Ptr CArf -> Ptr CArf -> Ptr CArf -> Ptr CArf -> CLong -> ArfRnd -> IO CInt

-- Low-level methods -----------------------------------------------------------

-- | /_arf_get_integer_mpn/ /y/ /xp/ /xn/ /exp/ 
--
-- Given a floating-point number /x/ represented by /xn/ limbs at /xp/ and
-- an exponent /exp/, writes the integer part of /x/ to /y/, returning
-- whether the result is inexact. The correct number of limbs is written
-- (no limbs are written if the integer part of /x/ is zero). Assumes that
-- @xp[0]@ is nonzero and that the top bit of @xp[xn-1]@ is set.
foreign import ccall "arf.h _arf_get_integer_mpn"
  _arf_get_integer_mpn :: Ptr CMp -> Ptr CMp -> CMpSize -> CLong -> IO CInt

-- | /_arf_set_mpn_fixed/ /z/ /xp/ /xn/ /fixn/ /negative/ /prec/ /rnd/ 
--
-- Sets /z/ to the fixed-point number having /xn/ total limbs and /fixn/
-- fractional limbs, negated if /negative/ is set, rounding /z/ to /prec/
-- bits in the direction /rnd/ and returning whether the result is inexact.
-- Both /xn/ and /fixn/ must be nonnegative and not so large that the bit
-- shift would overflow an /slong/, but otherwise no assumptions are made
-- about the input.
foreign import ccall "arf.h _arf_set_mpn_fixed"
  _arf_set_mpn_fixed :: Ptr CArf -> Ptr CMp -> CMpSize -> CMpSize -> CInt -> CLong -> ArfRnd -> IO CInt

-- | /_arf_set_round_ui/ /z/ /x/ /sgnbit/ /prec/ /rnd/ 
--
-- Sets /z/ to the integer /x/, negated if /sgnbit/ is 1, rounded to /prec/
-- bits in the direction specified by /rnd/. There are no assumptions on
-- /x/.
foreign import ccall "arf.h _arf_set_round_ui"
  _arf_set_round_ui :: Ptr CArf -> CULong -> CInt -> CLong -> ArfRnd -> IO CInt

-- | /_arf_set_round_uiui/ /z/ /fix/ /hi/ /lo/ /sgnbit/ /prec/ /rnd/ 
--
-- Sets the mantissa of /z/ to the two-limb mantissa given by /hi/ and
-- /lo/, negated if /sgnbit/ is 1, rounded to /prec/ bits in the direction
-- specified by /rnd/. Requires that not both /hi/ and /lo/ are zero.
-- Writes the exponent shift to /fix/ without writing the exponent of /z/
-- directly.
foreign import ccall "arf.h _arf_set_round_uiui"
  _arf_set_round_uiui :: Ptr CArf -> Ptr CLong -> CMpLimb -> CMpLimb -> CInt -> CLong -> ArfRnd -> IO CInt

-- | /_arf_set_round_mpn/ /z/ /exp_shift/ /x/ /xn/ /sgnbit/ /prec/ /rnd/ 
--
-- Sets the mantissa of /z/ to the mantissa given by the /xn/ limbs in /x/,
-- negated if /sgnbit/ is 1, rounded to /prec/ bits in the direction
-- specified by /rnd/. Returns the inexact flag. Requires that /xn/ is
-- positive and that the top limb of /x/ is nonzero. If /x/ has leading
-- zero bits, writes the shift to /exp_shift/. This method does not write
-- the exponent of /z/ directly. Requires that /x/ does not point to the
-- limbs of /z/.
foreign import ccall "arf.h _arf_set_round_mpn"
  _arf_set_round_mpn :: Ptr CArf -> Ptr CLong -> Ptr CMp -> CMpSize -> CInt -> CLong -> ArfRnd -> IO CInt

