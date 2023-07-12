
module Data.Number.Flint.Acb.FFI (
  -- * Complex numbers
  -- * Types
    Acb (..)
  , CAcb (..)
  , newAcb
  , withAcb
  , withNewAcb
  , withAcbRe
  , withAcbIm
  -- * Memory management
  , acb_init
  , acb_clear
  , _acb_vec_init
  , _acb_vec_clear
  , acb_allocated_bytes
  , _acb_vec_allocated_bytes
  , _acb_vec_estimate_allocated_bytes
  -- * Basic manipulation
  , acb_zero
  , acb_one
  , acb_onei
  , acb_set
  , acb_set_ui
  , acb_set_si
  , acb_set_d
  , acb_set_fmpz
  , acb_set_arb
  , acb_set_si_si
  , acb_set_d_d
  , acb_set_fmpz_fmpz
  , acb_set_arb_arb
  , acb_set_fmpq
  , acb_set_round
  , acb_set_round_fmpz
  , acb_set_round_arb
  , acb_swap
  , acb_add_error_arf
  , acb_add_error_mag
  , acb_add_error_arb
  , acb_get_mid
  -- * Input and output
  , acb_get_str
  , acb_get_strd
  , acb_get_strn
  , acb_print
  , acb_fprint
  , acb_printd
  , acb_fprintd
  , acb_printn
  , acb_fprintn
  -- * Random number generation
  , acb_randtest
  , acb_randtest_special
  , acb_randtest_precise
  , acb_randtest_param
  -- * Precision and comparisons
  , acb_is_zero
  , acb_is_one
  , acb_is_finite
  , acb_is_exact
  , acb_is_int
  , acb_is_int_2exp_si
  , acb_equal
  , acb_equal_si
  , acb_eq
  , acb_ne
  , acb_overlaps
  , acb_union
  , acb_get_abs_ubound_arf
  , acb_get_abs_lbound_arf
  , acb_get_rad_ubound_arf
  , acb_get_mag
  , acb_get_mag_lower
  , acb_contains_fmpq
  , acb_contains_fmpz
  , acb_contains
  , acb_contains_zero
  , acb_contains_int
  , acb_contains_interior
  , acb_rel_error_bits
  , acb_rel_accuracy_bits
  , acb_rel_one_accuracy_bits
  , acb_bits
  , acb_indeterminate
  , acb_trim
  , acb_is_real
  , acb_get_unique_fmpz
  -- * Complex parts
  , acb_get_real
  , acb_get_imag
  , acb_arg
  , acb_abs
  , acb_sgn
  , acb_csgn
  -- * Arithmetic
  , acb_neg
  , acb_neg_round
  , acb_conj
  , acb_add_ui
  , acb_add_si
  , acb_add_fmpz
  , acb_add_arb
  , acb_add
  , acb_sub_ui
  , acb_sub_si
  , acb_sub_fmpz
  , acb_sub_arb
  , acb_sub
  , acb_mul_onei
  , acb_div_onei
  , acb_mul_ui
  , acb_mul_si
  , acb_mul_fmpz
  , acb_mul_arb
  , acb_mul
  , acb_mul_2exp_si
  , acb_mul_2exp_fmpz
  , acb_sqr
  , acb_cube
  , acb_addmul
  , acb_addmul_ui
  , acb_addmul_si
  , acb_addmul_fmpz
  , acb_addmul_arb
  , acb_submul
  , acb_submul_ui
  , acb_submul_si
  , acb_submul_fmpz
  , acb_submul_arb
  , acb_inv
  , acb_div_ui
  , acb_div_si
  , acb_div_fmpz
  , acb_div_arb
  , acb_div
  -- * Dot product
  , acb_dot_precise
  , acb_approx_dot
  , acb_dot_ui
  -- * Mathematical constants
  , acb_const_pi
  -- * Powers and roots
  , acb_sqrt
  , acb_sqrt_analytic
  , acb_rsqrt
  , acb_rsqrt_analytic
  , acb_quadratic_roots_fmpz
  , acb_root_ui
  , acb_pow_fmpz
  , acb_pow_ui
  , acb_pow_si
  , acb_pow_arb
  , acb_pow
  , acb_pow_analytic
  , acb_unit_root
  -- * Exponentials and logarithms
  , acb_exp
  , acb_exp_pi_i
  , acb_exp_invexp
  , acb_expm1
  , acb_log
  , acb_log_analytic
  , acb_log1p
  -- * Trigonometric functions
  , acb_sin
  , acb_cos
  , acb_sin_cos
  , acb_tan
  , acb_cot
  , acb_sin_pi
  , acb_cos_pi
  , acb_sin_cos_pi
  , acb_tan_pi
  , acb_cot_pi
  , acb_sec
  , acb_csc
  , acb_csc_pi
  , acb_sinc
  , acb_sinc_pi
  -- * Inverse trigonometric functions
  , acb_asin
  , acb_acos
  , acb_atan
  -- * Hyperbolic functions
  , acb_sinh
  , acb_cosh
  , acb_sinh_cosh
  , acb_tanh
  , acb_coth
  , acb_sech
  , acb_csch
  -- * Inverse hyperbolic functions
  , acb_asinh
  , acb_acosh
  , acb_atanh
  -- * Lambert W function
  , acb_lambertw_asymp
  , acb_lambertw_check_branch
  , acb_lambertw_bound_deriv
  , acb_lambertw
  -- * Rising factorials
  , acb_rising_ui
  -- * Gamma function
  , acb_gamma
  , acb_rgamma
  , acb_lgamma
  , acb_digamma
  , acb_log_sin_pi
  , acb_polygamma
  , acb_barnes_g
  , acb_log_barnes_g
  -- * Zeta function
  , acb_zeta
  , acb_hurwitz_zeta
  , acb_bernoulli_poly_ui
  -- * Polylogarithms
  , acb_polylog
  , acb_polylog_si
  -- * Arithmetic-geometric mean
  , acb_agm1
  , acb_agm1_cpx
  , acb_agm
  -- * Other special functions
  , acb_chebyshev_t_ui
  , acb_chebyshev_u_ui
  , acb_chebyshev_t2_ui
  , acb_chebyshev_u2_ui
  -- * Piecewise real functions
  , acb_real_abs
  , acb_real_sgn
  , acb_real_heaviside
  , acb_real_floor
  , acb_real_ceil
  , acb_real_max
  , acb_real_min
  , acb_real_sqrtpos
  -- * Vector functions
  , _acb_vec_zero
  , _acb_vec_is_zero
  , _acb_vec_is_real
  , _acb_vec_set
  , _acb_vec_set_round
  , _acb_vec_swap
  , _acb_vec_neg
  , _acb_vec_add
  , _acb_vec_sub
  , _acb_vec_scalar_submul
  , _acb_vec_scalar_addmul
  , _acb_vec_scalar_mul
  , _acb_vec_scalar_mul_ui
  , _acb_vec_scalar_mul_2exp_si
  , _acb_vec_scalar_mul_onei
  , _acb_vec_scalar_div_ui
  , _acb_vec_scalar_div
  , _acb_vec_scalar_mul_arb
  , _acb_vec_scalar_div_arb
  , _acb_vec_scalar_mul_fmpz
  , _acb_vec_scalar_div_fmpz
  , _acb_vec_bits
  , _acb_vec_set_powers
  , _acb_vec_unit_roots
  , _acb_vec_add_error_arf_vec
  , _acb_vec_add_error_mag_vec
  , _acb_vec_indeterminate
  , _acb_vec_trim
  , _acb_vec_get_unique_fmpz_vec
  , _acb_vec_sort_pretty
) where 

-- Complex numbers -------------------------------------------------------------

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.C.Types
import Foreign.C.String
import Foreign.Storable
import Foreign.Marshal.Alloc (free)
import Foreign.Marshal.Array (advancePtr)

import Data.Typeable

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpq

import Data.Number.Flint.Arb.Types
import Data.Number.Flint.Acb.Types

#include <flint/acb.h>

-- Types -----------------------------------------------------------------------

-- | Create new `Acb`
newAcb = do
  x <- mallocForeignPtr
  withForeignPtr x acb_init
  addForeignPtrFinalizer p_acb_clear x
  return $ Acb x

-- | Apply function `f` to `Acb`
withAcb (Acb p) f = do
  withForeignPtr p $ \fp -> (Acb p,) <$> f fp

-- | Apply function `f` to new `Acb`
withNewAcb f = do
  x <- newAcb
  withAcb x f

-- | Apply function `f` to real part of `Acb`
withAcbRe :: Acb -> (Ptr CArb -> IO t) -> IO (Acb, t)
withAcbRe (Acb p) f = do
   withForeignPtr p $ \fp -> do
     withForeignPtr p $ \fp -> (Acb p,) <$> f (castPtr fp)

-- | Apply function `f` to imaginary part of `Acb`
withAcbIm :: Acb -> (Ptr CArb -> IO t) -> IO (Acb, t)
withAcbIm (Acb p) f = do
   withForeignPtr p $ \fp -> do
     withForeignPtr p $ \fp -> (Acb p,) <$> f (castPtr fp `advancePtr` 1)

instance Storable CAcb where
  sizeOf    _ = #{size      acb_t}
  alignment _ = #{alignment acb_t}
  peek ptr = CAcb
    <$> #{peek acb_struct, real} ptr
    <*> #{peek acb_struct, imag} ptr
  poke = error "CAcb.poke not defined."
  

-- Memory management -----------------------------------------------------------

-- | /acb_init/ /x/ 
-- 
-- Initializes the variable /x/ for use, and sets its value to zero.
foreign import ccall "acb.h acb_init"
  acb_init :: Ptr CAcb -> IO ()

-- | /acb_clear/ /x/ 
-- 
-- Clears the variable /x/, freeing or recycling its allocated memory.
foreign import ccall "acb.h acb_clear"
  acb_clear :: Ptr CAcb -> IO ()

foreign import ccall "acb.h &acb_clear"
  p_acb_clear :: FunPtr (Ptr CAcb -> IO ())

-- | /_acb_vec_init/ /n/ 
-- 
-- Returns a pointer to an array of /n/ initialized /acb_struct/:s.
foreign import ccall "acb.h _acb_vec_init"
  _acb_vec_init :: CLong -> IO (Ptr CAcb)

-- | /_acb_vec_clear/ /v/ /n/ 
-- 
-- Clears an array of /n/ initialized /acb_struct/:s.
foreign import ccall "acb.h _acb_vec_clear"
  _acb_vec_clear :: Ptr CAcb -> CLong -> IO ()

-- | /acb_allocated_bytes/ /x/ 
-- 
-- Returns the total number of bytes heap-allocated internally by this
-- object. The count excludes the size of the structure itself. Add
-- @sizeof(acb_struct)@ to get the size of the object as a whole.
foreign import ccall "acb.h acb_allocated_bytes"
  acb_allocated_bytes :: Ptr CAcb -> IO CLong

-- | /_acb_vec_allocated_bytes/ /vec/ /len/ 
-- 
-- Returns the total number of bytes allocated for this vector, i.e. the
-- space taken up by the vector itself plus the sum of the internal heap
-- allocation sizes for all its member elements.
foreign import ccall "acb.h _acb_vec_allocated_bytes"
  _acb_vec_allocated_bytes :: Ptr CAcb -> CLong -> IO CLong

-- | /_acb_vec_estimate_allocated_bytes/ /len/ /prec/ 
-- 
-- Estimates the number of bytes that need to be allocated for a vector of
-- /len/ elements with /prec/ bits of precision, including the space for
-- internal limb data. See comments for
-- @_arb_vec_estimate_allocated_bytes@.
foreign import ccall "acb.h _acb_vec_estimate_allocated_bytes"
  _acb_vec_estimate_allocated_bytes :: CLong -> CLong -> IO CDouble

-- Basic manipulation ----------------------------------------------------------

foreign import ccall "acb.h acb_zero"
  acb_zero :: Ptr CAcb -> IO ()

foreign import ccall "acb.h acb_one"
  acb_one :: Ptr CAcb -> IO ()

-- | /acb_onei/ /z/ 
-- 
-- Sets /z/ respectively to 0, 1, \(i = \sqrt{-1}\).
foreign import ccall "acb.h acb_onei"
  acb_onei :: Ptr CAcb -> IO ()

foreign import ccall "acb.h acb_set"
  acb_set :: Ptr CAcb -> Ptr CAcb -> IO ()

foreign import ccall "acb.h acb_set_ui"
  acb_set_ui :: Ptr CAcb -> CULong -> IO ()

foreign import ccall "acb.h acb_set_si"
  acb_set_si :: Ptr CAcb -> CLong -> IO ()

foreign import ccall "acb.h acb_set_d"
  acb_set_d :: Ptr CAcb -> CDouble -> IO ()

foreign import ccall "acb.h acb_set_fmpz"
  acb_set_fmpz :: Ptr CAcb -> Ptr CFmpz -> IO ()

-- | /acb_set_arb/ /z/ /c/ 
-- 
-- Sets /z/ to the value of /x/.
foreign import ccall "acb.h acb_set_arb"
  acb_set_arb :: Ptr CAcb -> Ptr CArb -> IO ()

foreign import ccall "acb.h acb_set_si_si"
  acb_set_si_si :: Ptr CAcb -> CLong -> CLong -> IO ()

foreign import ccall "acb.h acb_set_d_d"
  acb_set_d_d :: Ptr CAcb -> CDouble -> CDouble -> IO ()

foreign import ccall "acb.h acb_set_fmpz_fmpz"
  acb_set_fmpz_fmpz :: Ptr CAcb -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /acb_set_arb_arb/ /z/ /x/ /y/ 
-- 
-- Sets the real and imaginary part of /z/ to the values /x/ and /y/
-- respectively
foreign import ccall "acb.h acb_set_arb_arb"
  acb_set_arb_arb :: Ptr CAcb -> Ptr CArb -> Ptr CArb -> IO ()

foreign import ccall "acb.h acb_set_fmpq"
  acb_set_fmpq :: Ptr CAcb -> Ptr CFmpq -> CLong -> IO ()

foreign import ccall "acb.h acb_set_round"
  acb_set_round :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

foreign import ccall "acb.h acb_set_round_fmpz"
  acb_set_round_fmpz :: Ptr CAcb -> Ptr CFmpz -> CLong -> IO ()

-- | /acb_set_round_arb/ /z/ /x/ /prec/ 
-- 
-- Sets /z/ to /x/, rounded to /prec/ bits.
foreign import ccall "acb.h acb_set_round_arb"
  acb_set_round_arb :: Ptr CAcb -> Ptr CArb -> CLong -> IO ()

-- | /acb_swap/ /z/ /x/ 
-- 
-- Swaps /z/ and /x/ efficiently.
foreign import ccall "acb.h acb_swap"
  acb_swap :: Ptr CAcb -> Ptr CAcb -> IO ()

foreign import ccall "acb.h acb_add_error_arf"
  acb_add_error_arf :: Ptr CAcb -> Ptr CArf -> IO ()

foreign import ccall "acb.h acb_add_error_mag"
  acb_add_error_mag :: Ptr CAcb -> Ptr CMag -> IO ()

-- | /acb_add_error_arb/ /x/ /err/ 
-- 
-- Adds /err/ to the error bounds of both the real and imaginary parts of
-- /x/, modifying /x/ in-place.
foreign import ccall "acb.h acb_add_error_arb"
  acb_add_error_arb :: Ptr CAcb -> Ptr CArb -> IO ()

-- | /acb_get_mid/ /m/ /x/ 
-- 
-- Sets /m/ to the midpoint of /x/.
foreign import ccall "acb.h acb_get_mid"
  acb_get_mid :: Ptr CAcb -> Ptr CAcb -> IO ()

-- Input and output ------------------------------------------------------------

foreign import ccall "acb.h acb_get_str"
  acb_get_str :: Ptr CAcb -> IO CString

foreign import ccall "acb.h acb_get_strd"
  acb_get_strd :: Ptr CAcb -> CLong -> IO CString

foreign import ccall "acb.h acb_get_strn"
  acb_get_strn :: Ptr CAcb -> CLong -> ArbStrOption -> IO CString

-- The /acb_print.../ functions print to standard output, while
-- /acb_fprint.../ functions print to the stream /file/.
--
acb_print :: Ptr CAcb -> IO ()
acb_print x = do
  cstr <- acb_get_str x
  str <- peekCString cstr
  free cstr
  putStr str

-- | /acb_fprint/ /file/ /x/ 
-- 
-- Prints the internal representation of /x/.
foreign import ccall "acb.h acb_fprint"
  acb_fprint :: Ptr CFile -> Ptr CAcb -> IO ()

-- | /acb_printd/ /file/ /x/ /digits/ 
-- 
-- Prints /x/ in decimal to stdout. The printed value of the radius is
-- not adjusted to compensate for the fact that the binary-to-decimal
-- conversion of both the midpoint and the radius introduces
-- additional error.
acb_printd :: Ptr CAcb -> CLong -> IO ()
acb_printd x prec = do
  cstr <- acb_get_strd x prec
  str <- peekCString cstr
  free cstr
  putStr str

-- | /acb_fprintd/ /file/ /x/ /digits/ 
-- 
-- Prints /x/ in decimal to stream /file/. The printed value of the
-- radius is not adjusted to compensate for the fact that the
-- binary-to-decimal conversion of both the midpoint and the radius
-- introduces additional error.
foreign import ccall "acb.h acb_fprintd"
  acb_fprintd :: Ptr CFile -> Ptr CAcb -> CLong -> IO ()

acb_printn :: Ptr CAcb -> CLong -> ArbStrOption -> IO ()
acb_printn x prec opts = do
  cstr <- acb_get_strn x prec opts
  str <- peekCString cstr
  free cstr
  putStr str

-- | /acb_fprintn/ /file/ /x/ /digits/ /flags/ 
-- 
-- Prints a nice decimal representation of /x/, using the format of
-- @arb_get_str@ (or the corresponding @arb_printn@) for the real and
-- imaginary parts.
-- 
-- By default, the output shows the midpoint of both the real and imaginary
-- parts with a guaranteed error of at most one unit in the last decimal
-- place. In addition, explicit error bounds are printed so that the
-- displayed decimal interval is guaranteed to enclose /x/.
-- 
-- Any flags understood by @arb_get_str@ can be passed via /flags/ to
-- control the format of the real and imaginary parts.
foreign import ccall "acb.h acb_fprintn"
  acb_fprintn :: Ptr CFile -> Ptr CAcb -> CLong -> ArbStrOption -> IO ()

-- Random number generation ----------------------------------------------------

-- | /acb_randtest/ /z/ /state/ /prec/ /mag_bits/ 
-- 
-- Generates a random complex number by generating separate random real and
-- imaginary parts.
foreign import ccall "acb.h acb_randtest"
  acb_randtest :: Ptr CAcb -> Ptr CFRandState -> CLong -> CLong -> IO ()

-- | /acb_randtest_special/ /z/ /state/ /prec/ /mag_bits/ 
-- 
-- Generates a random complex number by generating separate random real and
-- imaginary parts. Also generates NaNs and infinities.
foreign import ccall "acb.h acb_randtest_special"
  acb_randtest_special :: Ptr CAcb -> Ptr CFRandState -> CLong -> CLong -> IO ()

-- | /acb_randtest_precise/ /z/ /state/ /prec/ /mag_bits/ 
-- 
-- Generates a random complex number with precise real and imaginary parts.
foreign import ccall "acb.h acb_randtest_precise"
  acb_randtest_precise :: Ptr CAcb -> Ptr CFRandState -> CLong -> CLong -> IO ()

-- | /acb_randtest_param/ /z/ /state/ /prec/ /mag_bits/ 
-- 
-- Generates a random complex number, with very high probability of
-- generating integers and half-integers.
foreign import ccall "acb.h acb_randtest_param"
  acb_randtest_param :: Ptr CAcb -> Ptr CFRandState -> CLong -> CLong -> IO ()

-- Precision and comparisons ---------------------------------------------------

-- | /acb_is_zero/ /z/ 
-- 
-- Returns nonzero iff /z/ is zero.
foreign import ccall "acb.h acb_is_zero"
  acb_is_zero :: Ptr CAcb -> IO CInt

-- | /acb_is_one/ /z/ 
-- 
-- Returns nonzero iff /z/ is exactly 1.
foreign import ccall "acb.h acb_is_one"
  acb_is_one :: Ptr CAcb -> IO CInt

-- | /acb_is_finite/ /z/ 
-- 
-- Returns nonzero iff /z/ certainly is finite.
foreign import ccall "acb.h acb_is_finite"
  acb_is_finite :: Ptr CAcb -> IO CInt

-- | /acb_is_exact/ /z/ 
-- 
-- Returns nonzero iff /z/ is exact.
foreign import ccall "acb.h acb_is_exact"
  acb_is_exact :: Ptr CAcb -> IO CInt

-- | /acb_is_int/ /z/ 
-- 
-- Returns nonzero iff /z/ is an exact integer.
foreign import ccall "acb.h acb_is_int"
  acb_is_int :: Ptr CAcb -> IO CInt

-- | /acb_is_int_2exp_si/ /x/ /e/ 
-- 
-- Returns nonzero iff /z/ exactly equals \(n 2^e\) for some integer /n/.
foreign import ccall "acb.h acb_is_int_2exp_si"
  acb_is_int_2exp_si :: Ptr CAcb -> CLong -> IO CInt

-- | /acb_equal/ /x/ /y/ 
-- 
-- Returns nonzero iff /x/ and /y/ are identical as sets, i.e. if the real
-- and imaginary parts are equal as balls.
-- 
-- Note that this is not the same thing as testing whether both /x/ and /y/
-- certainly represent the same complex number, unless either /x/ or /y/ is
-- exact (and neither contains NaN). To test whether both operands /might/
-- represent the same mathematical quantity, use @acb_overlaps@ or
-- @acb_contains@, depending on the circumstance.
foreign import ccall "acb.h acb_equal"
  acb_equal :: Ptr CAcb -> Ptr CAcb -> IO CInt

-- | /acb_equal_si/ /x/ /y/ 
-- 
-- Returns nonzero iff /x/ is equal to the integer /y/.
foreign import ccall "acb.h acb_equal_si"
  acb_equal_si :: Ptr CAcb -> CLong -> IO CInt

-- | /acb_eq/ /x/ /y/ 
-- 
-- Returns nonzero iff /x/ and /y/ are certainly equal, as determined by
-- testing that @arb_eq@ holds for both the real and imaginary parts.
foreign import ccall "acb.h acb_eq"
  acb_eq :: Ptr CAcb -> Ptr CAcb -> IO CInt

-- | /acb_ne/ /x/ /y/ 
-- 
-- Returns nonzero iff /x/ and /y/ are certainly not equal, as determined
-- by testing that @arb_ne@ holds for either the real or imaginary parts.
foreign import ccall "acb.h acb_ne"
  acb_ne :: Ptr CAcb -> Ptr CAcb -> IO CInt

-- | /acb_overlaps/ /x/ /y/ 
-- 
-- Returns nonzero iff /x/ and /y/ have some point in common.
foreign import ccall "acb.h acb_overlaps"
  acb_overlaps :: Ptr CAcb -> Ptr CAcb -> IO CInt

-- | /acb_union/ /z/ /x/ /y/ /prec/ 
-- 
-- Sets /z/ to a complex interval containing both /x/ and /y/.
foreign import ccall "acb.h acb_union"
  acb_union :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_get_abs_ubound_arf/ /u/ /z/ /prec/ 
-- 
-- Sets /u/ to an upper bound for the absolute value of /z/, computed using
-- a working precision of /prec/ bits.
foreign import ccall "acb.h acb_get_abs_ubound_arf"
  acb_get_abs_ubound_arf :: Ptr CArf -> Ptr CAcb -> CLong -> IO ()

-- | /acb_get_abs_lbound_arf/ /u/ /z/ /prec/ 
-- 
-- Sets /u/ to a lower bound for the absolute value of /z/, computed using
-- a working precision of /prec/ bits.
foreign import ccall "acb.h acb_get_abs_lbound_arf"
  acb_get_abs_lbound_arf :: Ptr CArf -> Ptr CAcb -> CLong -> IO ()

-- | /acb_get_rad_ubound_arf/ /u/ /z/ /prec/ 
-- 
-- Sets /u/ to an upper bound for the error radius of /z/ (the value is
-- currently not computed tightly).
foreign import ccall "acb.h acb_get_rad_ubound_arf"
  acb_get_rad_ubound_arf :: Ptr CArf -> Ptr CAcb -> CLong -> IO ()

-- | /acb_get_mag/ /u/ /x/ 
-- 
-- Sets /u/ to an upper bound for the absolute value of /x/.
foreign import ccall "acb.h acb_get_mag"
  acb_get_mag :: Ptr CMag -> Ptr CAcb -> IO ()

-- | /acb_get_mag_lower/ /u/ /x/ 
-- 
-- Sets /u/ to a lower bound for the absolute value of /x/.
foreign import ccall "acb.h acb_get_mag_lower"
  acb_get_mag_lower :: Ptr CMag -> Ptr CAcb -> IO ()

foreign import ccall "acb.h acb_contains_fmpq"
  acb_contains_fmpq :: Ptr CAcb -> Ptr CFmpq -> IO CInt

foreign import ccall "acb.h acb_contains_fmpz"
  acb_contains_fmpz :: Ptr CAcb -> Ptr CFmpz -> IO CInt

-- | /acb_contains/ /x/ /y/ 
-- 
-- Returns nonzero iff /y/ is contained in /x/.
foreign import ccall "acb.h acb_contains"
  acb_contains :: Ptr CAcb -> Ptr CAcb -> IO CInt

-- | /acb_contains_zero/ /x/ 
-- 
-- Returns nonzero iff zero is contained in /x/.
foreign import ccall "acb.h acb_contains_zero"
  acb_contains_zero :: Ptr CAcb -> IO CInt

-- | /acb_contains_int/ /x/ 
-- 
-- Returns nonzero iff the complex interval represented by /x/ contains an
-- integer.
foreign import ccall "acb.h acb_contains_int"
  acb_contains_int :: Ptr CAcb -> IO CInt

-- | /acb_contains_interior/ /x/ /y/ 
-- 
-- Tests if /y/ is contained in the interior of /x/. This predicate always
-- evaluates to false if /x/ and /y/ are both real-valued, since an
-- imaginary part of 0 is not considered contained in the interior of the
-- point interval 0. More generally, the same problem occurs for intervals
-- with an exact real or imaginary part. Such intervals must be handled
-- specially by the user where a different interpretation is intended.
foreign import ccall "acb.h acb_contains_interior"
  acb_contains_interior :: Ptr CAcb -> Ptr CAcb -> IO CInt

-- | /acb_rel_error_bits/ /x/ 
-- 
-- Returns the effective relative error of /x/ measured in bits. This is
-- computed as if calling @arb_rel_error_bits@ on the real ball whose
-- midpoint is the larger out of the real and imaginary midpoints of /x/,
-- and whose radius is the larger out of the real and imaginary radiuses of
-- /x/.
foreign import ccall "acb.h acb_rel_error_bits"
  acb_rel_error_bits :: Ptr CAcb -> IO CLong

-- | /acb_rel_accuracy_bits/ /x/ 
-- 
-- Returns the effective relative accuracy of /x/ measured in bits, equal
-- to the negative of the return value from @acb_rel_error_bits@.
foreign import ccall "acb.h acb_rel_accuracy_bits"
  acb_rel_accuracy_bits :: Ptr CAcb -> IO CLong

-- | /acb_rel_one_accuracy_bits/ /x/ 
-- 
-- Given a ball with midpoint /m/ and radius /r/, returns an approximation
-- of the relative accuracy of \([\max(1,|m|) \pm r]\) measured in bits.
foreign import ccall "acb.h acb_rel_one_accuracy_bits"
  acb_rel_one_accuracy_bits :: Ptr CAcb -> IO CLong

-- | /acb_bits/ /x/ 
-- 
-- Returns the maximum of /arb_bits/ applied to the real and imaginary
-- parts of /x/, i.e. the minimum precision sufficient to represent /x/
-- exactly.
foreign import ccall "acb.h acb_bits"
  acb_bits :: Ptr CAcb -> IO CLong

-- | /acb_indeterminate/ /x/ 
-- 
-- Sets /x/ to
-- \([\operatorname{NaN} \pm \infty] + [\operatorname{NaN} \pm \infty]i\),
-- representing an indeterminate result.
foreign import ccall "acb.h acb_indeterminate"
  acb_indeterminate :: Ptr CAcb -> IO ()

-- | /acb_trim/ /y/ /x/ 
-- 
-- Sets /y/ to a a copy of /x/ with both the real and imaginary parts
-- trimmed (see @arb_trim@).
foreign import ccall "acb.h acb_trim"
  acb_trim :: Ptr CAcb -> Ptr CAcb -> IO ()

-- | /acb_is_real/ /x/ 
-- 
-- Returns nonzero iff the imaginary part of /x/ is zero. It does not test
-- whether the real part of /x/ also is finite.
foreign import ccall "acb.h acb_is_real"
  acb_is_real :: Ptr CAcb -> IO CInt

-- | /acb_get_unique_fmpz/ /z/ /x/ 
-- 
-- If /x/ contains a unique integer, sets /z/ to that value and returns
-- nonzero. Otherwise (if /x/ represents no integers or more than one
-- integer), returns zero.
foreign import ccall "acb.h acb_get_unique_fmpz"
  acb_get_unique_fmpz :: Ptr CFmpz -> Ptr CAcb -> IO CInt

-- Complex parts ---------------------------------------------------------------

-- | /acb_get_real/ /re/ /z/ 
-- 
-- Sets /re/ to the real part of /z/.
foreign import ccall "acb.h acb_get_real"
  acb_get_real :: Ptr CArb -> Ptr CAcb -> IO ()

-- | /acb_get_imag/ /im/ /z/ 
-- 
-- Sets /im/ to the imaginary part of /z/.
foreign import ccall "acb.h acb_get_imag"
  acb_get_imag :: Ptr CArb -> Ptr CAcb -> IO ()

-- | /acb_arg/ /r/ /z/ /prec/ 
-- 
-- Sets /r/ to a real interval containing the complex argument (phase) of
-- /z/. We define the complex argument have a discontinuity on
-- \((-\infty,0]\), with the special value \(\operatorname{arg}(0) = 0\),
-- and \(\operatorname{arg}(a+0i) = \pi\) for \(a < 0\). Equivalently, if
-- \(z = a+bi\), the argument is given by \(\operatorname{atan2}(b,a)\)
-- (see @arb_atan2@).
foreign import ccall "acb.h acb_arg"
  acb_arg :: Ptr CArb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_abs/ /r/ /z/ /prec/ 
-- 
-- Sets /r/ to the absolute value of /z/.
foreign import ccall "acb.h acb_abs"
  acb_abs :: Ptr CArb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_sgn/ /r/ /z/ /prec/ 
-- 
-- Sets /r/ to the complex sign of /z/, defined as 0 if /z/ is exactly zero
-- and the projection onto the unit circle \(z / |z| = \exp(i \arg(z))\)
-- otherwise.
foreign import ccall "acb.h acb_sgn"
  acb_sgn :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_csgn/ /r/ /z/ 
-- 
-- Sets /r/ to the extension of the real sign function taking the value 1
-- for /z/ strictly in the right half plane, -1 for /z/ strictly in the
-- left half plane, and the sign of the imaginary part when /z/ is on the
-- imaginary axis. Equivalently,
-- \(\operatorname{csgn}(z) = z / \sqrt{z^2}\) except that the value is 0
-- when /z/ is exactly zero.
foreign import ccall "acb.h acb_csgn"
  acb_csgn :: Ptr CArb -> Ptr CAcb -> IO ()

-- Arithmetic ------------------------------------------------------------------

foreign import ccall "acb.h acb_neg"
  acb_neg :: Ptr CAcb -> Ptr CAcb -> IO ()

-- | /acb_neg_round/ /z/ /x/ /prec/ 
-- 
-- Sets /z/ to the negation of /x/.
foreign import ccall "acb.h acb_neg_round"
  acb_neg_round :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_conj/ /z/ /x/ 
-- 
-- Sets /z/ to the complex conjugate of /x/.
foreign import ccall "acb.h acb_conj"
  acb_conj :: Ptr CAcb -> Ptr CAcb -> IO ()

foreign import ccall "acb.h acb_add_ui"
  acb_add_ui :: Ptr CAcb -> Ptr CAcb -> CULong -> CLong -> IO ()

foreign import ccall "acb.h acb_add_si"
  acb_add_si :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

foreign import ccall "acb.h acb_add_fmpz"
  acb_add_fmpz :: Ptr CAcb -> Ptr CAcb -> Ptr CFmpz -> CLong -> IO ()

foreign import ccall "acb.h acb_add_arb"
  acb_add_arb :: Ptr CAcb -> Ptr CAcb -> Ptr CArb -> CLong -> IO ()

-- | /acb_add/ /z/ /x/ /y/ /prec/ 
-- 
-- Sets /z/ to the sum of /x/ and /y/.
foreign import ccall "acb.h acb_add"
  acb_add :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

foreign import ccall "acb.h acb_sub_ui"
  acb_sub_ui :: Ptr CAcb -> Ptr CAcb -> CULong -> CLong -> IO ()

foreign import ccall "acb.h acb_sub_si"
  acb_sub_si :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

foreign import ccall "acb.h acb_sub_fmpz"
  acb_sub_fmpz :: Ptr CAcb -> Ptr CAcb -> Ptr CFmpz -> CLong -> IO ()

foreign import ccall "acb.h acb_sub_arb"
  acb_sub_arb :: Ptr CAcb -> Ptr CAcb -> Ptr CArb -> CLong -> IO ()

-- | /acb_sub/ /z/ /x/ /y/ /prec/ 
-- 
-- Sets /z/ to the difference of /x/ and /y/.
foreign import ccall "acb.h acb_sub"
  acb_sub :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_mul_onei/ /z/ /x/ 
-- 
-- Sets /z/ to /x/ multiplied by the imaginary unit.
foreign import ccall "acb.h acb_mul_onei"
  acb_mul_onei :: Ptr CAcb -> Ptr CAcb -> IO ()

-- | /acb_div_onei/ /z/ /x/ 
-- 
-- Sets /z/ to /x/ divided by the imaginary unit.
foreign import ccall "acb.h acb_div_onei"
  acb_div_onei :: Ptr CAcb -> Ptr CAcb -> IO ()

foreign import ccall "acb.h acb_mul_ui"
  acb_mul_ui :: Ptr CAcb -> Ptr CAcb -> CULong -> CLong -> IO ()

foreign import ccall "acb.h acb_mul_si"
  acb_mul_si :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

foreign import ccall "acb.h acb_mul_fmpz"
  acb_mul_fmpz :: Ptr CAcb -> Ptr CAcb -> Ptr CFmpz -> CLong -> IO ()

-- | /acb_mul_arb/ /z/ /x/ /y/ /prec/ 
-- 
-- Sets /z/ to the product of /x/ and /y/.
foreign import ccall "acb.h acb_mul_arb"
  acb_mul_arb :: Ptr CAcb -> Ptr CAcb -> Ptr CArb -> CLong -> IO ()

-- | /acb_mul/ /z/ /x/ /y/ /prec/ 
-- 
-- Sets /z/ to the product of /x/ and /y/. If at least one part of /x/ or
-- /y/ is zero, the operations is reduced to two real multiplications. If
-- /x/ and /y/ are the same pointers, they are assumed to represent the
-- same mathematical quantity and the squaring formula is used.
foreign import ccall "acb.h acb_mul"
  acb_mul :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

foreign import ccall "acb.h acb_mul_2exp_si"
  acb_mul_2exp_si :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_mul_2exp_fmpz/ /z/ /x/ /e/ 
-- 
-- Sets /z/ to /x/ multiplied by \(2^e\), without rounding.
foreign import ccall "acb.h acb_mul_2exp_fmpz"
  acb_mul_2exp_fmpz :: Ptr CAcb -> Ptr CAcb -> Ptr CFmpz -> IO ()

-- | /acb_sqr/ /z/ /x/ /prec/ 
-- 
-- Sets /z/ to /x/ squared.
foreign import ccall "acb.h acb_sqr"
  acb_sqr :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_cube/ /z/ /x/ /prec/ 
-- 
-- Sets /z/ to /x/ cubed, computed efficiently using two real squarings,
-- two real multiplications, and scalar operations.
foreign import ccall "acb.h acb_cube"
  acb_cube :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

foreign import ccall "acb.h acb_addmul"
  acb_addmul :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

foreign import ccall "acb.h acb_addmul_ui"
  acb_addmul_ui :: Ptr CAcb -> Ptr CAcb -> CULong -> CLong -> IO ()

foreign import ccall "acb.h acb_addmul_si"
  acb_addmul_si :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

foreign import ccall "acb.h acb_addmul_fmpz"
  acb_addmul_fmpz :: Ptr CAcb -> Ptr CAcb -> Ptr CFmpz -> CLong -> IO ()

-- | /acb_addmul_arb/ /z/ /x/ /y/ /prec/ 
-- 
-- Sets /z/ to /z/ plus the product of /x/ and /y/.
foreign import ccall "acb.h acb_addmul_arb"
  acb_addmul_arb :: Ptr CAcb -> Ptr CAcb -> Ptr CArb -> CLong -> IO ()

foreign import ccall "acb.h acb_submul"
  acb_submul :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

foreign import ccall "acb.h acb_submul_ui"
  acb_submul_ui :: Ptr CAcb -> Ptr CAcb -> CULong -> CLong -> IO ()

foreign import ccall "acb.h acb_submul_si"
  acb_submul_si :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

foreign import ccall "acb.h acb_submul_fmpz"
  acb_submul_fmpz :: Ptr CAcb -> Ptr CAcb -> Ptr CFmpz -> CLong -> IO ()

-- | /acb_submul_arb/ /z/ /x/ /y/ /prec/ 
-- 
-- Sets /z/ to /z/ minus the product of /x/ and /y/.
foreign import ccall "acb.h acb_submul_arb"
  acb_submul_arb :: Ptr CAcb -> Ptr CAcb -> Ptr CArb -> CLong -> IO ()

-- | /acb_inv/ /z/ /x/ /prec/ 
-- 
-- Sets /z/ to the multiplicative inverse of /x/.
foreign import ccall "acb.h acb_inv"
  acb_inv :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

foreign import ccall "acb.h acb_div_ui"
  acb_div_ui :: Ptr CAcb -> Ptr CAcb -> CULong -> CLong -> IO ()

foreign import ccall "acb.h acb_div_si"
  acb_div_si :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

foreign import ccall "acb.h acb_div_fmpz"
  acb_div_fmpz :: Ptr CAcb -> Ptr CAcb -> Ptr CFmpz -> CLong -> IO ()

foreign import ccall "acb.h acb_div_arb"
  acb_div_arb :: Ptr CAcb -> Ptr CAcb -> Ptr CArb -> CLong -> IO ()

-- | /acb_div/ /z/ /x/ /y/ /prec/ 
-- 
-- Sets /z/ to the quotient of /x/ and /y/.
foreign import ccall "acb.h acb_div"
  acb_div :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- Dot product -----------------------------------------------------------------

-- | /acb_dot_precise/ /res/ /s/ /subtract/ /x/ /xstep/ /y/ /ystep/ /len/ /prec/ 
-- 
-- Computes the dot product of the vectors /x/ and /y/, setting /res/ to
-- \(s + (-1)^{subtract} \sum_{i=0}^{len-1} x_i y_i\).
-- 
-- The initial term /s/ is optional and can be omitted by passing /NULL/
-- (equivalently, \(s = 0\)). The parameter /subtract/ must be 0 or 1. The
-- length /len/ is allowed to be negative, which is equivalent to a length
-- of zero. The parameters /xstep/ or /ystep/ specify a step length for
-- traversing subsequences of the vectors /x/ and /y/; either can be
-- negative to step in the reverse direction starting from the initial
-- pointer. Aliasing is allowed between /res/ and /s/ but not between /res/
-- and the entries of /x/ and /y/.
-- 
-- The default version determines the optimal precision for each term and
-- performs all internal calculations using mpn arithmetic with minimal
-- overhead. This is the preferred way to compute a dot product; it is
-- generally much faster and more precise than a simple loop.
-- 
-- The /simple/ version performs fused multiply-add operations in a simple
-- loop. This can be used for testing purposes and is also used as a
-- fallback by the default version when the exponents are out of range for
-- the optimized code.
-- 
-- The /precise/ version computes the dot product exactly up to the final
-- rounding. This can be extremely slow and is only intended for testing.
foreign import ccall "acb.h acb_dot_precise"
  acb_dot_precise :: Ptr CAcb -> Ptr CAcb -> CInt -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

-- | /acb_approx_dot/ /res/ /s/ /subtract/ /x/ /xstep/ /y/ /ystep/ /len/ /prec/ 
-- 
-- Computes an approximate dot product /without error bounds/. The radii of
-- the inputs are ignored (only the midpoints are read) and only the
-- midpoint of the output is written.
foreign import ccall "acb.h acb_approx_dot"
  acb_approx_dot :: Ptr CAcb -> Ptr CAcb -> CInt -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

-- | /acb_dot_ui/ /res/ /initial/ /subtract/ /x/ /xstep/ /y/ /ystep/ /len/ /prec/ 
-- 
-- Equivalent to @acb_dot@, but with integers in the array /y/. The /uiui/
-- and /siui/ versions take an array of double-limb integers as input; the
-- /siui/ version assumes that these represent signed integers in two\'s
-- complement form.
foreign import ccall "acb.h acb_dot_ui"
  acb_dot_ui :: Ptr CAcb -> Ptr CAcb -> CInt -> Ptr CAcb -> CLong -> Ptr CULong -> CLong -> CLong -> CLong -> IO ()

-- Mathematical constants ------------------------------------------------------

-- | /acb_const_pi/ /y/ /prec/ 
-- 
-- Sets /y/ to the constant \(\pi\).
foreign import ccall "acb.h acb_const_pi"
  acb_const_pi :: Ptr CAcb -> CLong -> IO ()

-- Powers and roots ------------------------------------------------------------

-- | /acb_sqrt/ /r/ /z/ /prec/ 
-- 
-- Sets /r/ to the square root of /z/. If either the real or imaginary part
-- is exactly zero, only a single real square root is needed. Generally, we
-- use the formula \(\sqrt{a+bi} = u/2 + ib/u, u = \sqrt{2(|a+bi|+a)}\),
-- requiring two real square root extractions.
foreign import ccall "acb.h acb_sqrt"
  acb_sqrt :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_sqrt_analytic/ /r/ /z/ /analytic/ /prec/ 
-- 
-- Computes the square root. If /analytic/ is set, gives a NaN-containing
-- result if /z/ touches the branch cut.
foreign import ccall "acb.h acb_sqrt_analytic"
  acb_sqrt_analytic :: Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /acb_rsqrt/ /r/ /z/ /prec/ 
-- 
-- Sets /r/ to the reciprocal square root of /z/. If either the real or
-- imaginary part is exactly zero, only a single real reciprocal square
-- root is needed. Generally, we use the formula
-- \(1/\sqrt{a+bi} = ((a+r) - bi)/v, r = |a+bi|, v = \sqrt{r |a+bi+r|^2}\),
-- requiring one real square root and one real reciprocal square root.
foreign import ccall "acb.h acb_rsqrt"
  acb_rsqrt :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_rsqrt_analytic/ /r/ /z/ /analytic/ /prec/ 
-- 
-- Computes the reciprocal square root. If /analytic/ is set, gives a
-- NaN-containing result if /z/ touches the branch cut.
foreign import ccall "acb.h acb_rsqrt_analytic"
  acb_rsqrt_analytic :: Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /acb_quadratic_roots_fmpz/ /r1/ /r2/ /a/ /b/ /c/ /prec/ 
-- 
-- Sets /r1/ and /r2/ to the roots of the quadratic polynomial
-- \(ax^2 + bx + c\). Requires that /a/ is nonzero. This function is
-- implemented so that both roots are computed accurately even when direct
-- use of the quadratic formula would lose accuracy.
foreign import ccall "acb.h acb_quadratic_roots_fmpz"
  acb_quadratic_roots_fmpz :: Ptr CAcb -> Ptr CAcb -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- | /acb_root_ui/ /r/ /z/ /k/ /prec/ 
-- 
-- Sets /r/ to the principal /k/-th root of /z/.
foreign import ccall "acb.h acb_root_ui"
  acb_root_ui :: Ptr CAcb -> Ptr CAcb -> CULong -> CLong -> IO ()

foreign import ccall "acb.h acb_pow_fmpz"
  acb_pow_fmpz :: Ptr CAcb -> Ptr CAcb -> Ptr CFmpz -> CLong -> IO ()

foreign import ccall "acb.h acb_pow_ui"
  acb_pow_ui :: Ptr CAcb -> Ptr CAcb -> CULong -> CLong -> IO ()

-- | /acb_pow_si/ /y/ /b/ /e/ /prec/ 
-- 
-- Sets \(y = b^e\) using binary exponentiation (with an initial division
-- if \(e < 0\)). Note that these functions can get slow if the exponent is
-- extremely large (in such cases @acb_pow@ may be superior).
foreign import ccall "acb.h acb_pow_si"
  acb_pow_si :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

foreign import ccall "acb.h acb_pow_arb"
  acb_pow_arb :: Ptr CAcb -> Ptr CAcb -> Ptr CArb -> CLong -> IO ()

-- | /acb_pow/ /z/ /x/ /y/ /prec/ 
-- 
-- Sets \(z = x^y\), computed using binary exponentiation if \(y\) if a
-- small exact integer, as \(z = (x^{1/2})^{2y}\) if \(y\) is a small exact
-- half-integer, and generally as \(z = \exp(y \log x)\).
foreign import ccall "acb.h acb_pow"
  acb_pow :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_pow_analytic/ /r/ /x/ /y/ /analytic/ /prec/ 
-- 
-- Computes the power \(x^y\). If /analytic/ is set, gives a NaN-containing
-- result if /x/ touches the branch cut (unless /y/ is an integer).
foreign import ccall "acb.h acb_pow_analytic"
  acb_pow_analytic :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /acb_unit_root/ /res/ /order/ /prec/ 
-- 
-- Sets /res/ to \(\exp(\frac{2i\pi}{\mathrm{order}})\) to precision
-- /prec/.
foreign import ccall "acb.h acb_unit_root"
  acb_unit_root :: Ptr CAcb -> CULong -> CLong -> IO ()

-- Exponentials and logarithms -------------------------------------------------

-- | /acb_exp/ /y/ /z/ /prec/ 
-- 
-- Sets /y/ to the exponential function of /z/, computed as
-- \(\exp(a+bi) = \exp(a) \left( \cos(b) + \sin(b) i \right)\).
foreign import ccall "acb.h acb_exp"
  acb_exp :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_exp_pi_i/ /y/ /z/ /prec/ 
-- 
-- Sets /y/ to \(\exp(\pi i z)\).
foreign import ccall "acb.h acb_exp_pi_i"
  acb_exp_pi_i :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_exp_invexp/ /s/ /t/ /z/ /prec/ 
-- 
-- Sets \(s = \exp(z)\) and \(t = \exp(-z)\).
foreign import ccall "acb.h acb_exp_invexp"
  acb_exp_invexp :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_expm1/ /res/ /z/ /prec/ 
-- 
-- Sets /res/ to \(\exp(z)-1\), using a more accurate method when
-- \(z \approx 0\).
foreign import ccall "acb.h acb_expm1"
  acb_expm1 :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_log/ /y/ /z/ /prec/ 
-- 
-- Sets /y/ to the principal branch of the natural logarithm of /z/,
-- computed as
-- \(\log(a+bi) = \frac{1}{2} \log(a^2 + b^2) + i \operatorname{arg}(a+bi)\).
foreign import ccall "acb.h acb_log"
  acb_log :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_log_analytic/ /r/ /z/ /analytic/ /prec/ 
-- 
-- Computes the natural logarithm. If /analytic/ is set, gives a
-- NaN-containing result if /z/ touches the branch cut.
foreign import ccall "acb.h acb_log_analytic"
  acb_log_analytic :: Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /acb_log1p/ /z/ /x/ /prec/ 
-- 
-- Sets \(z = \log(1+x)\), computed accurately when \(x \approx 0\).
foreign import ccall "acb.h acb_log1p"
  acb_log1p :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- Trigonometric functions -----------------------------------------------------

foreign import ccall "acb.h acb_sin"
  acb_sin :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

foreign import ccall "acb.h acb_cos"
  acb_cos :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_sin_cos/ /s/ /c/ /z/ /prec/ 
-- 
-- Sets \(s = \sin(z)\), \(c = \cos(z)\), evaluated as
-- \(\sin(a+bi) = \sin(a)\cosh(b) + i \cos(a)\sinh(b)\),
-- \(\cos(a+bi) = \cos(a)\cosh(b) - i \sin(a)\sinh(b)\).
foreign import ccall "acb.h acb_sin_cos"
  acb_sin_cos :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_tan/ /s/ /z/ /prec/ 
-- 
-- Sets \(s = \tan(z) = \sin(z) / \cos(z)\). For large imaginary parts, the
-- function is evaluated in a numerically stable way as \(\pm i\) plus a
-- decreasing exponential factor.
foreign import ccall "acb.h acb_tan"
  acb_tan :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_cot/ /s/ /z/ /prec/ 
-- 
-- Sets \(s = \cot(z) = \cos(z) / \sin(z)\). For large imaginary parts, the
-- function is evaluated in a numerically stable way as \(\pm i\) plus a
-- decreasing exponential factor.
foreign import ccall "acb.h acb_cot"
  acb_cot :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

foreign import ccall "acb.h acb_sin_pi"
  acb_sin_pi :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

foreign import ccall "acb.h acb_cos_pi"
  acb_cos_pi :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_sin_cos_pi/ /s/ /c/ /z/ /prec/ 
-- 
-- Sets \(s = \sin(\pi z)\), \(c = \cos(\pi z)\), evaluating the
-- trigonometric factors of the real and imaginary part accurately via
-- @arb_sin_cos_pi@.
foreign import ccall "acb.h acb_sin_cos_pi"
  acb_sin_cos_pi :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_tan_pi/ /s/ /z/ /prec/ 
-- 
-- Sets \(s = \tan(\pi z)\). Uses the same algorithm as @acb_tan@, but
-- evaluates the sine and cosine accurately via @arb_sin_cos_pi@.
foreign import ccall "acb.h acb_tan_pi"
  acb_tan_pi :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_cot_pi/ /s/ /z/ /prec/ 
-- 
-- Sets \(s = \cot(\pi z)\). Uses the same algorithm as @acb_cot@, but
-- evaluates the sine and cosine accurately via @arb_sin_cos_pi@.
foreign import ccall "acb.h acb_cot_pi"
  acb_cot_pi :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_sec/ /res/ /z/ /prec/ 
-- 
-- Computes \(\sec(z) = 1 / \cos(z)\).
foreign import ccall "acb.h acb_sec"
  acb_sec :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_csc/ /res/ /z/ /prec/ 
-- 
-- Computes \(\csc(x) = 1 / \sin(z)\).
foreign import ccall "acb.h acb_csc"
  acb_csc :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_csc_pi/ /res/ /z/ /prec/ 
-- 
-- Computes \(\csc(\pi x) = 1 / \sin(\pi z)\). Evaluates the sine
-- accurately via @acb_sin_pi@.
foreign import ccall "acb.h acb_csc_pi"
  acb_csc_pi :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_sinc/ /s/ /z/ /prec/ 
-- 
-- Sets \(s = \operatorname{sinc}(x) = \sin(z) / z\).
foreign import ccall "acb.h acb_sinc"
  acb_sinc :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_sinc_pi/ /s/ /z/ /prec/ 
-- 
-- Sets \(s = \operatorname{sinc}(\pi x) = \sin(\pi z) / (\pi z)\).
foreign import ccall "acb.h acb_sinc_pi"
  acb_sinc_pi :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- Inverse trigonometric functions ---------------------------------------------

-- | /acb_asin/ /res/ /z/ /prec/ 
-- 
-- Sets /res/ to \(\operatorname{asin}(z) = -i \log(iz + \sqrt{1-z^2})\).
foreign import ccall "acb.h acb_asin"
  acb_asin :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_acos/ /res/ /z/ /prec/ 
-- 
-- Sets /res/ to
-- \(\operatorname{acos}(z) = \tfrac{1}{2} \pi - \operatorname{asin}(z)\).
foreign import ccall "acb.h acb_acos"
  acb_acos :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_atan/ /res/ /z/ /prec/ 
-- 
-- Sets /res/ to
-- \(\operatorname{atan}(z) = \tfrac{1}{2} i (\log(1-iz)-\log(1+iz))\).
foreign import ccall "acb.h acb_atan"
  acb_atan :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- Hyperbolic functions --------------------------------------------------------

foreign import ccall "acb.h acb_sinh"
  acb_sinh :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

foreign import ccall "acb.h acb_cosh"
  acb_cosh :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

foreign import ccall "acb.h acb_sinh_cosh"
  acb_sinh_cosh :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

foreign import ccall "acb.h acb_tanh"
  acb_tanh :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_coth/ /s/ /z/ /prec/ 
-- 
-- Respectively computes \(\sinh(z) = -i\sin(iz)\),
-- \(\cosh(z) = \cos(iz)\), \(\tanh(z) = -i\tan(iz)\),
-- \(\coth(z) = i\cot(iz)\).
foreign import ccall "acb.h acb_coth"
  acb_coth :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_sech/ /res/ /z/ /prec/ 
-- 
-- Computes \(\operatorname{sech}(z) = 1 / \cosh(z)\).
foreign import ccall "acb.h acb_sech"
  acb_sech :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_csch/ /res/ /z/ /prec/ 
-- 
-- Computes \(\operatorname{csch}(z) = 1 / \sinh(z)\).
foreign import ccall "acb.h acb_csch"
  acb_csch :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- Inverse hyperbolic functions ------------------------------------------------

-- | /acb_asinh/ /res/ /z/ /prec/ 
-- 
-- Sets /res/ to \(\operatorname{asinh}(z) = -i \operatorname{asin}(iz)\).
foreign import ccall "acb.h acb_asinh"
  acb_asinh :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_acosh/ /res/ /z/ /prec/ 
-- 
-- Sets /res/ to
-- \(\operatorname{acosh}(z) = \log(z + \sqrt{z+1} \sqrt{z-1})\).
foreign import ccall "acb.h acb_acosh"
  acb_acosh :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_atanh/ /res/ /z/ /prec/ 
-- 
-- Sets /res/ to \(\operatorname{atanh}(z) = -i \operatorname{atan}(iz)\).
foreign import ccall "acb.h acb_atanh"
  acb_atanh :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- Lambert W function ----------------------------------------------------------

-- | /acb_lambertw_asymp/ /res/ /z/ /k/ /L/ /M/ /prec/ 
-- 
-- Sets /res/ to the Lambert W function \(W_k(z)\) computed using /L/ and
-- /M/ terms in the bivariate series giving the asymptotic expansion at
-- zero or infinity. This algorithm is valid everywhere, but the error
-- bound is only finite when \(|\log(z)|\) is sufficiently large.
foreign import ccall "acb.h acb_lambertw_asymp"
  acb_lambertw_asymp :: Ptr CAcb -> Ptr CAcb -> Ptr CFmpz -> CLong -> CLong -> CLong -> IO ()

-- | /acb_lambertw_check_branch/ /w/ /k/ /prec/ 
-- 
-- Tests if /w/ definitely lies in the image of the branch \(W_k(z)\). This
-- function is used internally to verify that a computed approximation of
-- the Lambert W function lies on the intended branch. Note that this will
-- necessarily evaluate to false for points exactly on (or overlapping) the
-- branch cuts, where a different algorithm has to be used.
foreign import ccall "acb.h acb_lambertw_check_branch"
  acb_lambertw_check_branch :: Ptr CAcb -> Ptr CFmpz -> CLong -> IO CInt

-- | /acb_lambertw_bound_deriv/ /res/ /z/ /ez1/ /k/ 
-- 
-- Sets /res/ to an upper bound for \(|W_k'(z)|\). The input /ez1/ should
-- contain the precomputed value of \(ez+1\).
-- 
-- Along the real line, the directional derivative of \(W_k(z)\) is
-- understood to be taken. As a result, the user must handle the branch cut
-- discontinuity separately when using this function to bound perturbations
-- in the value of \(W_k(z)\).
foreign import ccall "acb.h acb_lambertw_bound_deriv"
  acb_lambertw_bound_deriv :: Ptr CMag -> Ptr CAcb -> Ptr CAcb -> Ptr CFmpz -> IO ()

-- | /acb_lambertw/ /res/ /z/ /k/ /flags/ /prec/ 
-- 
-- Sets /res/ to the Lambert W function \(W_k(z)\) where the index /k/
-- selects the branch (with \(k = 0\) giving the principal branch). The
-- placement of branch cuts follows < [CGHJK1996]>.
-- 
-- If /flags/ is nonzero, nonstandard branch cuts are used.
-- 
-- If /flags/ is set to /ACB_LAMBERTW_LEFT/, computes
-- \(W_{\mathrm{left}|k}(z)\) which corresponds to \(W_k(z)\) in the upper
-- half plane and \(W_{k+1}(z)\) in the lower half plane, connected
-- continuously to the left of the branch points. In other words, the
-- branch cut on \((-\infty,0)\) is rotated counterclockwise to
-- \((0,+\infty)\). (For \(k = -1\) and \(k = 0\), there is also a branch
-- cut on \((-1/e,0)\), continuous from below instead of from above to
-- maintain counterclockwise continuity.)
-- 
-- If /flags/ is set to /ACB_LAMBERTW_MIDDLE/, computes
-- \(W_{\mathrm{middle}}(z)\) which corresponds to \(W_{-1}(z)\) in the
-- upper half plane and \(W_{1}(z)\) in the lower half plane, connected
-- continuously through \((-1/e,0)\) with branch cuts on \((-\infty,-1/e)\)
-- and \((0,+\infty)\). \(W_{\mathrm{middle}}(z)\) extends the real
-- analytic function \(W_{-1}(x)\) defined on \((-1/e,0)\) to a complex
-- analytic function, whereas the standard branch \(W_{-1}(z)\) has a
-- branch cut along the real segment.
-- 
-- The algorithm used to compute the Lambert W function is described in
-- < [Joh2017b]>.
foreign import ccall "acb.h acb_lambertw"
  acb_lambertw :: Ptr CAcb -> Ptr CAcb -> Ptr CFmpz -> CInt -> CLong -> IO ()

-- Rising factorials -----------------------------------------------------------

-- | /acb_rising_ui/ /z/ /x/ /n/ /prec/ 
-- 
-- Computes the rising factorial \(z = x (x+1) (x+2) \cdots (x+n-1)\).
-- These functions are aliases for @acb_hypgeom_rising_ui@ and
-- @acb_hypgeom_rising@.
foreign import ccall "acb.h acb_rising_ui"
  acb_rising_ui :: Ptr CAcb -> Ptr CAcb -> CULong -> CLong -> IO ()







-- Gamma function --------------------------------------------------------------

-- | /acb_gamma/ /y/ /x/ /prec/ 
-- 
-- Computes the gamma function \(y = \Gamma(x)\). This is an alias for
-- @acb_hypgeom_gamma@.
foreign import ccall "acb.h acb_gamma"
  acb_gamma :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_rgamma/ /y/ /x/ /prec/ 
-- 
-- Computes the reciprocal gamma function \(y = 1/\Gamma(x)\), avoiding
-- division by zero at the poles of the gamma function. This is an alias
-- for @acb_hypgeom_rgamma@.
foreign import ccall "acb.h acb_rgamma"
  acb_rgamma :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_lgamma/ /y/ /x/ /prec/ 
-- 
-- Computes the logarithmic gamma function \(y = \log \Gamma(x)\). This is
-- an alias for @acb_hypgeom_lgamma@.
-- 
-- The branch cut of the logarithmic gamma function is placed on the
-- negative half-axis, which means that
-- \(\log \Gamma(z) + \log z = \log \Gamma(z+1)\) holds for all \(z\),
-- whereas \(\log \Gamma(z) \ne \log(\Gamma(z))\) in general. In the left
-- half plane, the reflection formula with correct branch structure is
-- evaluated via @acb_log_sin_pi@.
foreign import ccall "acb.h acb_lgamma"
  acb_lgamma :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_digamma/ /y/ /x/ /prec/ 
-- 
-- Computes the digamma function
-- \(y = \psi(x) = (\log \Gamma(x))' = \Gamma'(x) / \Gamma(x)\).
foreign import ccall "acb.h acb_digamma"
  acb_digamma :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_log_sin_pi/ /res/ /z/ /prec/ 
-- 
-- Computes the logarithmic sine function defined by
-- 
-- \[`\]
-- \[S(z) = \log(\pi) - \log \Gamma(z) + \log \Gamma(1-z)\]
-- 
-- which is equal to
-- 
-- \[`\]
-- \[S(z) = \int_{1/2}^z \pi \cot(\pi t) dt\]
-- 
-- where the path of integration goes through the upper half plane if
-- \(0 < \arg(z) \le \pi\) and through the lower half plane if
-- \(-\pi < \arg(z) \le 0\). Equivalently,
-- 
-- \[`\]
-- \[S(z) = \log(\sin(\pi(z-n))) \mp n \pi i, \quad n = \lfloor \operatorname{re}(z) \rfloor\]
-- 
-- where the negative sign is taken if \(0 < \arg(z) \le \pi\) and the
-- positive sign is taken otherwise (if the interval \(\arg(z)\) does not
-- certainly satisfy either condition, the union of both cases is
-- computed). After subtracting /n/, we have
-- \(0 \le \operatorname{re}(z) < 1\). In this strip, we use use
-- \(S(z) = \log(\sin(\pi(z)))\) if the imaginary part of /z/ is small.
-- Otherwise, we use \(S(z) = i \pi (z-1/2) + \log((1+e^{-2i\pi z})/2)\) in
-- the lower half-plane and the conjugated expression in the upper
-- half-plane to avoid exponent overflow.
-- 
-- The function is evaluated at the midpoint and the propagated error is
-- computed from \(S'(z)\) to get a continuous change when \(z\) is
-- non-real and \(n\) spans more than one possible integer value.
foreign import ccall "acb.h acb_log_sin_pi"
  acb_log_sin_pi :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_polygamma/ /res/ /s/ /z/ /prec/ 
-- 
-- Sets /res/ to the value of the generalized polygamma function
-- \(\psi(s,z)\).
-- 
-- If /s/ is a nonnegative order, this is simply the /s/-order derivative
-- of the digamma function. If \(s = 0\), this function simply calls the
-- digamma function internally. For integers \(s \ge 1\), it calls the
-- Hurwitz zeta function. Note that for small integers \(s \ge 1\), it can
-- be faster to use @acb_poly_digamma_series@ and read off the
-- coefficients.
-- 
-- The generalization to other values of /s/ is due to Espinosa and Moll
-- < [EM2004]>:
-- 
-- \[`\]
-- \[\psi(s,z) = \frac{\zeta'(s+1,z) + (\gamma + \psi(-s)) \zeta(s+1,z)}{\Gamma(-s)}\]
foreign import ccall "acb.h acb_polygamma"
  acb_polygamma :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

foreign import ccall "acb.h acb_barnes_g"
  acb_barnes_g :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_log_barnes_g/ /res/ /z/ /prec/ 
-- 
-- Computes Barnes /G/-function or the logarithmic Barnes /G/-function,
-- respectively. The logarithmic version has branch cuts on the negative
-- real axis and is continuous elsewhere in the complex plane, in analogy
-- with the logarithmic gamma function. The functional equation
-- 
-- \[`\]
-- \[\log G(z+1) = \log \Gamma(z) + \log G(z).\]
-- 
-- holds for all /z/.
-- 
-- For small integers, we directly use the recurrence relation
-- \(G(z+1) = \Gamma(z) G(z)\) together with the initial value
-- \(G(1) = 1\). For general /z/, we use the formula
-- 
-- \[`\]
-- \[\log G(z) = (z-1) \log \Gamma(z) - \zeta'(-1,z) + \zeta'(-1).\]
foreign import ccall "acb.h acb_log_barnes_g"
  acb_log_barnes_g :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- Zeta function ---------------------------------------------------------------

-- | /acb_zeta/ /z/ /s/ /prec/ 
-- 
-- Sets /z/ to the value of the Riemann zeta function \(\zeta(s)\). Note:
-- for computing derivatives with respect to \(s\), use
-- @acb_poly_zeta_series@ or related methods.
-- 
-- This is a wrapper of @acb_dirichlet_zeta@.
foreign import ccall "acb.h acb_zeta"
  acb_zeta :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_hurwitz_zeta/ /z/ /s/ /a/ /prec/ 
-- 
-- Sets /z/ to the value of the Hurwitz zeta function \(\zeta(s, a)\).
-- Note: for computing derivatives with respect to \(s\), use
-- @acb_poly_zeta_series@ or related methods.
-- 
-- This is a wrapper of @acb_dirichlet_hurwitz@.
foreign import ccall "acb.h acb_hurwitz_zeta"
  acb_hurwitz_zeta :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_bernoulli_poly_ui/ /res/ /n/ /x/ /prec/ 
-- 
-- Sets /res/ to the value of the Bernoulli polynomial \(B_n(x)\).
-- 
-- Warning: this function is only fast if either /n/ or /x/ is a small
-- integer.
-- 
-- This function reads Bernoulli numbers from the global cache if they are
-- already cached, but does not automatically extend the cache by itself.
foreign import ccall "acb.h acb_bernoulli_poly_ui"
  acb_bernoulli_poly_ui :: Ptr CAcb -> CULong -> Ptr CAcb -> CLong -> IO ()

-- Polylogarithms --------------------------------------------------------------

foreign import ccall "acb.h acb_polylog"
  acb_polylog :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_polylog_si/ /w/ /s/ /z/ /prec/ 
-- 
-- Sets /w/ to the polylogarithm \(\operatorname{Li}_s(z)\).
foreign import ccall "acb.h acb_polylog_si"
  acb_polylog_si :: Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> IO ()

-- Arithmetic-geometric mean ---------------------------------------------------

-- See @algorithms_agm@ for implementation details.
--
-- | /acb_agm1/ /m/ /z/ /prec/ 
-- 
-- Sets /m/ to the arithmetic-geometric mean
-- \(M(z) = \operatorname{agm}(1,z)\), defined such that the function is
-- continuous in the complex plane except for a branch cut along the
-- negative half axis (where it is continuous from above). This corresponds
-- to always choosing an \"optimal\" branch for the square root in the
-- arithmetic-geometric mean iteration.
foreign import ccall "acb.h acb_agm1"
  acb_agm1 :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_agm1_cpx/ /m/ /z/ /len/ /prec/ 
-- 
-- Sets the coefficients in the array /m/ to the power series expansion of
-- the arithmetic-geometric mean at the point /z/ truncated to length
-- /len/, i.e. \(M(z+x) \in \mathbb{C}[[x]]\).
foreign import ccall "acb.h acb_agm1_cpx"
  acb_agm1_cpx :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /acb_agm/ /m/ /x/ /y/ /prec/ 
-- 
-- Sets /m/ to the arithmetic-geometric mean of /x/ and /y/. The square
-- roots in the AGM iteration are chosen so as to form the \"optimal\" AGM
-- sequence. This gives a well-defined function of /x/ and /y/ except when
-- \(x / y\) is a negative real number, in which case there are two optimal
-- AGM sequences. In that case, an arbitrary but consistent choice is made
-- (if a decision cannot be made due to inexact arithmetic, the union of
-- both choices is returned).
foreign import ccall "acb.h acb_agm"
  acb_agm :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- Other special functions -----------------------------------------------------

foreign import ccall "acb.h acb_chebyshev_t_ui"
  acb_chebyshev_t_ui :: Ptr CAcb -> CULong -> Ptr CAcb -> CLong -> IO ()

-- | /acb_chebyshev_u_ui/ /a/ /n/ /x/ /prec/ 
-- 
-- Evaluates the Chebyshev polynomial of the first kind \(a = T_n(x)\) or
-- the Chebyshev polynomial of the second kind \(a = U_n(x)\).
foreign import ccall "acb.h acb_chebyshev_u_ui"
  acb_chebyshev_u_ui :: Ptr CAcb -> CULong -> Ptr CAcb -> CLong -> IO ()

foreign import ccall "acb.h acb_chebyshev_t2_ui"
  acb_chebyshev_t2_ui :: Ptr CAcb -> Ptr CAcb -> CULong -> Ptr CAcb -> CLong -> IO ()

-- | /acb_chebyshev_u2_ui/ /a/ /b/ /n/ /x/ /prec/ 
-- 
-- Simultaneously evaluates \(a = T_n(x), b = T_{n-1}(x)\) or
-- \(a = U_n(x), b = U_{n-1}(x)\). Aliasing between /a/, /b/ and /x/ is not
-- permitted.
foreign import ccall "acb.h acb_chebyshev_u2_ui"
  acb_chebyshev_u2_ui :: Ptr CAcb -> Ptr CAcb -> CULong -> Ptr CAcb -> CLong -> IO ()

-- Piecewise real functions ----------------------------------------------------

-- The following methods extend common piecewise real functions to
-- piecewise complex analytic functions, useful together with the
-- @acb_calc.h \<acb-calc>@ module. If /analytic/ is set, evaluation on a
-- discontinuity or non-analytic point gives a NaN result.
--
-- | /acb_real_abs/ /res/ /z/ /analytic/ /prec/ 
-- 
-- The absolute value is extended to \(+z\) in the right half plane and
-- \(-z\) in the left half plane, with a discontinuity on the vertical line
-- \(\operatorname{Re}(z) = 0\).
foreign import ccall "acb.h acb_real_abs"
  acb_real_abs :: Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /acb_real_sgn/ /res/ /z/ /analytic/ /prec/ 
-- 
-- The sign function is extended to \(+1\) in the right half plane and
-- \(-1\) in the left half plane, with a discontinuity on the vertical line
-- \(\operatorname{Re}(z) = 0\). If /analytic/ is not set, this is
-- effectively the same function as @acb_csgn@.
foreign import ccall "acb.h acb_real_sgn"
  acb_real_sgn :: Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /acb_real_heaviside/ /res/ /z/ /analytic/ /prec/ 
-- 
-- The Heaviside step function (or unit step function) is extended to
-- \(+1\) in the right half plane and \(0\) in the left half plane, with a
-- discontinuity on the vertical line \(\operatorname{Re}(z) = 0\).
foreign import ccall "acb.h acb_real_heaviside"
  acb_real_heaviside :: Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /acb_real_floor/ /res/ /z/ /analytic/ /prec/ 
-- 
-- The floor function is extended to a piecewise constant function equal to
-- \(n\) in the strips with real part \((n,n+1)\), with discontinuities on
-- the vertical lines \(\operatorname{Re}(z) = n\).
foreign import ccall "acb.h acb_real_floor"
  acb_real_floor :: Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /acb_real_ceil/ /res/ /z/ /analytic/ /prec/ 
-- 
-- The ceiling function is extended to a piecewise constant function equal
-- to \(n+1\) in the strips with real part \((n,n+1)\), with
-- discontinuities on the vertical lines \(\operatorname{Re}(z) = n\).
foreign import ccall "acb.h acb_real_ceil"
  acb_real_ceil :: Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /acb_real_max/ /res/ /x/ /y/ /analytic/ /prec/ 
-- 
-- The real function \(\max(x,y)\) is extended to a piecewise analytic
-- function of two variables by returning \(x\) when
-- \(\operatorname{Re}(x) \ge \operatorname{Re}(y)\) and returning \(y\)
-- when \(\operatorname{Re}(x) < \operatorname{Re}(y)\), with
-- discontinuities where \(\operatorname{Re}(x) = \operatorname{Re}(y)\).
foreign import ccall "acb.h acb_real_max"
  acb_real_max :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /acb_real_min/ /res/ /x/ /y/ /analytic/ /prec/ 
-- 
-- The real function \(\min(x,y)\) is extended to a piecewise analytic
-- function of two variables by returning \(x\) when
-- \(\operatorname{Re}(x) \le \operatorname{Re}(y)\) and returning \(y\)
-- when \(\operatorname{Re}(x) > \operatorname{Re}(y)\), with
-- discontinuities where \(\operatorname{Re}(x) = \operatorname{Re}(y)\).
foreign import ccall "acb.h acb_real_min"
  acb_real_min :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /acb_real_sqrtpos/ /res/ /z/ /analytic/ /prec/ 
-- 
-- Extends the real square root function on \([0,+\infty)\) to the usual
-- complex square root on the cut plane. Like @arb_sqrtpos@, only the
-- nonnegative part of /z/ is considered if /z/ is purely real and
-- /analytic/ is not set. This is useful for integrating \(\sqrt{f(x)}\)
-- where it is known that \(f(x) \ge 0\): unlike @acb_sqrt_analytic@, no
-- spurious imaginary terms \([\pm \varepsilon] i\) are created when the
-- balls computed for \(f(x)\) straddle zero.
foreign import ccall "acb.h acb_real_sqrtpos"
  acb_real_sqrtpos :: Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- Vector functions ------------------------------------------------------------

-- | /_acb_vec_zero/ /A/ /n/ 
-- 
-- Sets all entries in /vec/ to zero.
foreign import ccall "acb.h _acb_vec_zero"
  _acb_vec_zero :: Ptr CAcb -> CLong -> IO ()

-- | /_acb_vec_is_zero/ /vec/ /len/ 
-- 
-- Returns nonzero iff all entries in /x/ are zero.
foreign import ccall "acb.h _acb_vec_is_zero"
  _acb_vec_is_zero :: Ptr CAcb -> CLong -> IO CInt

-- | /_acb_vec_is_real/ /v/ /len/ 
-- 
-- Returns nonzero iff all entries in /x/ have zero imaginary part.
foreign import ccall "acb.h _acb_vec_is_real"
  _acb_vec_is_real :: Ptr CAcb -> CLong -> IO CInt

-- | /_acb_vec_set/ /res/ /vec/ /len/ 
-- 
-- Sets /res/ to a copy of /vec/.
foreign import ccall "acb.h _acb_vec_set"
  _acb_vec_set :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /_acb_vec_set_round/ /res/ /vec/ /len/ /prec/ 
-- 
-- Sets /res/ to a copy of /vec/, rounding each entry to /prec/ bits.
foreign import ccall "acb.h _acb_vec_set_round"
  _acb_vec_set_round :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /_acb_vec_swap/ /vec1/ /vec2/ /len/ 
-- 
-- Swaps the entries of /vec1/ and /vec2/.
foreign import ccall "acb.h _acb_vec_swap"
  _acb_vec_swap :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

foreign import ccall "acb.h _acb_vec_neg"
  _acb_vec_neg :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

foreign import ccall "acb.h _acb_vec_add"
  _acb_vec_add :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

foreign import ccall "acb.h _acb_vec_sub"
  _acb_vec_sub :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

foreign import ccall "acb.h _acb_vec_scalar_submul"
  _acb_vec_scalar_submul :: Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> IO ()

foreign import ccall "acb.h _acb_vec_scalar_addmul"
  _acb_vec_scalar_addmul :: Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> IO ()

foreign import ccall "acb.h _acb_vec_scalar_mul"
  _acb_vec_scalar_mul :: Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> IO ()

foreign import ccall "acb.h _acb_vec_scalar_mul_ui"
  _acb_vec_scalar_mul_ui :: Ptr CAcb -> Ptr CAcb -> CLong -> CULong -> CLong -> IO ()

foreign import ccall "acb.h _acb_vec_scalar_mul_2exp_si"
  _acb_vec_scalar_mul_2exp_si :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

foreign import ccall "acb.h _acb_vec_scalar_mul_onei"
  _acb_vec_scalar_mul_onei :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

foreign import ccall "acb.h _acb_vec_scalar_div_ui"
  _acb_vec_scalar_div_ui :: Ptr CAcb -> Ptr CAcb -> CLong -> CULong -> CLong -> IO ()

foreign import ccall "acb.h _acb_vec_scalar_div"
  _acb_vec_scalar_div :: Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> IO ()

foreign import ccall "acb.h _acb_vec_scalar_mul_arb"
  _acb_vec_scalar_mul_arb :: Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CArb -> CLong -> IO ()

foreign import ccall "acb.h _acb_vec_scalar_div_arb"
  _acb_vec_scalar_div_arb :: Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CArb -> CLong -> IO ()

foreign import ccall "acb.h _acb_vec_scalar_mul_fmpz"
  _acb_vec_scalar_mul_fmpz :: Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CFmpz -> CLong -> IO ()

-- | /_acb_vec_scalar_div_fmpz/ /res/ /vec/ /len/ /c/ /prec/ 
-- 
-- Performs the respective scalar operation elementwise.
foreign import ccall "acb.h _acb_vec_scalar_div_fmpz"
  _acb_vec_scalar_div_fmpz :: Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CFmpz -> CLong -> IO ()

-- | /_acb_vec_bits/ /vec/ /len/ 
-- 
-- Returns the maximum of @arb_bits@ for all entries in /vec/.
foreign import ccall "acb.h _acb_vec_bits"
  _acb_vec_bits :: Ptr CAcb -> CLong -> IO CLong

-- | /_acb_vec_set_powers/ /xs/ /x/ /len/ /prec/ 
-- 
-- Sets /xs/ to the powers \(1, x, x^2, \ldots, x^{len-1}\).
foreign import ccall "acb.h _acb_vec_set_powers"
  _acb_vec_set_powers :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /_acb_vec_unit_roots/ /z/ /order/ /len/ /prec/ 
-- 
-- Sets /z/ to the powers \(1,z,z^2,\dots z^{\mathrm{len}-1}\) where
-- \(z=\exp(\frac{2i\pi}{\mathrm{order}})\) to precision /prec/. /order/
-- can be taken negative.
-- 
-- In order to avoid precision loss, this function does not simply compute
-- powers of a primitive root.
foreign import ccall "acb.h _acb_vec_unit_roots"
  _acb_vec_unit_roots :: Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

foreign import ccall "acb.h _acb_vec_add_error_arf_vec"
  _acb_vec_add_error_arf_vec :: Ptr CAcb -> Ptr CArf -> CLong -> IO ()

-- | /_acb_vec_add_error_mag_vec/ /res/ /err/ /len/ 
-- 
-- Adds the magnitude of each entry in /err/ to the radius of the
-- corresponding entry in /res/.
foreign import ccall "acb.h _acb_vec_add_error_mag_vec"
  _acb_vec_add_error_mag_vec :: Ptr CAcb -> Ptr CMag -> CLong -> IO ()

-- | /_acb_vec_indeterminate/ /vec/ /len/ 
-- 
-- Applies @acb_indeterminate@ elementwise.
foreign import ccall "acb.h _acb_vec_indeterminate"
  _acb_vec_indeterminate :: Ptr CAcb -> CLong -> IO ()

-- | /_acb_vec_trim/ /res/ /vec/ /len/ 
-- 
-- Applies @acb_trim@ elementwise.
foreign import ccall "acb.h _acb_vec_trim"
  _acb_vec_trim :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /_acb_vec_get_unique_fmpz_vec/ /res/ /vec/ /len/ 
-- 
-- Calls @acb_get_unique_fmpz@ elementwise and returns nonzero if all
-- entries can be rounded uniquely to integers. If any entry in /vec/
-- cannot be rounded uniquely to an integer, returns zero.
foreign import ccall "acb.h _acb_vec_get_unique_fmpz_vec"
  _acb_vec_get_unique_fmpz_vec :: Ptr CFmpz -> Ptr CAcb -> CLong -> IO CInt

-- | /_acb_vec_sort_pretty/ /vec/ /len/ 
-- 
-- Sorts the vector of complex numbers based on the real and imaginary
-- parts. This is intended to reveal structure when printing a set of
-- complex numbers, not to apply an order relation in a rigorous way.
foreign import ccall "acb.h _acb_vec_sort_pretty"
  _acb_vec_sort_pretty :: Ptr CAcb -> CLong -> IO ()

