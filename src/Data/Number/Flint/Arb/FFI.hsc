
module Data.Number.Flint.Arb.FFI (
  -- * Real numbers
    Arb (..)
  , CArb (..)
  , newArb
  , newArbFromFmpz
  , newArbFromFmpq
  , withArb
  , withNewArb
  , withNewArbFromFmpz
  , withNewArbFromFmpq
  -- * Memory management
  , arb_init
  , arb_clear
  , arb_midref
  , _arb_vec_init
  , _arb_vec_clear
  , arb_swap
  , arb_allocated_bytes
  , _arb_vec_allocated_bytes
  , _arb_vec_estimate_allocated_bytes
  -- * Assignment and rounding
  , arb_set
  , arb_set_arf
  , arb_set_si
  , arb_set_ui
  , arb_set_d
  , arb_set_fmpz
  , arb_set_fmpz_2exp
  , arb_set_round
  , arb_set_round_fmpz
  , arb_set_round_fmpz_2exp
  , arb_set_fmpq
  , arb_set_str
  , arb_get_str
  -- * Assignment of special values
  , arb_zero
  , arb_one
  , arb_pos_inf
  , arb_neg_inf
  , arb_zero_pm_inf
  , arb_indeterminate
  , arb_zero_pm_one
  , arb_unit_interval
  -- * Input and output
  , ArbStrOption (..)
  -- | Default print option
  , arb_str_none
  -- | If /arb_str_more/ is added to flags, more (possibly incorrect)
  -- digits may be printed
  , arb_str_more
  -- | If /arb_str_no_radius/ is added to /flags/, the radius is not
  -- included in the output if at least 1 digit of the midpoint can be
  -- printed.
  , arb_str_no_radius
  -- | By adding a multiple m of /arb_str_condense/ to /flags/, strings of
  -- more than three times m consecutive digits are condensed, only
  -- printing the leading and trailing m digits along with brackets
  -- indicating the number of digits omitted (useful when computing
  -- values to extremely high precision).
  , arb_str_condense
  , arb_print
  , arb_fprint
  , arb_printd
  , arb_fprintd
  , arb_printn
  , arb_fprintn
  , arb_dump_str
  , arb_load_str
  , arb_dump_file
  , arb_load_file
  -- * Random number generation
  , arb_randtest
  , arb_randtest_exact
  , arb_randtest_precise
  , arb_randtest_wide
  , arb_randtest_special
  , arb_get_rand_fmpq
  , arb_urandom
  -- * Radius and interval operations
  , arb_get_mid_arb
  , arb_get_rad_arb
  , arb_add_error_arf
  , arb_add_error_mag
  , arb_add_error
  , arb_add_error_2exp_si
  , arb_add_error_2exp_fmpz
  , arb_union
  , arb_intersection
  , arb_nonnegative_part
  , arb_get_abs_ubound_arf
  , arb_get_abs_lbound_arf
  , arb_get_ubound_arf
  , arb_get_lbound_arf
  , arb_get_mag
  , arb_get_mag_lower
  , arb_get_mag_lower_nonnegative
  , arb_get_interval_fmpz_2exp
  , arb_set_interval_mag
  , arb_set_interval_arf
  , arb_set_interval_mpfr
  , arb_set_interval_neg_pos_mag
  , arb_get_interval_arf
  , arb_get_interval_mpfr
  , arb_rel_error_bits
  , arb_rel_accuracy_bits
  , arb_rel_one_accuracy_bits
  , arb_bits
  , arb_trim
  , arb_get_unique_fmpz
  , arb_floor
  , arb_get_fmpz_mid_rad_10exp
  , arb_can_round_arf
  , arb_can_round_mpfr
  -- * Comparisons
  , arb_is_zero
  , arb_is_nonzero
  , arb_is_one
  , arb_is_finite
  , arb_is_exact
  , arb_is_int
  , arb_is_int_2exp_si
  , arb_equal
  , arb_equal_si
  , arb_is_positive
  , arb_is_nonnegative
  , arb_is_negative
  , arb_is_nonpositive
  , arb_overlaps
  , arb_contains_arf
  , arb_contains_fmpq
  , arb_contains_fmpz
  , arb_contains_si
  , arb_contains_mpfr
  , arb_contains
  , arb_contains_int
  , arb_contains_zero
  , arb_contains_negative
  , arb_contains_nonpositive
  , arb_contains_positive
  , arb_contains_nonnegative
  , arb_contains_interior
  , arb_eq
  , arb_ne
  , arb_lt
  , arb_le
  , arb_gt
  , arb_ge
  -- * Arithmetic
  , arb_neg
  , arb_neg_round
  , arb_abs
  , arb_nonnegative_abs
  , arb_sgn
  , arb_sgn_nonzero
  , arb_min
  , arb_max
  , arb_add
  , arb_add_arf
  , arb_add_ui
  , arb_add_si
  , arb_add_fmpz
  , arb_add_fmpz_2exp
  , arb_sub
  , arb_sub_arf
  , arb_sub_ui
  , arb_sub_si
  , arb_sub_fmpz
  , arb_mul
  , arb_mul_arf
  , arb_mul_si
  , arb_mul_ui
  , arb_mul_fmpz
  , arb_mul_2exp_si
  , arb_mul_2exp_fmpz
  , arb_addmul
  , arb_addmul_arf
  , arb_addmul_si
  , arb_addmul_ui
  , arb_addmul_fmpz
  , arb_submul
  , arb_submul_arf
  , arb_submul_si
  , arb_submul_ui
  , arb_submul_fmpz
  , arb_fma
  , arb_inv
  , arb_div
  , arb_div_arf
  , arb_div_si
  , arb_div_ui
  , arb_div_fmpz
  , arb_fmpz_div_fmpz
  , arb_ui_div
  , arb_div_2expm1_ui
  -- * Dot product
  , arb_dot_precise
  , arb_approx_dot
  , arb_dot_ui
  -- * Powers and roots
  , arb_sqrt
  , arb_sqrt_arf
  , arb_sqrt_fmpz
  , arb_sqrt_ui
  , arb_sqrtpos
  , arb_hypot
  , arb_rsqrt
  , arb_rsqrt_ui
  , arb_sqrt1pm1
  , arb_root_ui
  , arb_root
  , arb_sqr
  , arb_pow_fmpz_binexp
  , arb_pow_fmpz
  , arb_pow_ui
  , arb_ui_pow_ui
  , arb_si_pow_ui
  , arb_pow_fmpq
  , arb_pow
  -- * Exponentials and logarithms
  , arb_log_ui
  , arb_log_fmpz
  , arb_log_arf
  , arb_log
  , arb_log_ui_from_prev
  , arb_log1p
  , arb_log_base_ui
  , arb_log_hypot
  , arb_exp
  , arb_expm1
  , arb_exp_invexp
  -- * Trigonometric functions
  , arb_sin
  , arb_cos
  , arb_sin_cos
  , arb_sin_pi
  , arb_cos_pi
  , arb_sin_cos_pi
  , arb_tan
  , arb_cot
  , arb_sin_cos_pi_fmpq
  , arb_sin_pi_fmpq
  , arb_cos_pi_fmpq
  , arb_tan_pi
  , arb_cot_pi
  , arb_sec
  , arb_csc
  , arb_csc_pi
  , arb_sinc
  , arb_sinc_pi
  -- * Inverse trigonometric functions
  , arb_atan_arf
  , arb_atan
  , arb_atan2
  , arb_asin
  , arb_acos
  -- * Hyperbolic functions
  , arb_sinh
  , arb_cosh
  , arb_sinh_cosh
  , arb_tanh
  , arb_coth
  , arb_sech
  , arb_csch
  -- * Inverse hyperbolic functions
  , arb_atanh
  , arb_asinh
  , arb_acosh
  -- * Constants
  , arb_const_pi
  , arb_const_sqrt_pi
  , arb_const_log_sqrt2pi
  , arb_const_log2
  , arb_const_log10
  , arb_const_euler
  , arb_const_catalan
  , arb_const_e
  , arb_const_khinchin
  , arb_const_glaisher
  , arb_const_apery
  -- * Lambert W function
  , arb_lambertw
  -- * Gamma function and factorials
  , arb_rising_ui
  , arb_rising_fmpq_ui
  , arb_fac_ui
  , arb_doublefac_ui
  , arb_bin_ui
  , arb_bin_uiui
  , arb_gamma
  , arb_lgamma
  , arb_rgamma
  , arb_digamma
  -- * Zeta function
  , arb_zeta_ui_vec_borwein
  , arb_zeta_ui_asymp
  , arb_zeta_ui_euler_product
  , arb_zeta_ui_bernoulli
  , arb_zeta_ui_borwein_bsplit
  , arb_zeta_ui_vec
  , arb_zeta_ui_vec_even
  , arb_zeta_ui_vec_odd
  , arb_zeta_ui
  , arb_zeta
  , arb_hurwitz_zeta
  -- * Bernoulli numbers and polynomials
  , arb_bernoulli_ui
  , arb_bernoulli_fmpz
  , arb_bernoulli_ui_zeta
  , arb_bernoulli_poly_ui
  , arb_power_sum_vec
  -- * Polylogarithms
  , arb_polylog
  , arb_polylog_si
  -- * Other special functions
  , arb_fib_fmpz
  , arb_agm
  , arb_chebyshev_t_ui
  , arb_chebyshev_u_ui
  , arb_chebyshev_t2_ui
  , arb_chebyshev_u2_ui
  , arb_bell_sum_bsplit
  , arb_bell_sum_taylor
  , arb_bell_fmpz
  , arb_bell_ui
  , arb_euler_number_fmpz
  , arb_fmpz_euler_number_ui_multi_mod
  , arb_partitions_fmpz
  , arb_partitions_ui
  , arb_primorial_nth_ui
  , arb_primorial_ui
  -- * Internals for computing elementary functions
  , _arb_atan_taylor_naive
  , _arb_atan_taylor_rs
  , _arb_exp_taylor_naive
  , _arb_exp_taylor_rs
  , _arb_sin_cos_taylor_naive
  , _arb_sin_cos_taylor_rs
  , _arb_get_mpn_fixed_mod_log2
  , _arb_get_mpn_fixed_mod_pi4
  , _arb_exp_taylor_bound
  , arb_exp_arf_bb
  , _arb_exp_sum_bs_simple
  , _arb_exp_sum_bs_powtab
  , arb_exp_arf_rs_generic
  , _arb_atan_sum_bs_simple
  , _arb_atan_sum_bs_powtab
  , arb_atan_arf_bb
  , arb_atan_frac_bsplit
  , arb_sin_cos_arf_generic
  , arb_sin_cos_arf_bb
  , arb_sin_cos_wide
  , arb_sin_cos_generic
  , arb_log_primes_vec_bsplit
  , _arb_log_p_ensure_cached
  , arb_exp_arf_log_reduction
  , arb_exp_arf_generic
  , arb_exp_arf
  , arb_log_newton
  , arb_atan_gauss_primes_vec_bsplit
  , _arb_atan_gauss_p_ensure_cached
  , arb_sin_cos_arf_atan_reduction
  , arb_atan_newton
  -- * Vector functions
  , _arb_vec_zero
  , _arb_vec_is_zero
  , _arb_vec_is_finite
  , _arb_vec_set
  , _arb_vec_set_round
  , _arb_vec_swap
  , _arb_vec_neg
  , _arb_vec_sub
  , _arb_vec_add
  , _arb_vec_scalar_mul
  , _arb_vec_scalar_div
  , _arb_vec_scalar_mul_fmpz
  , _arb_vec_scalar_mul_2exp_si
  , _arb_vec_scalar_addmul
  , _arb_vec_get_mag
  , _arb_vec_bits
  , _arb_vec_set_powers
  , _arb_vec_add_error_arf_vec
  , _arb_vec_add_error_mag_vec
  , _arb_vec_indeterminate
  , _arb_vec_trim
  , _arb_vec_get_unique_fmpz_vec
) where

-- Real numbers ----------------------------------------------------------------

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.C.Types
import Foreign.C.String
import Foreign.Storable
import Foreign.Marshal.Alloc 

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpq
import Data.Number.Flint.Arb.Types

#include <flint/arb.h>

-- Types -----------------------------------------------------------------------

newArb = do
  x <- mallocForeignPtr
  withForeignPtr x arb_init
  addForeignPtrFinalizer p_arb_clear x
  return $ Arb x

newArbFromFmpz value = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> do
    arb_init x
    withFmpz value $ \value -> do
      arb_set_fmpz x value
  addForeignPtrFinalizer p_arb_clear x
  return $ Arb x

newArbFromFmpq value prec = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> do
    arb_init x
    withFmpq value $ \value -> do
      arb_set_fmpq x value prec
  addForeignPtrFinalizer p_arb_clear x
  return $ Arb x

withArb (Arb p) f = do
  withForeignPtr p $ \fp -> (Arb p,) <$> f fp

withNewArb f = do
  x <- newArb
  withArb x f

withNewArbFromFmpz value f = do
  x <- newArbFromFmpz value
  withArb x f

withNewArbFromFmpq value prec f = do
  x <- newArbFromFmpq value prec
  withArb x f

-- Memory management -----------------------------------------------------------

-- | /arb_init/ /x/ 
-- 
-- Initializes the variable /x/ for use. Its midpoint and radius are both
-- set to zero.
foreign import ccall "arb.h arb_init"
  arb_init :: Ptr CArb -> IO ()

-- | /arb_clear/ /x/ 
-- 
-- Clears the variable /x/, freeing or recycling its allocated memory.
foreign import ccall "arb.h arb_clear"
  arb_clear :: Ptr CArb -> IO ()

foreign import ccall "arb.h &arb_clear"
  p_arb_clear :: FunPtr (Ptr CArb -> IO ())

foreign import ccall "arb.h arb_midref_"
  arb_midref :: Ptr CArb -> IO (Ptr CArf)
  
-- | /_arb_vec_init/ /n/ 
-- 
-- Returns a pointer to an array of /n/ initialized @arb_struct@ entries.
foreign import ccall "arb.h _arb_vec_init"
  _arb_vec_init :: CLong -> IO (Ptr CArb)

-- | /_arb_vec_clear/ /v/ /n/ 
-- 
-- Clears an array of /n/ initialized @arb_struct@ entries.
foreign import ccall "arb.h _arb_vec_clear"
  _arb_vec_clear :: Ptr CArb -> CLong -> IO ()

-- | /arb_swap/ /x/ /y/ 
-- 
-- Swaps /x/ and /y/ efficiently.
foreign import ccall "arb.h arb_swap"
  arb_swap :: Ptr CArb -> Ptr CArb -> IO ()

-- | /arb_allocated_bytes/ /x/ 
-- 
-- Returns the total number of bytes heap-allocated internally by this
-- object. The count excludes the size of the structure itself. Add
-- @sizeof(arb_struct)@ to get the size of the object as a whole.
foreign import ccall "arb.h arb_allocated_bytes"
  arb_allocated_bytes :: Ptr CArb -> IO CLong

-- | /_arb_vec_allocated_bytes/ /vec/ /len/ 
-- 
-- Returns the total number of bytes allocated for this vector, i.e. the
-- space taken up by the vector itself plus the sum of the internal heap
-- allocation sizes for all its member elements.
foreign import ccall "arb.h _arb_vec_allocated_bytes"
  _arb_vec_allocated_bytes :: Ptr CArb -> CLong -> IO CLong

-- | /_arb_vec_estimate_allocated_bytes/ /len/ /prec/ 
-- 
-- Estimates the number of bytes that need to be allocated for a vector of
-- /len/ elements with /prec/ bits of precision, including the space for
-- internal limb data. This function returns a /double/ to avoid overflow
-- issues when both /len/ and /prec/ are large.
-- 
-- This is only an approximation of the physical memory that will be used
-- by an actual vector. In practice, the space varies with the content of
-- the numbers; for example, zeros and small integers require no internal
-- heap allocation even if the precision is huge. The estimate assumes that
-- exponents will not be bignums. The actual amount may also be higher or
-- lower due to overhead in the memory allocator or overcommitment by the
-- operating system.
foreign import ccall "arb.h _arb_vec_estimate_allocated_bytes"
  _arb_vec_estimate_allocated_bytes :: CLong -> CLong -> IO CDouble

-- Assignment and rounding -----------------------------------------------------

foreign import ccall "arb.h arb_set"
  arb_set :: Ptr CArb -> Ptr CArb -> IO ()

foreign import ccall "arb.h arb_set_arf"
  arb_set_arf :: Ptr CArb -> Ptr CArf -> IO ()

foreign import ccall "arb.h arb_set_si"
  arb_set_si :: Ptr CArb -> CLong -> IO ()

foreign import ccall "arb.h arb_set_ui"
  arb_set_ui :: Ptr CArb -> CULong -> IO ()

foreign import ccall "arb.h arb_set_d"
  arb_set_d :: Ptr CArb -> CDouble -> IO ()

-- | /arb_set_fmpz/ /y/ /x/ 
-- 
-- Sets /y/ to the value of /x/ without rounding.
foreign import ccall "arb.h arb_set_fmpz"
  arb_set_fmpz :: Ptr CArb -> Ptr CFmpz -> IO ()

-- | /arb_set_fmpz_2exp/ /y/ /x/ /e/ 
-- 
-- Sets /y/ to \(x \cdot 2^e\).
foreign import ccall "arb.h arb_set_fmpz_2exp"
  arb_set_fmpz_2exp :: Ptr CArb -> Ptr CFmpz -> Ptr CFmpz -> IO ()

foreign import ccall "arb.h arb_set_round"
  arb_set_round :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_set_round_fmpz/ /y/ /x/ /prec/ 
-- 
-- Sets /y/ to the value of /x/, rounded to /prec/ bits in the direction
-- towards zero.
foreign import ccall "arb.h arb_set_round_fmpz"
  arb_set_round_fmpz :: Ptr CArb -> Ptr CFmpz -> CLong -> IO ()

-- | /arb_set_round_fmpz_2exp/ /y/ /x/ /e/ /prec/ 
-- 
-- Sets /y/ to \(x \cdot 2^e\), rounded to /prec/ bits in the direction
-- towards zero.
foreign import ccall "arb.h arb_set_round_fmpz_2exp"
  arb_set_round_fmpz_2exp :: Ptr CArb -> Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- | /arb_set_fmpq/ /y/ /x/ /prec/ 
-- 
-- Sets /y/ to the rational number /x/, rounded to /prec/ bits in the
-- direction towards zero.
foreign import ccall "arb.h arb_set_fmpq"
  arb_set_fmpq :: Ptr CArb -> Ptr CFmpq -> CLong -> IO ()

-- | /arb_set_str/ /res/ /inp/ /prec/ 
-- 
-- Sets /res/ to the value specified by the human-readable string /inp/.
-- The input may be a decimal floating-point literal, such as \"25\",
-- \"0.001\", \"7e+141\" or \"-31.4159e-1\", and may also consist of two
-- such literals separated by the symbol \"+\/-\" and optionally enclosed
-- in brackets, e.g. \"[3.25 +\/- 0.0001]\", or simply \"[+\/- 10]\" with
-- an implicit zero midpoint. The output is rounded to /prec/ bits, and if
-- the binary-to-decimal conversion is inexact, the resulting error is
-- added to the radius.
-- 
-- The symbols \"inf\" and \"nan\" are recognized (a nan midpoint results
-- in an indeterminate interval, with infinite radius).
-- 
-- Returns 0 if successful and nonzero if unsuccessful. If unsuccessful,
-- the result is set to an indeterminate interval.
foreign import ccall "arb.h arb_set_str"
  arb_set_str :: Ptr CArb -> CString -> CLong -> IO CInt

-- | /arb_get_str/ /x/ /n/ /flags/ 
-- 
-- Returns a nice human-readable representation of /x/, with at most /n/
-- digits of the midpoint printed.
-- 
-- With default flags, the output can be parsed back with @arb_set_str@,
-- and this is guaranteed to produce an interval containing the original
-- interval /x/.
-- 
-- By default, the output is rounded so that the value given for the
-- midpoint is correct up to 1 ulp (unit in the last decimal place).
-- 
-- If /ARB_STR_MORE/ is added to /flags/, more (possibly incorrect) digits
-- may be printed.
-- 
-- If /ARB_STR_NO_RADIUS/ is added to /flags/, the radius is not included
-- in the output. Unless /ARB_STR_MORE/ is set, the output is rounded so
-- that the midpoint is correct to 1 ulp. As a special case, if there are
-- no significant digits after rounding, the result will be shown as
-- @0e+n@, meaning that the result is between @-1e+n@ and @1e+n@ (following
-- the contract that the output is correct to within one unit in the only
-- shown digit).
-- 
-- By adding a multiple /m/ of /ARB_STR_CONDENSE/ to /flags/, strings of
-- more than three times /m/ consecutive digits are condensed, only
-- printing the leading and trailing /m/ digits along with brackets
-- indicating the number of digits omitted (useful when computing values to
-- extremely high precision).
foreign import ccall "arb.h arb_get_str"
  arb_get_str :: Ptr CArb -> CLong -> ArbStrOption -> IO CString

foreign import ccall "arb.h arb_get_strd"
  arb_get_strd :: Ptr CArb -> CLong -> IO CString

foreign import ccall "arb.h arb_get_str_"
  arb_get_str_ :: Ptr CArb -> IO CString

-- Assignment of special values ------------------------------------------------

-- | /arb_zero/ /x/ 
-- 
-- Sets /x/ to zero.
foreign import ccall "arb.h arb_zero"
  arb_zero :: Ptr CArb -> IO ()

-- | /arb_one/ /f/ 
-- 
-- Sets /x/ to the exact integer 1.
foreign import ccall "arb.h arb_one"
  arb_one :: Ptr CArb -> IO ()

-- | /arb_pos_inf/ /x/ 
-- 
-- Sets /x/ to positive infinity, with a zero radius.
foreign import ccall "arb.h arb_pos_inf"
  arb_pos_inf :: Ptr CArb -> IO ()

-- | /arb_neg_inf/ /x/ 
-- 
-- Sets /x/ to negative infinity, with a zero radius.
foreign import ccall "arb.h arb_neg_inf"
  arb_neg_inf :: Ptr CArb -> IO ()

-- | /arb_zero_pm_inf/ /x/ 
-- 
-- Sets /x/ to \([0 \pm \infty]\), representing the whole extended real
-- line.
foreign import ccall "arb.h arb_zero_pm_inf"
  arb_zero_pm_inf :: Ptr CArb -> IO ()

-- | /arb_indeterminate/ /x/ 
-- 
-- Sets /x/ to \([\operatorname{NaN} \pm \infty]\), representing an
-- indeterminate result.
foreign import ccall "arb.h arb_indeterminate"
  arb_indeterminate :: Ptr CArb -> IO ()

-- | /arb_zero_pm_one/ /x/ 
-- 
-- Sets /x/ to the interval \([0 \pm 1]\).
foreign import ccall "arb.h arb_zero_pm_one"
  arb_zero_pm_one :: Ptr CArb -> IO ()

-- | /arb_unit_interval/ /x/ 
-- 
-- Sets /x/ to the interval \([0, 1]\).
foreign import ccall "arb.h arb_unit_interval"
  arb_unit_interval :: Ptr CArb -> IO ()

-- Input and output ------------------------------------------------------------

-- | /arb_print/
--
-- The /arb_print.../ function prints the internal representation to
-- standard output.
--
arb_print :: Ptr CArb -> IO ()
arb_print x = do
  cstr <- arb_get_str_ x
  str <- peekCString cstr
  putStr str
  free cstr

-- | /arb_fprint/ /file/ /x/ 
-- 
-- Prints the internal representation of /x/ to the stream file /file/.
foreign import ccall "arb.h arb_fprint"
  arb_fprint :: Ptr CFile -> Ptr CArb -> IO ()

-- | /arb_printd/ /file/ /x/ /digits/ 
-- 
-- Prints /x/ in decimal to standard output. The printed value of the
-- radius is not adjusted to compensate for the fact that the
-- binary-to-decimal conversion of both the midpoint and the radius
-- introduces additional error.
arb_printd x prec = do
  cstr <- arb_get_strd x prec
  str <- peekCString cstr
  putStr str
  free cstr
  
-- | /arb_fprintd/ /file/ /x/ /digits/ 
-- 
-- Prints /x/ in decimal to stream file /file/. The printed value of
-- the radius is not adjusted to compensate for the fact that the
-- binary-to-decimal conversion of both the midpoint and the radius
-- introduces additional error.
foreign import ccall "arb.h arb_fprintd"
  arb_fprintd :: Ptr CFile -> Ptr CArb -> CLong -> IO ()


-- | /arb_printn/ /file/ /x/ /digits/ /flags/ 
-- 
-- Prints a nice decimal representation of /x/. By default, the output
-- shows the midpoint with a guaranteed error of at most one unit in the
-- last decimal place. In addition, an explicit error bound is printed so
-- that the displayed decimal interval is guaranteed to enclose /x/. See
-- @arb_get_str@ for details.
arb_printn :: Ptr CArb -> CLong -> ArbStrOption -> IO ()
arb_printn x prec opt = do
  cstr <- arb_get_str x prec opt
  str <- peekCString cstr
  putStr str
  free cstr

-- | /arb_fprintn/ /file/ /x/ /digits/ /flags/ 
-- 
-- Prints a nice decimal representation of /x/. By default, the output
-- shows the midpoint with a guaranteed error of at most one unit in the
-- last decimal place. In addition, an explicit error bound is printed so
-- that the displayed decimal interval is guaranteed to enclose /x/. See
-- @arb_get_str@ for details.
foreign import ccall "arb.h arb_fprintn"
  arb_fprintn :: Ptr CFile -> Ptr CArb -> CLong -> ArbStrOption -> IO ()

-- | /arb_dump_str/ /x/ 
-- 
-- Returns a serialized representation of /x/ as a null-terminated ASCII
-- string that can be read by @arb_load_str@. The format consists of four
-- hexadecimal integers representing the midpoint mantissa, midpoint
-- exponent, radius mantissa and radius exponent (with special values to
-- indicate zero, infinity and NaN values), separated by single spaces. The
-- returned string needs to be deallocated with /flint_free/.
foreign import ccall "arb.h arb_dump_str"
  arb_dump_str :: Ptr CArb -> IO CString

-- | /arb_load_str/ /x/ /str/ 
-- 
-- Sets /x/ to the serialized representation given in /str/. Returns a
-- nonzero value if /str/ is not formatted correctly (see @arb_dump_str@).
foreign import ccall "arb.h arb_load_str"
  arb_load_str :: Ptr CArb -> CString -> IO CInt

-- | /arb_dump_file/ /stream/ /x/ 
-- 
-- Writes a serialized ASCII representation of /x/ to /stream/ in a form
-- that can be read by @arb_load_file@. Returns a nonzero value if the data
-- could not be written.
foreign import ccall "arb.h arb_dump_file"
  arb_dump_file :: Ptr CFile -> Ptr CArb -> IO CInt

-- | /arb_load_file/ /x/ /stream/ 
-- 
-- Reads /x/ from a serialized ASCII representation in /stream/. Returns a
-- nonzero value if the data is not formatted correctly or the read failed.
-- Note that the data is assumed to be delimited by a whitespace or
-- end-of-file, i.e., when writing multiple values with @arb_dump_file@
-- make sure to insert a whitespace to separate consecutive values.
-- 
-- It is possible to serialize and deserialize a vector as follows
-- (warning: without error handling):
-- 
-- > fp = fopen("data.txt", "w");
-- > for (i = 0; i < n; i++)
-- > {
-- >     arb_dump_file(fp, vec + i);
-- >     fprintf(fp, "\n");    // or any whitespace character
-- > }
-- > fclose(fp);
-- >
-- > fp = fopen("data.txt", "r");
-- > for (i = 0; i < n; i++)
-- > {
-- >     arb_load_file(vec + i, fp);
-- > }
-- > fclose(fp);
foreign import ccall "arb.h arb_load_file"
  arb_load_file :: Ptr CArb -> Ptr CFile -> IO CInt

-- Random number generation ----------------------------------------------------

-- | /arb_randtest/ /x/ /state/ /prec/ /mag_bits/ 
-- 
-- Generates a random ball. The midpoint and radius will both be finite.
foreign import ccall "arb.h arb_randtest"
  arb_randtest :: Ptr CArb -> Ptr CFRandState -> CLong -> CLong -> IO ()

-- | /arb_randtest_exact/ /x/ /state/ /prec/ /mag_bits/ 
-- 
-- Generates a random number with zero radius.
foreign import ccall "arb.h arb_randtest_exact"
  arb_randtest_exact :: Ptr CArb -> Ptr CFRandState -> CLong -> CLong -> IO ()

-- | /arb_randtest_precise/ /x/ /state/ /prec/ /mag_bits/ 
-- 
-- Generates a random number with radius around \(2^{-\text{prec}}\) the
-- magnitude of the midpoint.
foreign import ccall "arb.h arb_randtest_precise"
  arb_randtest_precise :: Ptr CArb -> Ptr CFRandState -> CLong -> CLong -> IO ()

-- | /arb_randtest_wide/ /x/ /state/ /prec/ /mag_bits/ 
-- 
-- Generates a random number with midpoint and radius chosen independently,
-- possibly giving a very large interval.
foreign import ccall "arb.h arb_randtest_wide"
  arb_randtest_wide :: Ptr CArb -> Ptr CFRandState -> CLong -> CLong -> IO ()

-- | /arb_randtest_special/ /x/ /state/ /prec/ /mag_bits/ 
-- 
-- Generates a random interval, possibly having NaN or an infinity as the
-- midpoint and possibly having an infinite radius.
foreign import ccall "arb.h arb_randtest_special"
  arb_randtest_special :: Ptr CArb -> Ptr CFRandState -> CLong -> CLong -> IO ()

-- | /arb_get_rand_fmpq/ /q/ /state/ /x/ /bits/ 
-- 
-- Sets /q/ to a random rational number from the interval represented by
-- /x/. A denominator is chosen by multiplying the binary denominator of
-- /x/ by a random integer up to /bits/ bits.
-- 
-- The outcome is undefined if the midpoint or radius of /x/ is non-finite,
-- or if the exponent of the midpoint or radius is so large or small that
-- representing the endpoints as exact rational numbers would cause
-- overflows.
foreign import ccall "arb.h arb_get_rand_fmpq"
  arb_get_rand_fmpq :: Ptr CFmpq -> Ptr CFRandState -> Ptr CArb -> CLong -> IO ()

-- | /arb_urandom/ /x/ /state/ /prec/ 
-- 
-- Sets /x/ to a uniformly distributed random number in the interval
-- \([0, 1]\). The method uses rounding from integers to floats, hence the
-- radius might not be \(0\).
foreign import ccall "arb.h arb_urandom"
  arb_urandom :: Ptr CArb -> Ptr CFRandState -> CLong -> IO ()

-- Radius and interval operations ----------------------------------------------

-- | /arb_get_mid_arb/ /m/ /x/ 
-- 
-- Sets /m/ to the midpoint of /x/.
foreign import ccall "arb.h arb_get_mid_arb"
  arb_get_mid_arb :: Ptr CArb -> Ptr CArb -> IO ()

-- | /arb_get_rad_arb/ /r/ /x/ 
-- 
-- Sets /r/ to the radius of /x/.
foreign import ccall "arb.h arb_get_rad_arb"
  arb_get_rad_arb :: Ptr CArb -> Ptr CArb -> IO ()

foreign import ccall "arb.h arb_add_error_arf"
  arb_add_error_arf :: Ptr CArb -> Ptr CArf -> IO ()

foreign import ccall "arb.h arb_add_error_mag"
  arb_add_error_mag :: Ptr CArb -> Ptr CMag -> IO ()

-- | /arb_add_error/ /x/ /err/ 
-- 
-- Adds the absolute value of /err/ to the radius of /x/ (the operation is
-- done in-place).
foreign import ccall "arb.h arb_add_error"
  arb_add_error :: Ptr CArb -> Ptr CArb -> IO ()

foreign import ccall "arb.h arb_add_error_2exp_si"
  arb_add_error_2exp_si :: Ptr CArb -> CLong -> IO ()

-- | /arb_add_error_2exp_fmpz/ /x/ /e/ 
-- 
-- Adds \(2^e\) to the radius of /x/.
foreign import ccall "arb.h arb_add_error_2exp_fmpz"
  arb_add_error_2exp_fmpz :: Ptr CArb -> Ptr CFmpz -> IO ()

-- | /arb_union/ /z/ /x/ /y/ /prec/ 
-- 
-- Sets /z/ to a ball containing both /x/ and /y/.
foreign import ccall "arb.h arb_union"
  arb_union :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_intersection/ /z/ /x/ /y/ /prec/ 
-- 
-- If /x/ and /y/ overlap according to @arb_overlaps@, then /z/ is set to a
-- ball containing the intersection of /x/ and /y/ and a nonzero value is
-- returned. Otherwise zero is returned and the value of /z/ is undefined.
-- If /x/ or /y/ contains NaN, the result is NaN.
foreign import ccall "arb.h arb_intersection"
  arb_intersection :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO CInt

-- | /arb_nonnegative_part/ /res/ /x/ 
-- 
-- Sets /res/ to the intersection of /x/ with \([0,\infty]\). If /x/ is
-- nonnegative, an exact copy is made. If /x/ is finite and contains
-- negative numbers, an interval of the form \([r/2 \pm r/2]\) is produced,
-- which certainly contains no negative points. In the special case when
-- /x/ is strictly negative, /res/ is set to zero.
foreign import ccall "arb.h arb_nonnegative_part"
  arb_nonnegative_part :: Ptr CArb -> Ptr CArb -> IO ()

-- | /arb_get_abs_ubound_arf/ /u/ /x/ /prec/ 
-- 
-- Sets /u/ to the upper bound for the absolute value of /x/, rounded up to
-- /prec/ bits. If /x/ contains NaN, the result is NaN.
foreign import ccall "arb.h arb_get_abs_ubound_arf"
  arb_get_abs_ubound_arf :: Ptr CArf -> Ptr CArb -> CLong -> IO ()

-- | /arb_get_abs_lbound_arf/ /u/ /x/ /prec/ 
-- 
-- Sets /u/ to the lower bound for the absolute value of /x/, rounded down
-- to /prec/ bits. If /x/ contains NaN, the result is NaN.
foreign import ccall "arb.h arb_get_abs_lbound_arf"
  arb_get_abs_lbound_arf :: Ptr CArf -> Ptr CArb -> CLong -> IO ()

-- | /arb_get_ubound_arf/ /u/ /x/ /prec/ 
-- 
-- Sets /u/ to the upper bound for the value of /x/, rounded up to /prec/
-- bits. If /x/ contains NaN, the result is NaN.
foreign import ccall "arb.h arb_get_ubound_arf"
  arb_get_ubound_arf :: Ptr CArf -> Ptr CArb -> CLong -> IO ()

-- | /arb_get_lbound_arf/ /u/ /x/ /prec/ 
-- 
-- Sets /u/ to the lower bound for the value of /x/, rounded down to /prec/
-- bits. If /x/ contains NaN, the result is NaN.
foreign import ccall "arb.h arb_get_lbound_arf"
  arb_get_lbound_arf :: Ptr CArf -> Ptr CArb -> CLong -> IO ()

-- | /arb_get_mag/ /z/ /x/ 
-- 
-- Sets /z/ to an upper bound for the absolute value of /x/. If /x/
-- contains NaN, the result is positive infinity.
foreign import ccall "arb.h arb_get_mag"
  arb_get_mag :: Ptr CMag -> Ptr CArb -> IO ()

-- | /arb_get_mag_lower/ /z/ /x/ 
-- 
-- Sets /z/ to a lower bound for the absolute value of /x/. If /x/ contains
-- NaN, the result is zero.
foreign import ccall "arb.h arb_get_mag_lower"
  arb_get_mag_lower :: Ptr CMag -> Ptr CArb -> IO ()

-- | /arb_get_mag_lower_nonnegative/ /z/ /x/ 
-- 
-- Sets /z/ to a lower bound for the signed value of /x/, or zero if /x/
-- overlaps with the negative half-axis. If /x/ contains NaN, the result is
-- zero.
foreign import ccall "arb.h arb_get_mag_lower_nonnegative"
  arb_get_mag_lower_nonnegative :: Ptr CMag -> Ptr CArb -> IO ()

-- | /arb_get_interval_fmpz_2exp/ /a/ /b/ /exp/ /x/ 
-- 
-- Computes the exact interval represented by /x/, in the form of an
-- integer interval multiplied by a power of two, i.e.
-- \(x = [a, b] \times 2^{\text{exp}}\). The result is normalized by
-- removing common trailing zeros from /a/ and /b/.
-- 
-- This method aborts if /x/ is infinite or NaN, or if the difference
-- between the exponents of the midpoint and the radius is so large that
-- allocating memory for the result fails.
-- 
-- Warning: this method will allocate a huge amount of memory to store the
-- result if the exponent difference is huge. Memory allocation could
-- succeed even if the required space is far larger than the physical
-- memory available on the machine, resulting in swapping. It is
-- recommended to check that the midpoint and radius of /x/ both are within
-- a reasonable range before calling this method.
foreign import ccall "arb.h arb_get_interval_fmpz_2exp"
  arb_get_interval_fmpz_2exp :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CArb -> IO ()

foreign import ccall "arb.h arb_set_interval_mag"
  arb_set_interval_mag :: Ptr CArb -> Ptr CMag -> Ptr CMag -> CLong -> IO ()

foreign import ccall "arb.h arb_set_interval_arf"
  arb_set_interval_arf :: Ptr CArb -> Ptr CArf -> Ptr CArf -> CLong -> IO ()

-- | /arb_set_interval_mpfr/ /x/ /a/ /b/ /prec/ 
-- 
-- Sets /x/ to a ball containing the interval \([a, b]\). We require that
-- \(a \le b\).
foreign import ccall "arb.h arb_set_interval_mpfr"
  arb_set_interval_mpfr :: Ptr CArb -> Ptr CMpfr -> Ptr CMpfr -> CLong -> IO ()

-- | /arb_set_interval_neg_pos_mag/ /x/ /a/ /b/ /prec/ 
-- 
-- Sets /x/ to a ball containing the interval \([-a, b]\).
foreign import ccall "arb.h arb_set_interval_neg_pos_mag"
  arb_set_interval_neg_pos_mag :: Ptr CArb -> Ptr CMag -> Ptr CMag -> CLong -> IO ()

foreign import ccall "arb.h arb_get_interval_arf"
  arb_get_interval_arf :: Ptr CArf -> Ptr CArf -> Ptr CArb -> CLong -> IO ()

-- | /arb_get_interval_mpfr/ /a/ /b/ /x/ 
-- 
-- Constructs an interval \([a, b]\) containing the ball /x/. The MPFR
-- version uses the precision of the output variables.
foreign import ccall "arb.h arb_get_interval_mpfr"
  arb_get_interval_mpfr :: Ptr CMpfr -> Ptr CMpfr -> Ptr CArb -> IO ()

-- | /arb_rel_error_bits/ /x/ 
-- 
-- Returns the effective relative error of /x/ measured in bits, defined as
-- the difference between the position of the top bit in the radius and the
-- top bit in the midpoint, plus one. The result is clamped between
-- plus\/minus /ARF_PREC_EXACT/.
foreign import ccall "arb.h arb_rel_error_bits"
  arb_rel_error_bits :: Ptr CArb -> IO CLong

-- | /arb_rel_accuracy_bits/ /x/ 
-- 
-- Returns the effective relative accuracy of /x/ measured in bits, equal
-- to the negative of the return value from @arb_rel_error_bits@.
foreign import ccall "arb.h arb_rel_accuracy_bits"
  arb_rel_accuracy_bits :: Ptr CArb -> IO CLong

-- | /arb_rel_one_accuracy_bits/ /x/ 
-- 
-- Given a ball with midpoint /m/ and radius /r/, returns an approximation
-- of the relative accuracy of \([\max(1,|m|) \pm r]\) measured in bits.
foreign import ccall "arb.h arb_rel_one_accuracy_bits"
  arb_rel_one_accuracy_bits :: Ptr CArb -> IO CLong

-- | /arb_bits/ /x/ 
-- 
-- Returns the number of bits needed to represent the absolute value of the
-- mantissa of the midpoint of /x/, i.e. the minimum precision sufficient
-- to represent /x/ exactly. Returns 0 if the midpoint of /x/ is a special
-- value.
foreign import ccall "arb.h arb_bits"
  arb_bits :: Ptr CArb -> IO CLong

-- | /arb_trim/ /y/ /x/ 
-- 
-- Sets /y/ to a trimmed copy of /x/: rounds /x/ to a number of bits equal
-- to the accuracy of /x/ (as indicated by its radius), plus a few guard
-- bits. The resulting ball is guaranteed to contain /x/, but is more
-- economical if /x/ has less than full accuracy.
foreign import ccall "arb.h arb_trim"
  arb_trim :: Ptr CArb -> Ptr CArb -> IO ()

-- | /arb_get_unique_fmpz/ /z/ /x/ 
-- 
-- If /x/ contains a unique integer, sets /z/ to that value and returns
-- nonzero. Otherwise (if /x/ represents no integers or more than one
-- integer), returns zero.
-- 
-- This method aborts if there is a unique integer but that integer is so
-- large that allocating memory for the result fails.
-- 
-- Warning: this method will allocate a huge amount of memory to store the
-- result if there is a unique integer and that integer is huge. Memory
-- allocation could succeed even if the required space is far larger than
-- the physical memory available on the machine, resulting in swapping. It
-- is recommended to check that the midpoint of /x/ is within a reasonable
-- range before calling this method.
foreign import ccall "arb.h arb_get_unique_fmpz"
  arb_get_unique_fmpz :: Ptr CFmpz -> Ptr CArb -> IO CInt

-- | /arb_floor/ /y/ /x/ /prec/ 
-- 
-- Sets /y/ to a ball containing respectively, \(\lfloor x \rfloor\) and
-- \(\lceil x \rceil\), \(\operatorname{trunc}(x)\),
-- \(\operatorname{nint}(x)\), with the midpoint of /y/ rounded to at most
-- /prec/ bits.
foreign import ccall "arb.h arb_floor"
  arb_floor :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_get_fmpz_mid_rad_10exp/ /mid/ /rad/ /exp/ /x/ /n/ 
-- 
-- Assuming that /x/ is finite and not exactly zero, computes integers
-- /mid/, /rad/, /exp/ such that \(x \in [m-r, m+r] \times 10^e\) and such
-- that the larger out of /mid/ and /rad/ has at least /n/ digits plus a
-- few guard digits. If /x/ is infinite or exactly zero, the outputs are
-- all set to zero.
foreign import ccall "arb.h arb_get_fmpz_mid_rad_10exp"
  arb_get_fmpz_mid_rad_10exp :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CArb -> CLong -> IO ()

foreign import ccall "arb.h arb_can_round_arf"
  arb_can_round_arf :: Ptr CArb -> CLong -> ArfRnd -> IO CInt

-- | /arb_can_round_mpfr/ /x/ /prec/ /rnd/ 
-- 
-- Returns nonzero if rounding the midpoint of /x/ to /prec/ bits in the
-- direction /rnd/ is guaranteed to give the unique correctly rounded
-- floating-point approximation for the real number represented by /x/.
-- 
-- In other words, if this function returns nonzero, applying
-- @arf_set_round@, or @arf_get_mpfr@, or @arf_get_d@ to the midpoint of
-- /x/ is guaranteed to return a correctly rounded /arf_t/, /mpfr_t/
-- (provided that /prec/ is the precision of the output variable), or
-- /double/ (provided that /prec/ is 53). Moreover, @arf_get_mpfr@ is
-- guaranteed to return the correct ternary value according to MPFR
-- semantics.
-- 
-- Note that the /mpfr/ version of this function takes an MPFR rounding
-- mode symbol as input, while the /arf/ version takes an /arf/ rounding
-- mode symbol. Otherwise, the functions are identical.
-- 
-- This function may perform a fast, inexact test; that is, it may return
-- zero in some cases even when correct rounding actually is possible.
-- 
-- To be conservative, zero is returned when /x/ is non-finite, even if it
-- is an \"exact\" infinity.
foreign import ccall "arb.h arb_can_round_mpfr"
  arb_can_round_mpfr :: Ptr CArb -> CLong -> CMpfrRnd -> IO CInt

-- Comparisons -----------------------------------------------------------------

-- | /arb_is_zero/ /x/ 
-- 
-- Returns nonzero iff the midpoint and radius of /x/ are both zero.
foreign import ccall "arb.h arb_is_zero"
  arb_is_zero :: Ptr CArb -> IO CInt

-- | /arb_is_nonzero/ /x/ 
-- 
-- Returns nonzero iff zero is not contained in the interval represented by
-- /x/.
foreign import ccall "arb.h arb_is_nonzero"
  arb_is_nonzero :: Ptr CArb -> IO CInt

-- | /arb_is_one/ /f/ 
-- 
-- Returns nonzero iff /x/ is exactly 1.
foreign import ccall "arb.h arb_is_one"
  arb_is_one :: Ptr CArb -> IO CInt

-- | /arb_is_finite/ /x/ 
-- 
-- Returns nonzero iff the midpoint and radius of /x/ are both finite
-- floating-point numbers, i.e. not infinities or NaN.
foreign import ccall "arb.h arb_is_finite"
  arb_is_finite :: Ptr CArb -> IO CInt

-- | /arb_is_exact/ /x/ 
-- 
-- Returns nonzero iff the radius of /x/ is zero.
foreign import ccall "arb.h arb_is_exact"
  arb_is_exact :: Ptr CArb -> IO CInt

-- | /arb_is_int/ /x/ 
-- 
-- Returns nonzero iff /x/ is an exact integer.
foreign import ccall "arb.h arb_is_int"
  arb_is_int :: Ptr CArb -> IO CInt

-- | /arb_is_int_2exp_si/ /x/ /e/ 
-- 
-- Returns nonzero iff /x/ exactly equals \(n 2^e\) for some integer /n/.
foreign import ccall "arb.h arb_is_int_2exp_si"
  arb_is_int_2exp_si :: Ptr CArb -> CLong -> IO CInt

-- | /arb_equal/ /x/ /y/ 
-- 
-- Returns nonzero iff /x/ and /y/ are equal as balls, i.e. have both the
-- same midpoint and radius.
-- 
-- Note that this is not the same thing as testing whether both /x/ and /y/
-- certainly represent the same real number, unless either /x/ or /y/ is
-- exact (and neither contains NaN). To test whether both operands /might/
-- represent the same mathematical quantity, use @arb_overlaps@ or
-- @arb_contains@, depending on the circumstance.
foreign import ccall "arb.h arb_equal"
  arb_equal :: Ptr CArb -> Ptr CArb -> IO CInt

-- | /arb_equal_si/ /x/ /y/ 
-- 
-- Returns nonzero iff /x/ is equal to the integer /y/.
foreign import ccall "arb.h arb_equal_si"
  arb_equal_si :: Ptr CArb -> CLong -> IO CInt

foreign import ccall "arb.h arb_is_positive"
  arb_is_positive :: Ptr CArb -> IO CInt

foreign import ccall "arb.h arb_is_nonnegative"
  arb_is_nonnegative :: Ptr CArb -> IO CInt

foreign import ccall "arb.h arb_is_negative"
  arb_is_negative :: Ptr CArb -> IO CInt

-- | /arb_is_nonpositive/ /x/ 
-- 
-- Returns nonzero iff all points /p/ in the interval represented by /x/
-- satisfy, respectively, \(p > 0\), \(p \ge 0\), \(p < 0\), \(p \le 0\).
-- If /x/ contains NaN, returns zero.
foreign import ccall "arb.h arb_is_nonpositive"
  arb_is_nonpositive :: Ptr CArb -> IO CInt

-- | /arb_overlaps/ /x/ /y/ 
-- 
-- Returns nonzero iff /x/ and /y/ have some point in common. If either /x/
-- or /y/ contains NaN, this function always returns nonzero (as a NaN
-- could be anything, it could in particular contain any number that is
-- included in the other operand).
foreign import ccall "arb.h arb_overlaps"
  arb_overlaps :: Ptr CArb -> Ptr CArb -> IO CInt

foreign import ccall "arb.h arb_contains_arf"
  arb_contains_arf :: Ptr CArb -> Ptr CArf -> IO CInt

foreign import ccall "arb.h arb_contains_fmpq"
  arb_contains_fmpq :: Ptr CArb -> Ptr CFmpq -> IO CInt

foreign import ccall "arb.h arb_contains_fmpz"
  arb_contains_fmpz :: Ptr CArb -> Ptr CFmpz -> IO CInt

foreign import ccall "arb.h arb_contains_si"
  arb_contains_si :: Ptr CArb -> CLong -> IO CInt

foreign import ccall "arb.h arb_contains_mpfr"
  arb_contains_mpfr :: Ptr CArb -> Ptr CMpfr -> IO CInt

-- | /arb_contains/ /x/ /y/ 
-- 
-- Returns nonzero iff the given number (or ball) /y/ is contained in the
-- interval represented by /x/.
-- 
-- If /x/ contains NaN, this function always returns nonzero (as it could
-- represent anything, and in particular could represent all the points
-- included in /y/). If /y/ contains NaN and /x/ does not, it always
-- returns zero.
foreign import ccall "arb.h arb_contains"
  arb_contains :: Ptr CArb -> Ptr CArb -> IO CInt

-- | /arb_contains_int/ /x/ 
-- 
-- Returns nonzero iff the interval represented by /x/ contains an integer.
foreign import ccall "arb.h arb_contains_int"
  arb_contains_int :: Ptr CArb -> IO CInt

foreign import ccall "arb.h arb_contains_zero"
  arb_contains_zero :: Ptr CArb -> IO CInt

foreign import ccall "arb.h arb_contains_negative"
  arb_contains_negative :: Ptr CArb -> IO CInt

foreign import ccall "arb.h arb_contains_nonpositive"
  arb_contains_nonpositive :: Ptr CArb -> IO CInt

foreign import ccall "arb.h arb_contains_positive"
  arb_contains_positive :: Ptr CArb -> IO CInt

-- | /arb_contains_nonnegative/ /x/ 
-- 
-- Returns nonzero iff there is any point /p/ in the interval represented
-- by /x/ satisfying, respectively, \(p = 0\), \(p < 0\), \(p \le 0\),
-- \(p > 0\), \(p \ge 0\). If /x/ contains NaN, returns nonzero.
foreign import ccall "arb.h arb_contains_nonnegative"
  arb_contains_nonnegative :: Ptr CArb -> IO CInt

-- | /arb_contains_interior/ /x/ /y/ 
-- 
-- Tests if /y/ is contained in the interior of /x/; that is, contained in
-- /x/ and not touching either endpoint.
foreign import ccall "arb.h arb_contains_interior"
  arb_contains_interior :: Ptr CArb -> Ptr CArb -> IO CInt

foreign import ccall "arb.h arb_eq"
  arb_eq :: Ptr CArb -> Ptr CArb -> IO CInt

foreign import ccall "arb.h arb_ne"
  arb_ne :: Ptr CArb -> Ptr CArb -> IO CInt

foreign import ccall "arb.h arb_lt"
  arb_lt :: Ptr CArb -> Ptr CArb -> IO CInt

foreign import ccall "arb.h arb_le"
  arb_le :: Ptr CArb -> Ptr CArb -> IO CInt

foreign import ccall "arb.h arb_gt"
  arb_gt :: Ptr CArb -> Ptr CArb -> IO CInt

-- | /arb_ge/ /x/ /y/ 
-- 
-- Respectively performs the comparison \(x = y\), \(x \ne y\), \(x < y\),
-- \(x \le y\), \(x > y\), \(x \ge y\) in a mathematically meaningful way.
-- If the comparison \(t \, (\operatorname{op}) \, u\) holds for all
-- \(t \in x\) and all \(u \in y\), returns 1. Otherwise, returns 0.
-- 
-- The balls /x/ and /y/ are viewed as subintervals of the extended real
-- line. Note that balls that are formally different can compare as equal
-- under this definition: for example,
-- \([-\infty \pm 3] = [-\infty \pm 0]\). Also
-- \([-\infty] \le [\infty \pm \infty]\).
-- 
-- The output is always 0 if either input has NaN as midpoint.
foreign import ccall "arb.h arb_ge"
  arb_ge :: Ptr CArb -> Ptr CArb -> IO CInt

-- Arithmetic ------------------------------------------------------------------

foreign import ccall "arb.h arb_neg"
  arb_neg :: Ptr CArb -> Ptr CArb -> IO ()

-- | /arb_neg_round/ /y/ /x/ /prec/ 
-- 
-- Sets /y/ to the negation of /x/.
foreign import ccall "arb.h arb_neg_round"
  arb_neg_round :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_abs/ /y/ /x/ 
-- 
-- Sets /y/ to the absolute value of /x/. No attempt is made to improve the
-- interval represented by /x/ if it contains zero.
foreign import ccall "arb.h arb_abs"
  arb_abs :: Ptr CArb -> Ptr CArb -> IO ()

-- | /arb_nonnegative_abs/ /y/ /x/ 
-- 
-- Sets /y/ to the absolute value of /x/. If /x/ is finite and it contains
-- zero, sets /y/ to some interval \([r \pm r]\) that contains the absolute
-- value of /x/.
foreign import ccall "arb.h arb_nonnegative_abs"
  arb_nonnegative_abs :: Ptr CArb -> Ptr CArb -> IO ()

-- | /arb_sgn/ /y/ /x/ 
-- 
-- Sets /y/ to the sign function of /x/. The result is \([0 \pm 1]\) if /x/
-- contains both zero and nonzero numbers.
foreign import ccall "arb.h arb_sgn"
  arb_sgn :: Ptr CArb -> Ptr CArb -> IO ()

-- | /arb_sgn_nonzero/ /x/ 
-- 
-- Returns 1 if /x/ is strictly positive, -1 if /x/ is strictly negative,
-- and 0 if /x/ is zero or a ball containing zero so that its sign is not
-- determined.
foreign import ccall "arb.h arb_sgn_nonzero"
  arb_sgn_nonzero :: Ptr CArb -> IO CInt

foreign import ccall "arb.h arb_min"
  arb_min :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_max/ /z/ /x/ /y/ /prec/ 
-- 
-- Sets /z/ respectively to the minimum and the maximum of /x/ and /y/.
foreign import ccall "arb.h arb_max"
  arb_max :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()

foreign import ccall "arb.h arb_add"
  arb_add :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()

foreign import ccall "arb.h arb_add_arf"
  arb_add_arf :: Ptr CArb -> Ptr CArb -> Ptr CArf -> CLong -> IO ()

foreign import ccall "arb.h arb_add_ui"
  arb_add_ui :: Ptr CArb -> Ptr CArb -> CULong -> CLong -> IO ()

foreign import ccall "arb.h arb_add_si"
  arb_add_si :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /arb_add_fmpz/ /z/ /x/ /y/ /prec/ 
-- 
-- Sets \(z = x + y\), rounded to /prec/ bits. The precision can be
-- /ARF_PREC_EXACT/ provided that the result fits in memory.
foreign import ccall "arb.h arb_add_fmpz"
  arb_add_fmpz :: Ptr CArb -> Ptr CArb -> Ptr CFmpz -> CLong -> IO ()

-- | /arb_add_fmpz_2exp/ /z/ /x/ /m/ /e/ /prec/ 
-- 
-- Sets \(z = x + m \cdot 2^e\), rounded to /prec/ bits. The precision can
-- be /ARF_PREC_EXACT/ provided that the result fits in memory.
foreign import ccall "arb.h arb_add_fmpz_2exp"
  arb_add_fmpz_2exp :: Ptr CArb -> Ptr CArb -> Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

foreign import ccall "arb.h arb_sub"
  arb_sub :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()

foreign import ccall "arb.h arb_sub_arf"
  arb_sub_arf :: Ptr CArb -> Ptr CArb -> Ptr CArf -> CLong -> IO ()

foreign import ccall "arb.h arb_sub_ui"
  arb_sub_ui :: Ptr CArb -> Ptr CArb -> CULong -> CLong -> IO ()

foreign import ccall "arb.h arb_sub_si"
  arb_sub_si :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /arb_sub_fmpz/ /z/ /x/ /y/ /prec/ 
-- 
-- Sets \(z = x - y\), rounded to /prec/ bits. The precision can be
-- /ARF_PREC_EXACT/ provided that the result fits in memory.
foreign import ccall "arb.h arb_sub_fmpz"
  arb_sub_fmpz :: Ptr CArb -> Ptr CArb -> Ptr CFmpz -> CLong -> IO ()

foreign import ccall "arb.h arb_mul"
  arb_mul :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()

foreign import ccall "arb.h arb_mul_arf"
  arb_mul_arf :: Ptr CArb -> Ptr CArb -> Ptr CArf -> CLong -> IO ()

foreign import ccall "arb.h arb_mul_si"
  arb_mul_si :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> IO ()

foreign import ccall "arb.h arb_mul_ui"
  arb_mul_ui :: Ptr CArb -> Ptr CArb -> CULong -> CLong -> IO ()

-- | /arb_mul_fmpz/ /z/ /x/ /y/ /prec/ 
-- 
-- Sets \(z = x \cdot y\), rounded to /prec/ bits. The precision can be
-- /ARF_PREC_EXACT/ provided that the result fits in memory.
foreign import ccall "arb.h arb_mul_fmpz"
  arb_mul_fmpz :: Ptr CArb -> Ptr CArb -> Ptr CFmpz -> CLong -> IO ()

foreign import ccall "arb.h arb_mul_2exp_si"
  arb_mul_2exp_si :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_mul_2exp_fmpz/ /y/ /x/ /e/ 
-- 
-- Sets /y/ to /x/ multiplied by \(2^e\).
foreign import ccall "arb.h arb_mul_2exp_fmpz"
  arb_mul_2exp_fmpz :: Ptr CArb -> Ptr CArb -> Ptr CFmpz -> IO ()

foreign import ccall "arb.h arb_addmul"
  arb_addmul :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()

foreign import ccall "arb.h arb_addmul_arf"
  arb_addmul_arf :: Ptr CArb -> Ptr CArb -> Ptr CArf -> CLong -> IO ()

foreign import ccall "arb.h arb_addmul_si"
  arb_addmul_si :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> IO ()

foreign import ccall "arb.h arb_addmul_ui"
  arb_addmul_ui :: Ptr CArb -> Ptr CArb -> CULong -> CLong -> IO ()

-- | /arb_addmul_fmpz/ /z/ /x/ /y/ /prec/ 
-- 
-- Sets \(z = z + x \cdot y\), rounded to prec bits. The precision can be
-- /ARF_PREC_EXACT/ provided that the result fits in memory.
foreign import ccall "arb.h arb_addmul_fmpz"
  arb_addmul_fmpz :: Ptr CArb -> Ptr CArb -> Ptr CFmpz -> CLong -> IO ()

foreign import ccall "arb.h arb_submul"
  arb_submul :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()

foreign import ccall "arb.h arb_submul_arf"
  arb_submul_arf :: Ptr CArb -> Ptr CArb -> Ptr CArf -> CLong -> IO ()

foreign import ccall "arb.h arb_submul_si"
  arb_submul_si :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> IO ()

foreign import ccall "arb.h arb_submul_ui"
  arb_submul_ui :: Ptr CArb -> Ptr CArb -> CULong -> CLong -> IO ()

-- | /arb_submul_fmpz/ /z/ /x/ /y/ /prec/ 
-- 
-- Sets \(z = z - x \cdot y\), rounded to prec bits. The precision can be
-- /ARF_PREC_EXACT/ provided that the result fits in memory.
foreign import ccall "arb.h arb_submul_fmpz"
  arb_submul_fmpz :: Ptr CArb -> Ptr CArb -> Ptr CFmpz -> CLong -> IO ()

-- | /arb_fma/ /res/ /x/ /y/ /z/ /prec/ 
-- 
-- Sets /res/ to \(x \cdot y + z\). This is equivalent to an /addmul/
-- except that /res/ and /z/ can be separate variables.
foreign import ccall "arb.h arb_fma"
  arb_fma :: Ptr CArb -> Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_inv/ /z/ /x/ /prec/ 
-- 
-- Sets /z/ to \(1 / x\).
foreign import ccall "arb.h arb_inv"
  arb_inv :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

foreign import ccall "arb.h arb_div"
  arb_div :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()

foreign import ccall "arb.h arb_div_arf"
  arb_div_arf :: Ptr CArb -> Ptr CArb -> Ptr CArf -> CLong -> IO ()

foreign import ccall "arb.h arb_div_si"
  arb_div_si :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> IO ()

foreign import ccall "arb.h arb_div_ui"
  arb_div_ui :: Ptr CArb -> Ptr CArb -> CULong -> CLong -> IO ()

foreign import ccall "arb.h arb_div_fmpz"
  arb_div_fmpz :: Ptr CArb -> Ptr CArb -> Ptr CFmpz -> CLong -> IO ()

foreign import ccall "arb.h arb_fmpz_div_fmpz"
  arb_fmpz_div_fmpz :: Ptr CArb -> Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- | /arb_ui_div/ /z/ /x/ /y/ /prec/ 
-- 
-- Sets \(z = x / y\), rounded to /prec/ bits. If /y/ contains zero, /z/ is
-- set to \(0 \pm \infty\). Otherwise, error propagation uses the rule
-- 
-- \[`
-- \left| \frac{x}{y} - \frac{x+\xi_1 a}{y+\xi_2 b} \right| =
-- \left|\frac{x \xi_2 b - y \xi_1 a}{y (y+\xi_2 b)}\right| \le
-- \frac{|xb|+|ya|}{|y| (|y|-b)}\]
-- 
-- where \(-1 \le \xi_1, \xi_2 \le 1\), and where the triangle inequality
-- has been applied to the numerator and the reverse triangle inequality
-- has been applied to the denominator.
foreign import ccall "arb.h arb_ui_div"
  arb_ui_div :: Ptr CArb -> CULong -> Ptr CArb -> CLong -> IO ()

-- | /arb_div_2expm1_ui/ /z/ /x/ /n/ /prec/ 
-- 
-- Sets \(z = x / (2^n - 1)\), rounded to /prec/ bits.
foreign import ccall "arb.h arb_div_2expm1_ui"
  arb_div_2expm1_ui :: Ptr CArb -> Ptr CArb -> CULong -> CLong -> IO ()

-- Dot product -----------------------------------------------------------------

-- | /arb_dot_precise/ /res/ /s/ /subtract/ /x/ /xstep/ /y/ /ystep/ /len/ /prec/ 
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
foreign import ccall "arb.h arb_dot_precise"
  arb_dot_precise :: Ptr CArb -> Ptr CArb -> CInt -> Ptr CArb -> CLong -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_approx_dot/ /res/ /s/ /subtract/ /x/ /xstep/ /y/ /ystep/ /len/ /prec/ 
-- 
-- Computes an approximate dot product /without error bounds/. The radii of
-- the inputs are ignored (only the midpoints are read) and only the
-- midpoint of the output is written.
foreign import ccall "arb.h arb_approx_dot"
  arb_approx_dot :: Ptr CArb -> Ptr CArb -> CInt -> Ptr CArb -> CLong -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_dot_ui/ /res/ /initial/ /subtract/ /x/ /xstep/ /y/ /ystep/ /len/ /prec/ 
-- 
-- Equivalent to @arb_dot@, but with integers in the array /y/. The /uiui/
-- and /siui/ versions take an array of double-limb integers as input; the
-- /siui/ version assumes that these represent signed integers in two\'s
-- complement form.
foreign import ccall "arb.h arb_dot_ui"
  arb_dot_ui :: Ptr CArb -> Ptr CArb -> CInt -> Ptr CArb -> CLong -> Ptr CULong -> CLong -> CLong -> CLong -> IO ()

-- Powers and roots ------------------------------------------------------------

foreign import ccall "arb.h arb_sqrt"
  arb_sqrt :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

foreign import ccall "arb.h arb_sqrt_arf"
  arb_sqrt_arf :: Ptr CArb -> Ptr CArf -> CLong -> IO ()

foreign import ccall "arb.h arb_sqrt_fmpz"
  arb_sqrt_fmpz :: Ptr CArb -> Ptr CFmpz -> CLong -> IO ()

-- | /arb_sqrt_ui/ /z/ /x/ /prec/ 
-- 
-- Sets /z/ to the square root of /x/, rounded to /prec/ bits.
-- 
-- If \(x = m \pm x\) where \(m \ge r \ge 0\), the propagated error is
-- bounded by
-- \(\sqrt{m} - \sqrt{m-r} = \sqrt{m} (1 - \sqrt{1 - r/m}) \le \sqrt{m} (r/m + (r/m)^2)/2\).
foreign import ccall "arb.h arb_sqrt_ui"
  arb_sqrt_ui :: Ptr CArb -> CULong -> CLong -> IO ()

-- | /arb_sqrtpos/ /z/ /x/ /prec/ 
-- 
-- Sets /z/ to the square root of /x/, assuming that /x/ represents a
-- nonnegative number (i.e. discarding any negative numbers in the input
-- interval).
foreign import ccall "arb.h arb_sqrtpos"
  arb_sqrtpos :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_hypot/ /z/ /x/ /y/ /prec/ 
-- 
-- Sets /z/ to \(\sqrt{x^2 + y^2}\).
foreign import ccall "arb.h arb_hypot"
  arb_hypot :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()

foreign import ccall "arb.h arb_rsqrt"
  arb_rsqrt :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_rsqrt_ui/ /z/ /x/ /prec/ 
-- 
-- Sets /z/ to the reciprocal square root of /x/, rounded to /prec/ bits.
-- At high precision, this is faster than computing a square root.
foreign import ccall "arb.h arb_rsqrt_ui"
  arb_rsqrt_ui :: Ptr CArb -> CULong -> CLong -> IO ()

-- | /arb_sqrt1pm1/ /z/ /x/ /prec/ 
-- 
-- Sets \(z = \sqrt{1+x}-1\), computed accurately when \(x \approx 0\).
foreign import ccall "arb.h arb_sqrt1pm1"
  arb_sqrt1pm1 :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_root_ui/ /z/ /x/ /k/ /prec/ 
-- 
-- Sets /z/ to the /k/-th root of /x/, rounded to /prec/ bits. This
-- function selects between different algorithms. For large /k/, it
-- evaluates \(\exp(\log(x)/k)\). For small /k/, it uses @arf_root@ at the
-- midpoint and computes a propagated error bound as follows: if input
-- interval is \([m-r, m+r]\) with \(r \le m\), the error is largest at
-- \(m-r\) where it satisfies
-- 
-- \[`\]
-- \[m^{1/k} - (m-r)^{1/k} = m^{1/k} [1 - (1-r/m)^{1/k}]\]
-- \[= m^{1/k} [1 - \exp(\log(1-r/m)/k)]\]
-- \[\le m^{1/k} \min(1, -\log(1-r/m)/k)\]
-- \[= m^{1/k} \min(1, \log(1+r/(m-r))/k).\]
-- 
-- This is evaluated using @mag_log1p@.
foreign import ccall "arb.h arb_root_ui"
  arb_root_ui :: Ptr CArb -> Ptr CArb -> CULong -> CLong -> IO ()

-- | /arb_root/ /z/ /x/ /k/ /prec/ 
-- 
-- Alias for @arb_root_ui@, provided for backwards compatibility.
foreign import ccall "arb.h arb_root"
  arb_root :: Ptr CArb -> Ptr CArb -> CULong -> CLong -> IO ()

-- | /arb_sqr/ /y/ /x/ /prec/ 
-- 
-- Sets /y/ to be the square of /x/.
foreign import ccall "arb.h arb_sqr"
  arb_sqr :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

foreign import ccall "arb.h arb_pow_fmpz_binexp"
  arb_pow_fmpz_binexp :: Ptr CArb -> Ptr CArb -> Ptr CFmpz -> CLong -> IO ()

foreign import ccall "arb.h arb_pow_fmpz"
  arb_pow_fmpz :: Ptr CArb -> Ptr CArb -> Ptr CFmpz -> CLong -> IO ()

foreign import ccall "arb.h arb_pow_ui"
  arb_pow_ui :: Ptr CArb -> Ptr CArb -> CULong -> CLong -> IO ()

foreign import ccall "arb.h arb_ui_pow_ui"
  arb_ui_pow_ui :: Ptr CArb -> CULong -> CULong -> CLong -> IO ()

-- | /arb_si_pow_ui/ /y/ /b/ /e/ /prec/ 
-- 
-- Sets \(y = b^e\) using binary exponentiation (with an initial division
-- if \(e < 0\)). Provided that /b/ and /e/ are small enough and the
-- exponent is positive, the exact power can be computed by setting the
-- precision to /ARF_PREC_EXACT/.
-- 
-- Note that these functions can get slow if the exponent is extremely
-- large (in such cases @arb_pow@ may be superior).
foreign import ccall "arb.h arb_si_pow_ui"
  arb_si_pow_ui :: Ptr CArb -> CLong -> CULong -> CLong -> IO ()

-- | /arb_pow_fmpq/ /y/ /x/ /a/ /prec/ 
-- 
-- Sets \(y = b^e\), computed as \(y = (b^{1/q})^p\) if the denominator of
-- \(e = p/q\) is small, and generally as \(y = \exp(e \log b)\).
-- 
-- Note that this function can get slow if the exponent is extremely large
-- (in such cases @arb_pow@ may be superior).
foreign import ccall "arb.h arb_pow_fmpq"
  arb_pow_fmpq :: Ptr CArb -> Ptr CArb -> Ptr CFmpq -> CLong -> IO ()

-- | /arb_pow/ /z/ /x/ /y/ /prec/ 
-- 
-- Sets \(z = x^y\), computed using binary exponentiation if \(y\) is a
-- small exact integer, as \(z = (x^{1/2})^{2y}\) if \(y\) is a small exact
-- half-integer, and generally as \(z = \exp(y \log x)\), except giving the
-- obvious finite result if \(x\) is \(a \pm a\) and \(y\) is positive.
foreign import ccall "arb.h arb_pow"
  arb_pow :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- Exponentials and logarithms -------------------------------------------------

foreign import ccall "arb.h arb_log_ui"
  arb_log_ui :: Ptr CArb -> CULong -> CLong -> IO ()

foreign import ccall "arb.h arb_log_fmpz"
  arb_log_fmpz :: Ptr CArb -> Ptr CFmpz -> CLong -> IO ()

foreign import ccall "arb.h arb_log_arf"
  arb_log_arf :: Ptr CArb -> Ptr CArf -> CLong -> IO ()

-- | /arb_log/ /z/ /x/ /prec/ 
-- 
-- Sets \(z = \log(x)\).
-- 
-- At low to medium precision (up to about 4096 bits), @arb_log_arf@ uses
-- table-based argument reduction and fast Taylor series evaluation via
-- @_arb_atan_taylor_rs@. At high precision, it falls back to MPFR. The
-- function @arb_log@ simply calls @arb_log_arf@ with the midpoint as
-- input, and separately adds the propagated error.
foreign import ccall "arb.h arb_log"
  arb_log :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_log_ui_from_prev/ /log_k1/ /k1/ /log_k0/ /k0/ /prec/ 
-- 
-- Computes \(\log(k_1)\), given \(\log(k_0)\) where \(k_0 < k_1\). At high
-- precision, this function uses the formula
-- \(\log(k_1) = \log(k_0) + 2 \operatorname{atanh}((k_1-k_0)/(k_1+k_0))\),
-- evaluating the inverse hyperbolic tangent using binary splitting (for
-- best efficiency, \(k_0\) should be large and \(k_1 - k_0\) should be
-- small). Otherwise, it ignores \(\log(k_0)\) and evaluates the logarithm
-- the usual way.
foreign import ccall "arb.h arb_log_ui_from_prev"
  arb_log_ui_from_prev :: Ptr CArb -> CULong -> Ptr CArb -> CULong -> CLong -> IO ()

-- | /arb_log1p/ /z/ /x/ /prec/ 
-- 
-- Sets \(z = \log(1+x)\), computed accurately when \(x \approx 0\).
foreign import ccall "arb.h arb_log1p"
  arb_log1p :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_log_base_ui/ /res/ /x/ /b/ /prec/ 
-- 
-- Sets /res/ to \(\log_b(x)\). The result is computed exactly when
-- possible.
foreign import ccall "arb.h arb_log_base_ui"
  arb_log_base_ui :: Ptr CArb -> Ptr CArb -> CULong -> CLong -> IO ()

-- | /arb_log_hypot/ /res/ /x/ /y/ /prec/ 
-- 
-- Sets /res/ to \(\log(\sqrt{x^2+y^2})\).
foreign import ccall "arb.h arb_log_hypot"
  arb_log_hypot :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_exp/ /z/ /x/ /prec/ 
-- 
-- Sets \(z = \exp(x)\). Error propagation is done using the following
-- rule: assuming \(x = m \pm r\), the error is largest at \(m + r\), and
-- we have \(\exp(m+r) - \exp(m) = \exp(m) (\exp(r)-1) \le r \exp(m+r)\).
foreign import ccall "arb.h arb_exp"
  arb_exp :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_expm1/ /z/ /x/ /prec/ 
-- 
-- Sets \(z = \exp(x)-1\), using a more accurate method when
-- \(x \approx 0\).
foreign import ccall "arb.h arb_expm1"
  arb_expm1 :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_exp_invexp/ /z/ /w/ /x/ /prec/ 
-- 
-- Sets \(z = \exp(x)\) and \(w = \exp(-x)\). The second exponential is
-- computed from the first using a division, but propagated error bounds
-- are computed separately.
foreign import ccall "arb.h arb_exp_invexp"
  arb_exp_invexp :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- Trigonometric functions -----------------------------------------------------

foreign import ccall "arb.h arb_sin"
  arb_sin :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

foreign import ccall "arb.h arb_cos"
  arb_cos :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_sin_cos/ /s/ /c/ /x/ /prec/ 
-- 
-- Sets \(s = \sin(x)\), \(c = \cos(x)\).
foreign import ccall "arb.h arb_sin_cos"
  arb_sin_cos :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()

foreign import ccall "arb.h arb_sin_pi"
  arb_sin_pi :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

foreign import ccall "arb.h arb_cos_pi"
  arb_cos_pi :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_sin_cos_pi/ /s/ /c/ /x/ /prec/ 
-- 
-- Sets \(s = \sin(\pi x)\), \(c = \cos(\pi x)\).
foreign import ccall "arb.h arb_sin_cos_pi"
  arb_sin_cos_pi :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_tan/ /y/ /x/ /prec/ 
-- 
-- Sets \(y = \tan(x) = \sin(x) / \cos(y)\).
foreign import ccall "arb.h arb_tan"
  arb_tan :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_cot/ /y/ /x/ /prec/ 
-- 
-- Sets \(y = \cot(x) = \cos(x) / \sin(y)\).
foreign import ccall "arb.h arb_cot"
  arb_cot :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

foreign import ccall "arb.h arb_sin_cos_pi_fmpq"
  arb_sin_cos_pi_fmpq :: Ptr CArb -> Ptr CArb -> Ptr CFmpq -> CLong -> IO ()

foreign import ccall "arb.h arb_sin_pi_fmpq"
  arb_sin_pi_fmpq :: Ptr CArb -> Ptr CFmpq -> CLong -> IO ()

-- | /arb_cos_pi_fmpq/ /c/ /x/ /prec/ 
-- 
-- Sets \(s = \sin(\pi x)\), \(c = \cos(\pi x)\) where \(x\) is a rational
-- number (whose numerator and denominator are assumed to be reduced). We
-- first use trigonometric symmetries to reduce the argument to the octant
-- \([0, 1/4]\). Then we either multiply by a numerical approximation of
-- \(\pi\) and evaluate the trigonometric function the usual way, or we use
-- algebraic methods, depending on which is estimated to be faster. Since
-- the argument has been reduced to the first octant, the first of these
-- two methods gives full accuracy even if the original argument is close
-- to some root other the origin.
foreign import ccall "arb.h arb_cos_pi_fmpq"
  arb_cos_pi_fmpq :: Ptr CArb -> Ptr CFmpq -> CLong -> IO ()

-- | /arb_tan_pi/ /y/ /x/ /prec/ 
-- 
-- Sets \(y = \tan(\pi x)\).
foreign import ccall "arb.h arb_tan_pi"
  arb_tan_pi :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_cot_pi/ /y/ /x/ /prec/ 
-- 
-- Sets \(y = \cot(\pi x)\).
foreign import ccall "arb.h arb_cot_pi"
  arb_cot_pi :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_sec/ /res/ /x/ /prec/ 
-- 
-- Computes \(\sec(x) = 1 / \cos(x)\).
foreign import ccall "arb.h arb_sec"
  arb_sec :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_csc/ /res/ /x/ /prec/ 
-- 
-- Computes \(\csc(x) = 1 / \sin(x)\).
foreign import ccall "arb.h arb_csc"
  arb_csc :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_csc_pi/ /res/ /x/ /prec/ 
-- 
-- Computes \(\csc(\pi x) = 1 / \sin(\pi x)\).
foreign import ccall "arb.h arb_csc_pi"
  arb_csc_pi :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_sinc/ /z/ /x/ /prec/ 
-- 
-- Sets \(z = \operatorname{sinc}(x) = \sin(x) / x\).
foreign import ccall "arb.h arb_sinc"
  arb_sinc :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_sinc_pi/ /z/ /x/ /prec/ 
-- 
-- Sets \(z = \operatorname{sinc}(\pi x) = \sin(\pi x) / (\pi x)\).
foreign import ccall "arb.h arb_sinc_pi"
  arb_sinc_pi :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- Inverse trigonometric functions ---------------------------------------------

foreign import ccall "arb.h arb_atan_arf"
  arb_atan_arf :: Ptr CArb -> Ptr CArf -> CLong -> IO ()

-- | /arb_atan/ /z/ /x/ /prec/ 
-- 
-- Sets \(z = \operatorname{atan}(x)\).
-- 
-- At low to medium precision (up to about 4096 bits), @arb_atan_arf@ uses
-- table-based argument reduction and fast Taylor series evaluation via
-- @_arb_atan_taylor_rs@. At high precision, it falls back to MPFR. The
-- function @arb_atan@ simply calls @arb_atan_arf@ with the midpoint as
-- input, and separately adds the propagated error.
-- 
-- The function @arb_atan_arf@ uses lookup tables if possible, and
-- otherwise falls back to @arb_atan_arf_bb@.
foreign import ccall "arb.h arb_atan"
  arb_atan :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_atan2/ /z/ /b/ /a/ /prec/ 
-- 
-- Sets /r/ to an the argument (phase) of the complex number \(a + bi\),
-- with the branch cut discontinuity on \((-\infty,0]\). We define
-- \(\operatorname{atan2}(0,0) = 0\), and for \(a < 0\),
-- \(\operatorname{atan2}(0,a) = \pi\).
foreign import ccall "arb.h arb_atan2"
  arb_atan2 :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_asin/ /z/ /x/ /prec/ 
-- 
-- Sets
-- \(z = \operatorname{asin}(x) = \operatorname{atan}(x / \sqrt{1-x^2})\).
-- If \(x\) is not contained in the domain \([-1,1]\), the result is an
-- indeterminate interval.
foreign import ccall "arb.h arb_asin"
  arb_asin :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_acos/ /z/ /x/ /prec/ 
-- 
-- Sets \(z = \operatorname{acos}(x) = \pi/2 - \operatorname{asin}(x)\). If
-- \(x\) is not contained in the domain \([-1,1]\), the result is an
-- indeterminate interval.
foreign import ccall "arb.h arb_acos"
  arb_acos :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- Hyperbolic functions --------------------------------------------------------

foreign import ccall "arb.h arb_sinh"
  arb_sinh :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

foreign import ccall "arb.h arb_cosh"
  arb_cosh :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_sinh_cosh/ /s/ /c/ /x/ /prec/ 
-- 
-- Sets \(s = \sinh(x)\), \(c = \cosh(x)\). If the midpoint of \(x\) is
-- close to zero and the hyperbolic sine is to be computed, evaluates
-- \((e^{2x}\pm1) / (2e^x)\) via @arb_expm1@ to avoid loss of accuracy.
-- Otherwise evaluates \((e^x \pm e^{-x}) / 2\).
foreign import ccall "arb.h arb_sinh_cosh"
  arb_sinh_cosh :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_tanh/ /y/ /x/ /prec/ 
-- 
-- Sets \(y = \tanh(x) = \sinh(x) / \cosh(x)\), evaluated via @arb_expm1@
-- as \(\tanh(x) = (e^{2x} - 1) / (e^{2x} + 1)\) if \(|x|\) is small, and
-- as \(\tanh(\pm x) = 1 - 2 e^{\mp 2x} / (1 + e^{\mp 2x})\) if \(|x|\) is
-- large.
foreign import ccall "arb.h arb_tanh"
  arb_tanh :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_coth/ /y/ /x/ /prec/ 
-- 
-- Sets \(y = \coth(x) = \cosh(x) / \sinh(x)\), evaluated using the same
-- strategy as @arb_tanh@.
foreign import ccall "arb.h arb_coth"
  arb_coth :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_sech/ /res/ /x/ /prec/ 
-- 
-- Computes \(\operatorname{sech}(x) = 1 / \cosh(x)\).
foreign import ccall "arb.h arb_sech"
  arb_sech :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_csch/ /res/ /x/ /prec/ 
-- 
-- Computes \(\operatorname{csch}(x) = 1 / \sinh(x)\).
foreign import ccall "arb.h arb_csch"
  arb_csch :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- Inverse hyperbolic functions ------------------------------------------------

-- | /arb_atanh/ /z/ /x/ /prec/ 
-- 
-- Sets \(z = \operatorname{atanh}(x)\).
foreign import ccall "arb.h arb_atanh"
  arb_atanh :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_asinh/ /z/ /x/ /prec/ 
-- 
-- Sets \(z = \operatorname{asinh}(x)\).
foreign import ccall "arb.h arb_asinh"
  arb_asinh :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_acosh/ /z/ /x/ /prec/ 
-- 
-- Sets \(z = \operatorname{acosh}(x)\). If \(x < 1\), the result is an
-- indeterminate interval.
foreign import ccall "arb.h arb_acosh"
  arb_acosh :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- Constants -------------------------------------------------------------------

-- The following functions cache the computed values to speed up repeated
-- calls at the same or lower precision. For further implementation
-- details, see @algorithms_constants@.
--
-- | /arb_const_pi/ /z/ /prec/ 
-- 
-- Computes \(\pi\).
foreign import ccall "arb.h arb_const_pi"
  arb_const_pi :: Ptr CArb -> CLong -> IO ()

-- | /arb_const_sqrt_pi/ /z/ /prec/ 
-- 
-- Computes \(\sqrt{\pi}\).
foreign import ccall "arb.h arb_const_sqrt_pi"
  arb_const_sqrt_pi :: Ptr CArb -> CLong -> IO ()

-- | /arb_const_log_sqrt2pi/ /z/ /prec/ 
-- 
-- Computes \(\log \sqrt{2 \pi}\).
foreign import ccall "arb.h arb_const_log_sqrt2pi"
  arb_const_log_sqrt2pi :: Ptr CArb -> CLong -> IO ()

-- | /arb_const_log2/ /z/ /prec/ 
-- 
-- Computes \(\log(2)\).
foreign import ccall "arb.h arb_const_log2"
  arb_const_log2 :: Ptr CArb -> CLong -> IO ()

-- | /arb_const_log10/ /z/ /prec/ 
-- 
-- Computes \(\log(10)\).
foreign import ccall "arb.h arb_const_log10"
  arb_const_log10 :: Ptr CArb -> CLong -> IO ()

-- | /arb_const_euler/ /z/ /prec/ 
-- 
-- Computes Euler\'s constant
-- \(\gamma = \lim_{k \rightarrow \infty} (H_k - \log k)\) where
-- \(H_k = 1 + 1/2 + \ldots + 1/k\).
foreign import ccall "arb.h arb_const_euler"
  arb_const_euler :: Ptr CArb -> CLong -> IO ()

-- | /arb_const_catalan/ /z/ /prec/ 
-- 
-- Computes Catalan\'s constant
-- \(C = \sum_{n=0}^{\infty} (-1)^n / (2n+1)^2\).
foreign import ccall "arb.h arb_const_catalan"
  arb_const_catalan :: Ptr CArb -> CLong -> IO ()

-- | /arb_const_e/ /z/ /prec/ 
-- 
-- Computes \(e = \exp(1)\).
foreign import ccall "arb.h arb_const_e"
  arb_const_e :: Ptr CArb -> CLong -> IO ()

-- | /arb_const_khinchin/ /z/ /prec/ 
-- 
-- Computes Khinchin\'s constant \(K_0\).
foreign import ccall "arb.h arb_const_khinchin"
  arb_const_khinchin :: Ptr CArb -> CLong -> IO ()

-- | /arb_const_glaisher/ /z/ /prec/ 
-- 
-- Computes the Glaisher-Kinkelin constant \(A = \exp(1/12 - \zeta'(-1))\).
foreign import ccall "arb.h arb_const_glaisher"
  arb_const_glaisher :: Ptr CArb -> CLong -> IO ()

-- | /arb_const_apery/ /z/ /prec/ 
-- 
-- Computes Apery\'s constant \(\zeta(3)\).
foreign import ccall "arb.h arb_const_apery"
  arb_const_apery :: Ptr CArb -> CLong -> IO ()

-- Lambert W function ----------------------------------------------------------

-- | /arb_lambertw/ /res/ /x/ /flags/ /prec/ 
-- 
-- Computes the Lambert W function, which solves the equation
-- \(w e^w = x\).
-- 
-- The Lambert W function has infinitely many complex branches \(W_k(x)\),
-- two of which are real on a part of the real line. The principal branch
-- \(W_0(x)\) is selected by setting /flags/ to 0, and the \(W_{-1}\)
-- branch is selected by setting /flags/ to 1. The principal branch is
-- real-valued for \(x \ge -1/e\) (taking values in \([-1,+\infty)\)) and
-- the \(W_{-1}\) branch is real-valued for \(-1/e \le x < 0\) and takes
-- values in \((-\infty,-1]\). Elsewhere, the Lambert W function is complex
-- and @acb_lambertw@ should be used.
-- 
-- The implementation first computes a floating-point approximation
-- heuristically and then computes a rigorously certified enclosure around
-- this approximation. Some asymptotic cases are handled specially. The
-- algorithm used to compute the Lambert W function is described in
-- < [Joh2017b]>, which follows the main ideas in < [CGHJK1996]>.
foreign import ccall "arb.h arb_lambertw"
  arb_lambertw :: Ptr CArb -> Ptr CArb -> CInt -> CLong -> IO ()

-- Gamma function and factorials -----------------------------------------------

-- | /arb_rising_ui/ /z/ /x/ /n/ /prec/ 
-- 
-- Computes the rising factorial \(z = x (x+1) (x+2) \cdots (x+n-1)\).
-- These functions are aliases for @arb_hypgeom_rising_ui@ and
-- @arb_hypgeom_rising@.
foreign import ccall "arb.h arb_rising_ui"
  arb_rising_ui :: Ptr CArb -> Ptr CArb -> CULong -> CLong -> IO ()

-- | /arb_rising_fmpq_ui/ /z/ /x/ /n/ /prec/ 
-- 
-- Computes the rising factorial \(z = x (x+1) (x+2) \cdots (x+n-1)\) using
-- binary splitting. If the denominator or numerator of /x/ is large
-- compared to /prec/, it is more efficient to convert /x/ to an
-- approximation and use @arb_rising_ui@.
foreign import ccall "arb.h arb_rising_fmpq_ui"
  arb_rising_fmpq_ui :: Ptr CArb -> Ptr CFmpq -> CULong -> CLong -> IO ()




-- | /arb_fac_ui/ /z/ /n/ /prec/ 
-- 
-- Computes the factorial \(z = n!\) via the gamma function.
foreign import ccall "arb.h arb_fac_ui"
  arb_fac_ui :: Ptr CArb -> CULong -> CLong -> IO ()

-- | /arb_doublefac_ui/ /z/ /n/ /prec/ 
-- 
-- Computes the double factorial \(z = n!!\) via the gamma function.
foreign import ccall "arb.h arb_doublefac_ui"
  arb_doublefac_ui :: Ptr CArb -> CULong -> CLong -> IO ()

foreign import ccall "arb.h arb_bin_ui"
  arb_bin_ui :: Ptr CArb -> Ptr CArb -> CULong -> CLong -> IO ()

-- | /arb_bin_uiui/ /z/ /n/ /k/ /prec/ 
-- 
-- Computes the binomial coefficient \(z = {n \choose k}\), via the rising
-- factorial as \({n \choose k} = (n-k+1)_k / k!\).
foreign import ccall "arb.h arb_bin_uiui"
  arb_bin_uiui :: Ptr CArb -> CULong -> CULong -> CLong -> IO ()

-- | /arb_gamma/ /z/ /x/ /prec/ 
-- 
-- Computes the gamma function \(z = \Gamma(x)\).
-- 
-- These functions are aliases for @arb_hypgeom_gamma@,
-- @arb_hypgeom_gamma_fmpq@, @arb_hypgeom_gamma_fmpz@.
foreign import ccall "arb.h arb_gamma"
  arb_gamma :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_lgamma/ /z/ /x/ /prec/ 
-- 
-- Computes the logarithmic gamma function \(z = \log \Gamma(x)\). The
-- complex branch structure is assumed, so if \(x \le 0\), the result is an
-- indeterminate interval. This function is an alias for
-- @arb_hypgeom_lgamma@.
foreign import ccall "arb.h arb_lgamma"
  arb_lgamma :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_rgamma/ /z/ /x/ /prec/ 
-- 
-- Computes the reciprocal gamma function \(z = 1/\Gamma(x)\), avoiding
-- division by zero at the poles of the gamma function. This function is an
-- alias for @arb_hypgeom_rgamma@.
foreign import ccall "arb.h arb_rgamma"
  arb_rgamma :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_digamma/ /y/ /x/ /prec/ 
-- 
-- Computes the digamma function
-- \(z = \psi(x) = (\log \Gamma(x))' = \Gamma'(x) / \Gamma(x)\).
foreign import ccall "arb.h arb_digamma"
  arb_digamma :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- Zeta function ---------------------------------------------------------------

-- | /arb_zeta_ui_vec_borwein/ /z/ /start/ /num/ /step/ /prec/ 
-- 
-- Evaluates \(\zeta(s)\) at \(\mathrm{num}\) consecutive integers /s/
-- beginning with /start/ and proceeding in increments of /step/. Uses
-- Borwein\'s formula (< [Bor2000]>, < [GS2003]>), implemented to support
-- fast multi-evaluation (but also works well for a single /s/).
-- 
-- Requires \(\mathrm{start} \ge 2\). For efficiency, the largest /s/
-- should be at most about as large as /prec/. Arguments approaching
-- /LONG_MAX/ will cause overflows. One should therefore only use this
-- function for /s/ up to about /prec/, and then switch to the Euler
-- product.
-- 
-- The algorithm for single /s/ is basically identical to the one used in
-- MPFR (see < [MPFR2012]> for a detailed description). In particular, we
-- evaluate the sum backwards to avoid storing more than one \(d_k\)
-- coefficient, and use integer arithmetic throughout since it is
-- convenient and the terms turn out to be slightly larger than
-- \(2^\mathrm{prec}\). The only numerical error in the main loop comes
-- from the division by \(k^s\), which adds less than 1 unit of error per
-- term. For fast multi-evaluation, we repeatedly divide by
-- \(k^{\mathrm{step}}\). Each division reduces the input error and adds at
-- most 1 unit of additional rounding error, so by induction, the error per
-- term is always smaller than 2 units.
foreign import ccall "arb.h arb_zeta_ui_vec_borwein"
  arb_zeta_ui_vec_borwein :: Ptr CArb -> CULong -> CLong -> CULong -> CLong -> IO ()

foreign import ccall "arb.h arb_zeta_ui_asymp"
  arb_zeta_ui_asymp :: Ptr CArb -> CULong -> CLong -> IO ()

-- | /arb_zeta_ui_euler_product/ /z/ /s/ /prec/ 
-- 
-- Computes \(\zeta(s)\) using the Euler product. This is fast only if /s/
-- is large compared to the precision. Both methods are trivial wrappers
-- for @_acb_dirichlet_euler_product_real_ui@.
foreign import ccall "arb.h arb_zeta_ui_euler_product"
  arb_zeta_ui_euler_product :: Ptr CArb -> CULong -> CLong -> IO ()

-- | /arb_zeta_ui_bernoulli/ /x/ /s/ /prec/ 
-- 
-- Computes \(\zeta(s)\) for even /s/ via the corresponding Bernoulli
-- number.
foreign import ccall "arb.h arb_zeta_ui_bernoulli"
  arb_zeta_ui_bernoulli :: Ptr CArb -> CULong -> CLong -> IO ()

-- | /arb_zeta_ui_borwein_bsplit/ /x/ /s/ /prec/ 
-- 
-- Computes \(\zeta(s)\) for arbitrary \(s \ge 2\) using a binary splitting
-- implementation of Borwein\'s algorithm. This has quasilinear complexity
-- with respect to the precision (assuming that \(s\) is fixed).
foreign import ccall "arb.h arb_zeta_ui_borwein_bsplit"
  arb_zeta_ui_borwein_bsplit :: Ptr CArb -> CULong -> CLong -> IO ()

foreign import ccall "arb.h arb_zeta_ui_vec"
  arb_zeta_ui_vec :: Ptr CArb -> CULong -> CLong -> CLong -> IO ()

foreign import ccall "arb.h arb_zeta_ui_vec_even"
  arb_zeta_ui_vec_even :: Ptr CArb -> CULong -> CLong -> CLong -> IO ()

-- | /arb_zeta_ui_vec_odd/ /x/ /start/ /num/ /prec/ 
-- 
-- Computes \(\zeta(s)\) at /num/ consecutive integers (respectively /num/
-- even or /num/ odd integers) beginning with \(s = \mathrm{start} \ge 2\),
-- automatically choosing an appropriate algorithm.
foreign import ccall "arb.h arb_zeta_ui_vec_odd"
  arb_zeta_ui_vec_odd :: Ptr CArb -> CULong -> CLong -> CLong -> IO ()

-- | /arb_zeta_ui/ /x/ /s/ /prec/ 
-- 
-- Computes \(\zeta(s)\) for nonnegative integer \(s \ne 1\), automatically
-- choosing an appropriate algorithm. This function is intended for
-- numerical evaluation of isolated zeta values; for multi-evaluation, the
-- vector versions are more efficient.
foreign import ccall "arb.h arb_zeta_ui"
  arb_zeta_ui :: Ptr CArb -> CULong -> CLong -> IO ()

-- | /arb_zeta/ /z/ /s/ /prec/ 
-- 
-- Sets /z/ to the value of the Riemann zeta function \(\zeta(s)\).
-- 
-- For computing derivatives with respect to \(s\), use
-- @arb_poly_zeta_series@.
foreign import ccall "arb.h arb_zeta"
  arb_zeta :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_hurwitz_zeta/ /z/ /s/ /a/ /prec/ 
-- 
-- Sets /z/ to the value of the Hurwitz zeta function \(\zeta(s,a)\).
-- 
-- For computing derivatives with respect to \(s\), use
-- @arb_poly_zeta_series@.
foreign import ccall "arb.h arb_hurwitz_zeta"
  arb_hurwitz_zeta :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- Bernoulli numbers and polynomials -------------------------------------------

foreign import ccall "arb.h arb_bernoulli_ui"
  arb_bernoulli_ui :: Ptr CArb -> CULong -> CLong -> IO ()

-- | /arb_bernoulli_fmpz/ /b/ /n/ /prec/ 
-- 
-- Sets \(b\) to the numerical value of the Bernoulli number \(B_n\)
-- approximated to /prec/ bits.
-- 
-- The internal precision is increased automatically to give an accurate
-- result. Note that, with huge /fmpz/ input, the output will have a huge
-- exponent and evaluation will accordingly be slower.
-- 
-- A single division from the exact fraction of \(B_n\) is used if this
-- value is in the global cache or the exact numerator roughly is larger
-- than /prec/ bits. Otherwise, the Riemann zeta function is used (see
-- @arb_bernoulli_ui_zeta@).
-- 
-- This function reads \(B_n\) from the global cache if the number is
-- already cached, but does not automatically extend the cache by itself.
foreign import ccall "arb.h arb_bernoulli_fmpz"
  arb_bernoulli_fmpz :: Ptr CArb -> Ptr CFmpz -> CLong -> IO ()

-- | /arb_bernoulli_ui_zeta/ /b/ /n/ /prec/ 
-- 
-- Sets \(b\) to the numerical value of \(B_n\) accurate to /prec/ bits,
-- computed using the formula
-- \(B_{2n} = (-1)^{n+1} 2 (2n)! \zeta(2n) / (2 \pi)^n\).
-- 
-- To avoid potential infinite recursion, we explicitly call the Euler
-- product implementation of the zeta function. This method will only give
-- high accuracy if the precision is small enough compared to \(n\) for the
-- Euler product to converge rapidly.
foreign import ccall "arb.h arb_bernoulli_ui_zeta"
  arb_bernoulli_ui_zeta :: Ptr CArb -> CULong -> CLong -> IO ()

-- | /arb_bernoulli_poly_ui/ /res/ /n/ /x/ /prec/ 
-- 
-- Sets /res/ to the value of the Bernoulli polynomial \(B_n(x)\).
-- 
-- Warning: this function is only fast if either /n/ or /x/ is a small
-- integer.
-- 
-- This function reads Bernoulli numbers from the global cache if they are
-- already cached, but does not automatically extend the cache by itself.
foreign import ccall "arb.h arb_bernoulli_poly_ui"
  arb_bernoulli_poly_ui :: Ptr CArb -> CULong -> Ptr CArb -> CLong -> IO ()

-- | /arb_power_sum_vec/ /res/ /a/ /b/ /len/ /prec/ 
-- 
-- For /n/ from 0 to /len/ - 1, sets entry /n/ in the output vector /res/
-- to
-- 
-- \[`\]
-- \[S_n(a,b) = \frac{1}{n+1}\left(B_{n+1}(b) - B_{n+1}(a)\right)\]
-- 
-- where \(B_n(x)\) is a Bernoulli polynomial. If /a/ and /b/ are integers
-- and \(b \ge a\), this is equivalent to
-- 
-- \[`\]
-- \[S_n(a,b) = \sum_{k=a}^{b-1} k^n.\]
-- 
-- The computation uses the generating function for Bernoulli polynomials.
foreign import ccall "arb.h arb_power_sum_vec"
  arb_power_sum_vec :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> CLong -> IO ()

-- Polylogarithms --------------------------------------------------------------

foreign import ccall "arb.h arb_polylog"
  arb_polylog :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_polylog_si/ /w/ /s/ /z/ /prec/ 
-- 
-- Sets /w/ to the polylogarithm \(\operatorname{Li}_s(z)\).
foreign import ccall "arb.h arb_polylog_si"
  arb_polylog_si :: Ptr CArb -> CLong -> Ptr CArb -> CLong -> IO ()

-- Other special functions -----------------------------------------------------

-- | /arb_fib_fmpz/ /z/ /n/ /prec/ 
-- 
-- Computes the Fibonacci number \(F_n\) using binary squaring.
foreign import ccall "arb.h arb_fib_fmpz"
  arb_fib_fmpz :: Ptr CArb -> Ptr CFmpz -> CLong -> IO ()

-- | /arb_agm/ /z/ /x/ /y/ /prec/ 
-- 
-- Sets /z/ to the arithmetic-geometric mean of /x/ and /y/.
foreign import ccall "arb.h arb_agm"
  arb_agm :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()

foreign import ccall "arb.h arb_chebyshev_t_ui"
  arb_chebyshev_t_ui :: Ptr CArb -> CULong -> Ptr CArb -> CLong -> IO ()

-- | /arb_chebyshev_u_ui/ /a/ /n/ /x/ /prec/ 
-- 
-- Evaluates the Chebyshev polynomial of the first kind \(a = T_n(x)\) or
-- the Chebyshev polynomial of the second kind \(a = U_n(x)\).
foreign import ccall "arb.h arb_chebyshev_u_ui"
  arb_chebyshev_u_ui :: Ptr CArb -> CULong -> Ptr CArb -> CLong -> IO ()

foreign import ccall "arb.h arb_chebyshev_t2_ui"
  arb_chebyshev_t2_ui :: Ptr CArb -> Ptr CArb -> CULong -> Ptr CArb -> CLong -> IO ()

-- | /arb_chebyshev_u2_ui/ /a/ /b/ /n/ /x/ /prec/ 
-- 
-- Simultaneously evaluates \(a = T_n(x), b = T_{n-1}(x)\) or
-- \(a = U_n(x), b = U_{n-1}(x)\). Aliasing between /a/, /b/ and /x/ is not
-- permitted.
foreign import ccall "arb.h arb_chebyshev_u2_ui"
  arb_chebyshev_u2_ui :: Ptr CArb -> Ptr CArb -> CULong -> Ptr CArb -> CLong -> IO ()

foreign import ccall "arb.h arb_bell_sum_bsplit"
  arb_bell_sum_bsplit :: Ptr CArb -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- | /arb_bell_sum_taylor/ /res/ /n/ /a/ /b/ /mmag/ /prec/ 
-- 
-- Helper functions for Bell numbers, evaluating the sum
-- \(\sum_{k=a}^{b-1} k^n / k!\). If /mmag/ is non-NULL, it may be used to
-- indicate that the target error tolerance should be \(2^{mmag - prec}\).
foreign import ccall "arb.h arb_bell_sum_taylor"
  arb_bell_sum_taylor :: Ptr CArb -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

foreign import ccall "arb.h arb_bell_fmpz"
  arb_bell_fmpz :: Ptr CArb -> Ptr CFmpz -> CLong -> IO ()

-- | /arb_bell_ui/ /res/ /n/ /prec/ 
-- 
-- Sets /res/ to the Bell number \(B_n\). If the number is too large to fit
-- exactly in /prec/ bits, a numerical approximation is computed
-- efficiently.
-- 
-- The algorithm to compute Bell numbers, including error analysis, is
-- described in detail in < [Joh2015]>.
foreign import ccall "arb.h arb_bell_ui"
  arb_bell_ui :: Ptr CArb -> CULong -> CLong -> IO ()

-- | /arb_euler_number_fmpz/ /res/ /n/ /prec/ 
-- 
-- Sets /res/ to the Euler number \(E_n\), which is defined by the
-- exponential generating function \(1 / \cosh(x)\). The result will be
-- exact if \(E_n\) is exactly representable at the requested precision.
foreign import ccall "arb.h arb_euler_number_fmpz"
  arb_euler_number_fmpz :: Ptr CArb -> Ptr CFmpz -> CLong -> IO ()

-- | /arb_fmpz_euler_number_ui_multi_mod/ /res/ /n/ /alpha/ 
-- 
-- Computes the Euler number \(E_n\) as an exact integer. The default
-- algorithm uses a table lookup, the Dirichlet beta function or a hybrid
-- modular algorithm depending on the size of /n/. The /multi_mod/
-- algorithm accepts a tuning parameter /alpha/ which can be set to a
-- negative value to use defaults.
foreign import ccall "arb.h arb_fmpz_euler_number_ui_multi_mod"
  arb_fmpz_euler_number_ui_multi_mod :: Ptr CFmpz -> CULong -> CDouble -> IO ()

foreign import ccall "arb.h arb_partitions_fmpz"
  arb_partitions_fmpz :: Ptr CArb -> Ptr CFmpz -> CLong -> IO ()

-- | /arb_partitions_ui/ /res/ /n/ /prec/ 
-- 
-- Sets /res/ to the partition function \(p(n)\). When /n/ is large and
-- \(\log_2 p(n)\) is more than twice /prec/, the leading term in the
-- Hardy-Ramanujan asymptotic series is used together with an error bound.
-- Otherwise, the exact value is computed and rounded.
foreign import ccall "arb.h arb_partitions_ui"
  arb_partitions_ui :: Ptr CArb -> CULong -> CLong -> IO ()

-- | /arb_primorial_nth_ui/ /res/ /n/ /prec/ 
-- 
-- Sets /res/ to the /nth/ primorial, defined as the product of the first
-- /n/ prime numbers. The running time is quasilinear in /n/.
foreign import ccall "arb.h arb_primorial_nth_ui"
  arb_primorial_nth_ui :: Ptr CArb -> CULong -> CLong -> IO ()

-- | /arb_primorial_ui/ /res/ /n/ /prec/ 
-- 
-- Sets /res/ to the primorial defined as the product of the positive
-- integers up to and including /n/. The running time is quasilinear in
-- /n/.
foreign import ccall "arb.h arb_primorial_ui"
  arb_primorial_ui :: Ptr CArb -> CULong -> CLong -> IO ()

-- Internals for computing elementary functions --------------------------------

foreign import ccall "arb.h _arb_atan_taylor_naive"
  _arb_atan_taylor_naive :: Ptr CMp -> Ptr CMpLimb -> Ptr CMp -> CMpSize -> CULong -> CInt -> IO ()

-- | /_arb_atan_taylor_rs/ /y/ /error/ /x/ /xn/ /N/ /alternating/ 
-- 
-- Computes an approximation of \(y = \sum_{k=0}^{N-1} x^{2k+1} / (2k+1)\)
-- (if /alternating/ is 0) or
-- \(y = \sum_{k=0}^{N-1} (-1)^k x^{2k+1} / (2k+1)\) (if /alternating/ is
-- 1). Used internally for computing arctangents and logarithms. The
-- /naive/ version uses the forward recurrence, and the /rs/ version uses a
-- division-avoiding rectangular splitting scheme.
-- 
-- Requires \(N \le 255\), \(0 \le x \le 1/16\), and /xn/ positive. The
-- input /x/ and output /y/ are fixed-point numbers with /xn/ fractional
-- limbs. A bound for the ulp error is written to /error/.
foreign import ccall "arb.h _arb_atan_taylor_rs"
  _arb_atan_taylor_rs :: Ptr CMp -> Ptr CMpLimb -> Ptr CMp -> CMpSize -> CULong -> CInt -> IO ()

foreign import ccall "arb.h _arb_exp_taylor_naive"
  _arb_exp_taylor_naive :: Ptr CMp -> Ptr CMpLimb -> Ptr CMp -> CMpSize -> CULong -> IO ()

-- | /_arb_exp_taylor_rs/ /y/ /error/ /x/ /xn/ /N/ 
-- 
-- Computes an approximation of \(y = \sum_{k=0}^{N-1} x^k / k!\). Used
-- internally for computing exponentials. The /naive/ version uses the
-- forward recurrence, and the /rs/ version uses a division-avoiding
-- rectangular splitting scheme.
-- 
-- Requires \(N \le 287\), \(0 \le x \le 1/16\), and /xn/ positive. The
-- input /x/ is a fixed-point number with /xn/ fractional limbs, and the
-- output /y/ is a fixed-point number with /xn/ fractional limbs plus one
-- extra limb for the integer part of the result.
-- 
-- A bound for the ulp error is written to /error/.
foreign import ccall "arb.h _arb_exp_taylor_rs"
  _arb_exp_taylor_rs :: Ptr CMp -> Ptr CMpLimb -> Ptr CMp -> CMpSize -> CULong -> IO ()

foreign import ccall "arb.h _arb_sin_cos_taylor_naive"
  _arb_sin_cos_taylor_naive :: Ptr CMp -> Ptr CMp -> Ptr CMpLimb -> Ptr CMp -> CMpSize -> CULong -> IO ()

-- | /_arb_sin_cos_taylor_rs/ /ysin/ /ycos/ /error/ /x/ /xn/ /N/ /sinonly/ /alternating/ 
-- 
-- Computes approximations of
-- \(y_s = \sum_{k=0}^{N-1} (-1)^k x^{2k+1} / (2k+1)!\) and
-- \(y_c = \sum_{k=0}^{N-1} (-1)^k x^{2k} / (2k)!\). Used internally for
-- computing sines and cosines. The /naive/ version uses the forward
-- recurrence, and the /rs/ version uses a division-avoiding rectangular
-- splitting scheme.
-- 
-- Requires \(N \le 143\), \(0 \le x \le 1/16\), and /xn/ positive. The
-- input /x/ and outputs /ysin/, /ycos/ are fixed-point numbers with /xn/
-- fractional limbs. A bound for the ulp error is written to /error/.
-- 
-- If /sinonly/ is 1, only the sine is computed; if /sinonly/ is 0 both the
-- sine and cosine are computed. To compute sin and cos, /alternating/
-- should be 1. If /alternating/ is 0, the hyperbolic sine is computed
-- (this is currently only intended to be used together with /sinonly/).
foreign import ccall "arb.h _arb_sin_cos_taylor_rs"
  _arb_sin_cos_taylor_rs :: Ptr CMp -> Ptr CMp -> Ptr CMpLimb -> Ptr CMp -> CMpSize -> CULong -> CInt -> CInt -> IO ()

-- | /_arb_get_mpn_fixed_mod_log2/ /w/ /q/ /error/ /x/ /wn/ 
-- 
-- Attempts to write \(w = x - q \log(2)\) with \(0 \le w < \log(2)\),
-- where /w/ is a fixed-point number with /wn/ limbs and ulp error /error/.
-- Returns success.
foreign import ccall "arb.h _arb_get_mpn_fixed_mod_log2"
  _arb_get_mpn_fixed_mod_log2 :: Ptr CMp -> Ptr CFmpz -> Ptr CMpLimb -> Ptr CArf -> CMpSize -> IO CInt

-- | /_arb_get_mpn_fixed_mod_pi4/ /w/ /q/ /octant/ /error/ /x/ /wn/ 
-- 
-- Attempts to write \(w = |x| - q \pi/4\) with \(0 \le w < \pi/4\), where
-- /w/ is a fixed-point number with /wn/ limbs and ulp error /error/.
-- Returns success.
-- 
-- The value of /q/ mod 8 is written to /octant/. The output variable /q/
-- can be NULL, in which case the full value of /q/ is not stored.
foreign import ccall "arb.h _arb_get_mpn_fixed_mod_pi4"
  _arb_get_mpn_fixed_mod_pi4 :: Ptr CMp -> Ptr CFmpz -> Ptr CInt -> Ptr CMpLimb -> Ptr CArf -> CMpSize -> IO CInt

-- | /_arb_exp_taylor_bound/ /mag/ /prec/ 
-- 
-- Returns /n/ such that
-- \(\left|\sum_{k=n}^{\infty} x^k / k!\right| \le 2^{-\mathrm{prec}}\),
-- assuming \(|x| \le 2^{\mathrm{mag}} \le 1/4\).
foreign import ccall "arb.h _arb_exp_taylor_bound"
  _arb_exp_taylor_bound :: CLong -> CLong -> IO CLong

-- | /arb_exp_arf_bb/ /z/ /x/ /prec/ /m1/ 
-- 
-- Computes the exponential function using the bit-burst algorithm. If /m1/
-- is nonzero, the exponential function minus one is computed accurately.
-- 
-- Aborts if /x/ is extremely small or large (where another algorithm
-- should be used).
-- 
-- For large /x/, repeated halving is used. In fact, we always do argument
-- reduction until \(|x|\) is smaller than about \(2^{-d}\) where
-- \(d \approx 16\) to speed up convergence. If \(|x| \approx 2^m\), we
-- thus need about \(m+d\) squarings.
-- 
-- Computing \(\log(2)\) costs roughly 100-200 multiplications, so is not
-- usually worth the effort at very high precision. However, this function
-- could be improved by using \(\log(2)\) based reduction at precision low
-- enough that the value can be assumed to be cached.
foreign import ccall "arb.h arb_exp_arf_bb"
  arb_exp_arf_bb :: Ptr CArb -> Ptr CArf -> CLong -> CInt -> IO ()

foreign import ccall "arb.h _arb_exp_sum_bs_simple"
  _arb_exp_sum_bs_simple :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFBitCnt -> Ptr CFmpz -> CFBitCnt -> CLong -> IO ()

-- | /_arb_exp_sum_bs_powtab/ /T/ /Q/ /Qexp/ /x/ /r/ /N/ 
-- 
-- Computes /T/, /Q/ and /Qexp/ such that
-- \(T / (Q 2^{\text{Qexp}}) = \sum_{k=1}^N (x/2^r)^k/k!\) using binary
-- splitting. Note that the sum is taken to /N/ inclusive and omits the
-- constant term.
-- 
-- The /powtab/ version precomputes a table of powers of /x/, resulting in
-- slightly higher memory usage but better speed. For best efficiency, /N/
-- should have many trailing zero bits.
foreign import ccall "arb.h _arb_exp_sum_bs_powtab"
  _arb_exp_sum_bs_powtab :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFBitCnt -> Ptr CFmpz -> CFBitCnt -> CLong -> IO ()

-- | /arb_exp_arf_rs_generic/ /res/ /x/ /prec/ /minus_one/ 
-- 
-- Computes the exponential function using a generic version of the
-- rectangular splitting strategy, intended for intermediate precision.
foreign import ccall "arb.h arb_exp_arf_rs_generic"
  arb_exp_arf_rs_generic :: Ptr CArb -> Ptr CArf -> CLong -> CInt -> IO ()

foreign import ccall "arb.h _arb_atan_sum_bs_simple"
  _arb_atan_sum_bs_simple :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFBitCnt -> Ptr CFmpz -> CFBitCnt -> CLong -> IO ()

-- | /_arb_atan_sum_bs_powtab/ /T/ /Q/ /Qexp/ /x/ /r/ /N/ 
-- 
-- Computes /T/, /Q/ and /Qexp/ such that
-- \(T / (Q 2^{\text{Qexp}}) = \sum_{k=1}^N (-1)^k (x/2^r)^{2k} / (2k+1)\)
-- using binary splitting. Note that the sum is taken to /N/ inclusive,
-- omits the linear term, and requires a final multiplication by
-- \((x/2^r)\) to give the true series for atan.
-- 
-- The /powtab/ version precomputes a table of powers of /x/, resulting in
-- slightly higher memory usage but better speed. For best efficiency, /N/
-- should have many trailing zero bits.
foreign import ccall "arb.h _arb_atan_sum_bs_powtab"
  _arb_atan_sum_bs_powtab :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFBitCnt -> Ptr CFmpz -> CFBitCnt -> CLong -> IO ()

-- | /arb_atan_arf_bb/ /z/ /x/ /prec/ 
-- 
-- Computes the arctangent of /x/. Initially, the argument-halving formula
-- 
-- \[`\]
-- \[\operatorname{atan}(x) = 2 \operatorname{atan}\left(\frac{x}{1+\sqrt{1+x^2}}\right)\]
-- 
-- is applied up to 8 times to get a small argument. Then a version of the
-- bit-burst algorithm is used. The functional equation
-- 
-- \[`\]
-- \[\operatorname{atan}(x) = \operatorname{atan}(p/q) +
--     \operatorname{atan}(w),
--     \quad w = \frac{qx-p}{px+q},
--     \quad p = \lfloor qx \rfloor\]
-- 
-- is applied repeatedly instead of integrating a differential equation for
-- the arctangent, as this appears to be more efficient.
foreign import ccall "arb.h arb_atan_arf_bb"
  arb_atan_arf_bb :: Ptr CArb -> Ptr CArf -> CLong -> IO ()

-- | /arb_atan_frac_bsplit/ /s/ /p/ /q/ /hyperbolic/ /prec/ 
-- 
-- Computes the arctangent of \(p/q\), optionally the hyperbolic
-- arctangent, using direct series summation with binary splitting.
foreign import ccall "arb.h arb_atan_frac_bsplit"
  arb_atan_frac_bsplit :: Ptr CArb -> Ptr CFmpz -> Ptr CFmpz -> CInt -> CLong -> IO ()

-- | /arb_sin_cos_arf_generic/ /s/ /c/ /x/ /prec/ 
-- 
-- Computes the sine and cosine of /x/ using a generic strategy. This
-- function gets called internally by the main sin and cos functions when
-- the precision for argument reduction or series evaluation based on
-- lookup tables is exhausted.
-- 
-- This function first performs a cheap test to see if
-- \(|x| < \pi / 2 - \varepsilon\). If the test fails, it uses \(\pi\) to
-- reduce the argument to the first octant, and then evaluates the sin and
-- cos functions recursively (this call cannot result in infinite
-- recursion).
-- 
-- If no argument reduction is needed, this function uses a generic version
-- of the rectangular splitting algorithm if the precision is not too high,
-- and otherwise invokes the asymptotically fast bit-burst algorithm.
foreign import ccall "arb.h arb_sin_cos_arf_generic"
  arb_sin_cos_arf_generic :: Ptr CArb -> Ptr CArb -> Ptr CArf -> CLong -> IO ()

-- | /arb_sin_cos_arf_bb/ /s/ /c/ /x/ /prec/ 
-- 
-- Computes the sine and cosine of /x/ using the bit-burst algorithm. It is
-- required that \(|x| < \pi / 2\) (this is not checked).
foreign import ccall "arb.h arb_sin_cos_arf_bb"
  arb_sin_cos_arf_bb :: Ptr CArb -> Ptr CArb -> Ptr CArf -> CLong -> IO ()

-- | /arb_sin_cos_wide/ /s/ /c/ /x/ /prec/ 
-- 
-- Computes an accurate enclosure (with both endpoints optimal to within
-- about \(2^{-30}\) as afforded by the radius format) of the range of sine
-- and cosine on a given wide interval. The computation is done by
-- evaluating the sine and cosine at the interval endpoints and determining
-- whether peaks of -1 or 1 occur between the endpoints. The interval is
-- then converted back to a ball.
-- 
-- The internal computations are done with doubles, using a simple
-- floating-point algorithm to approximate the sine and cosine. It is easy
-- to see that the cumulative errors in this algorithm add up to less than
-- \(2^{-30}\), with the dominant source of error being a single
-- approximate reduction by \(\pi/2\). This reduction is done safely using
-- doubles up to a magnitude of about \(2^{20}\). For larger arguments, a
-- slower reduction using @arb_t@ arithmetic is done as a preprocessing
-- step.
foreign import ccall "arb.h arb_sin_cos_wide"
  arb_sin_cos_wide :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_sin_cos_generic/ /s/ /c/ /x/ /prec/ 
-- 
-- Computes the sine and cosine of /x/ by taking care of various special
-- cases and computing the propagated error before calling
-- @arb_sin_cos_arf_generic@. This is used as a fallback inside
-- @arb_sin_cos@ to take care of all cases without a fast path in that
-- function.
foreign import ccall "arb.h arb_sin_cos_generic"
  arb_sin_cos_generic :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_log_primes_vec_bsplit/ /res/ /n/ /prec/ 
-- 
-- Sets /res/ to a vector containing the natural logarithms of the first
-- /n/ prime numbers, computed using binary splitting applied to
-- simultaneous Machine-type formulas. This function is not optimized for
-- large /n/ or small /prec/.
foreign import ccall "arb.h arb_log_primes_vec_bsplit"
  arb_log_primes_vec_bsplit :: Ptr CArb -> CLong -> CLong -> IO ()







-- | /_arb_log_p_ensure_cached/ /prec/ 
-- 
-- Ensure that the internal cache of logarithms of small prime numbers has
-- entries to at least /prec/ bits.
foreign import ccall "arb.h _arb_log_p_ensure_cached"
  _arb_log_p_ensure_cached :: CLong -> IO ()

-- | /arb_exp_arf_log_reduction/ /res/ /x/ /prec/ /minus_one/ 
-- 
-- Computes the exponential function using log reduction.
foreign import ccall "arb.h arb_exp_arf_log_reduction"
  arb_exp_arf_log_reduction :: Ptr CArb -> Ptr CArf -> CLong -> CInt -> IO ()

-- | /arb_exp_arf_generic/ /z/ /x/ /prec/ /minus_one/ 
-- 
-- Computes the exponential function using an automatic choice between
-- rectangular splitting and the bit-burst algorithm, without
-- precomputation.
foreign import ccall "arb.h arb_exp_arf_generic"
  arb_exp_arf_generic :: Ptr CArb -> Ptr CArf -> CLong -> CInt -> IO ()

-- | /arb_exp_arf/ /z/ /x/ /prec/ /minus_one/ /maglim/ 
-- 
-- Computes the exponential function using an automatic choice between all
-- implemented algorithms.
foreign import ccall "arb.h arb_exp_arf"
  arb_exp_arf :: Ptr CArb -> Ptr CArf -> CLong -> CInt -> CLong -> IO ()

-- | /arb_log_newton/ /res/ /x/ /prec/ 
-- 
-- Computes the logarithm using Newton iteration.
foreign import ccall "arb.h arb_log_newton"
  arb_log_newton :: Ptr CArb -> Ptr CArb -> CLong -> IO ()




-- | /arb_atan_gauss_primes_vec_bsplit/ /res/ /n/ /prec/ 
-- 
-- Sets /res/ to the primitive angles corresponding to the first /n/
-- nonreal Gaussian primes (ignoring symmetries), computed using binary
-- splitting applied to simultaneous Machine-type formulas. This function
-- is not optimized for large /n/ or small /prec/.
foreign import ccall "arb.h arb_atan_gauss_primes_vec_bsplit"
  arb_atan_gauss_primes_vec_bsplit :: Ptr CArb -> CLong -> CLong -> IO ()

foreign import ccall "arb.h _arb_atan_gauss_p_ensure_cached"
  _arb_atan_gauss_p_ensure_cached :: CLong -> IO ()

-- | /arb_sin_cos_arf_atan_reduction/ /res1/ /res2/ /x/ /prec/ 
-- 
-- Computes sin and\/or cos using reduction by primitive angles.
foreign import ccall "arb.h arb_sin_cos_arf_atan_reduction"
  arb_sin_cos_arf_atan_reduction :: Ptr CArb -> Ptr CArb -> Ptr CArf -> CLong -> IO ()

-- | /arb_atan_newton/ /res/ /x/ /prec/ 
-- 
-- Computes the arctangent using Newton iteration.
foreign import ccall "arb.h arb_atan_newton"
  arb_atan_newton :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- Vector functions ------------------------------------------------------------

-- | /_arb_vec_zero/ /vec/ /n/ 
-- 
-- Sets all entries in /vec/ to zero.
foreign import ccall "arb.h _arb_vec_zero"
  _arb_vec_zero :: Ptr CArb -> CLong -> IO ()

-- | /_arb_vec_is_zero/ /vec/ /len/ 
-- 
-- Returns nonzero iff all entries in /x/ are zero.
foreign import ccall "arb.h _arb_vec_is_zero"
  _arb_vec_is_zero :: Ptr CArb -> CLong -> IO CInt

-- | /_arb_vec_is_finite/ /x/ /len/ 
-- 
-- Returns nonzero iff all entries in /x/ certainly are finite.
foreign import ccall "arb.h _arb_vec_is_finite"
  _arb_vec_is_finite :: Ptr CArb -> CLong -> IO CInt

-- | /_arb_vec_set/ /res/ /vec/ /len/ 
-- 
-- Sets /res/ to a copy of /vec/.
foreign import ccall "arb.h _arb_vec_set"
  _arb_vec_set :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /_arb_vec_set_round/ /res/ /vec/ /len/ /prec/ 
-- 
-- Sets /res/ to a copy of /vec/, rounding each entry to /prec/ bits.
foreign import ccall "arb.h _arb_vec_set_round"
  _arb_vec_set_round :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /_arb_vec_swap/ /vec1/ /vec2/ /len/ 
-- 
-- Swaps the entries of /vec1/ and /vec2/.
foreign import ccall "arb.h _arb_vec_swap"
  _arb_vec_swap :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

foreign import ccall "arb.h _arb_vec_neg"
  _arb_vec_neg :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

foreign import ccall "arb.h _arb_vec_sub"
  _arb_vec_sub :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> CLong -> IO ()

foreign import ccall "arb.h _arb_vec_add"
  _arb_vec_add :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> CLong -> IO ()

foreign import ccall "arb.h _arb_vec_scalar_mul"
  _arb_vec_scalar_mul :: Ptr CArb -> Ptr CArb -> CLong -> Ptr CArb -> CLong -> IO ()

foreign import ccall "arb.h _arb_vec_scalar_div"
  _arb_vec_scalar_div :: Ptr CArb -> Ptr CArb -> CLong -> Ptr CArb -> CLong -> IO ()

foreign import ccall "arb.h _arb_vec_scalar_mul_fmpz"
  _arb_vec_scalar_mul_fmpz :: Ptr CArb -> Ptr CArb -> CLong -> Ptr CFmpz -> CLong -> IO ()

foreign import ccall "arb.h _arb_vec_scalar_mul_2exp_si"
  _arb_vec_scalar_mul_2exp_si :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /_arb_vec_scalar_addmul/ /res/ /vec/ /len/ /c/ /prec/ 
-- 
-- Performs the respective scalar operation elementwise.
foreign import ccall "arb.h _arb_vec_scalar_addmul"
  _arb_vec_scalar_addmul :: Ptr CArb -> Ptr CArb -> CLong -> Ptr CArb -> CLong -> IO ()

-- | /_arb_vec_get_mag/ /bound/ /vec/ /len/ /prec/ 
-- 
-- Sets /bound/ to an upper bound for the entries in /vec/.
foreign import ccall "arb.h _arb_vec_get_mag"
  _arb_vec_get_mag :: Ptr CMag -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /_arb_vec_bits/ /x/ /len/ 
-- 
-- Returns the maximum of @arb_bits@ for all entries in /vec/.
foreign import ccall "arb.h _arb_vec_bits"
  _arb_vec_bits :: Ptr CArb -> CLong -> IO CLong

-- | /_arb_vec_set_powers/ /xs/ /x/ /len/ /prec/ 
-- 
-- Sets /xs/ to the powers \(1, x, x^2, \ldots, x^{len-1}\).
foreign import ccall "arb.h _arb_vec_set_powers"
  _arb_vec_set_powers :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> IO ()

foreign import ccall "arb.h _arb_vec_add_error_arf_vec"
  _arb_vec_add_error_arf_vec :: Ptr CArb -> Ptr CArf -> CLong -> IO ()

-- | /_arb_vec_add_error_mag_vec/ /res/ /err/ /len/ 
-- 
-- Adds the magnitude of each entry in /err/ to the radius of the
-- corresponding entry in /res/.
foreign import ccall "arb.h _arb_vec_add_error_mag_vec"
  _arb_vec_add_error_mag_vec :: Ptr CArb -> Ptr CMag -> CLong -> IO ()

-- | /_arb_vec_indeterminate/ /vec/ /len/ 
-- 
-- Applies @arb_indeterminate@ elementwise.
foreign import ccall "arb.h _arb_vec_indeterminate"
  _arb_vec_indeterminate :: Ptr CArb -> CLong -> IO ()

-- | /_arb_vec_trim/ /res/ /vec/ /len/ 
-- 
-- Applies @arb_trim@ elementwise.
foreign import ccall "arb.h _arb_vec_trim"
  _arb_vec_trim :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /_arb_vec_get_unique_fmpz_vec/ /res/ /vec/ /len/ 
-- 
-- Calls @arb_get_unique_fmpz@ elementwise and returns nonzero if all
-- entries can be rounded uniquely to integers. If any entry in /vec/
-- cannot be rounded uniquely to an integer, returns zero.
foreign import ccall "arb.h _arb_vec_get_unique_fmpz_vec"
  _arb_vec_get_unique_fmpz_vec :: Ptr CFmpz -> Ptr CArb -> CLong -> IO CInt

