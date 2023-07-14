module Data.Number.Flint.Acb.Poly.FFI (
  -- * Polynomials over the complex numbers
  -- * Types
    AcbPoly (..)
  , CAcbPoly (..)
  , newAcbPoly
  , withAcbPoly
  , withNewAcbPoly
  -- * Memory management
  , acb_poly_init
  , acb_poly_clear
  , acb_poly_fit_length
  , _acb_poly_set_length
  , _acb_poly_normalise
  , acb_poly_swap
  , acb_poly_allocated_bytes
  -- * Basic properties and manipulation
  , acb_poly_length
  , acb_poly_degree
  , acb_poly_is_zero
  , acb_poly_is_one
  , acb_poly_is_x
  , acb_poly_zero
  , acb_poly_one
  , acb_poly_set
  , acb_poly_set_round
  , acb_poly_set_trunc
  , acb_poly_set_trunc_round
  , acb_poly_set_coeff_si
  , acb_poly_set_coeff_acb
  , acb_poly_get_coeff_acb
  , _acb_poly_shift_right
  , acb_poly_shift_right
  , _acb_poly_shift_left
  , acb_poly_shift_left
  , acb_poly_truncate
  , acb_poly_valuation
  -- * Input and output
  , acb_poly_printd
  , acb_poly_fprintd
  -- * Random generation
  , acb_poly_randtest
  -- * Comparisons
  , acb_poly_equal
  , acb_poly_contains
  , acb_poly_contains_fmpz_poly
  , acb_poly_contains_fmpq_poly
  , _acb_poly_overlaps
  , acb_poly_overlaps
  , acb_poly_get_unique_fmpz_poly
  , acb_poly_is_real
  -- * Conversions
  , acb_poly_set_fmpz_poly
  , acb_poly_set2_fmpz_poly
  , acb_poly_set_arb_poly
  , acb_poly_set2_arb_poly
  , acb_poly_set_fmpq_poly
  , acb_poly_set2_fmpq_poly
  , acb_poly_set_acb
  , acb_poly_set_si
  -- * Bounds
  , _acb_poly_majorant
  , acb_poly_majorant
  -- * Arithmetic
  , _acb_poly_add
  , acb_poly_add
  , acb_poly_add_si
  , _acb_poly_sub
  , acb_poly_sub
  , acb_poly_add_series
  , acb_poly_sub_series
  , acb_poly_neg
  , acb_poly_scalar_mul_2exp_si
  , acb_poly_scalar_mul
  , acb_poly_scalar_div
  , _acb_poly_mullow_classical
  , _acb_poly_mullow_transpose
  , _acb_poly_mullow_transpose_gauss
  , _acb_poly_mullow
  , acb_poly_mullow_classical
  , acb_poly_mullow_transpose
  , acb_poly_mullow_transpose_gauss
  , acb_poly_mullow
  , _acb_poly_mul
  , acb_poly_mul
  , _acb_poly_inv_series
  , acb_poly_inv_series
  , _acb_poly_div_series
  , acb_poly_div_series
  , _acb_poly_div
  , _acb_poly_rem
  , _acb_poly_divrem
  , acb_poly_divrem
  , _acb_poly_div_root
  -- * Composition
  , _acb_poly_taylor_shift
  , _acb_poly_compose
  , _acb_poly_compose_series
  , _acb_poly_revert_series_lagrange
  , acb_poly_revert_series_lagrange
  , _acb_poly_revert_series_newton
  , acb_poly_revert_series_newton
  , _acb_poly_revert_series_lagrange_fast
  , acb_poly_revert_series_lagrange_fast
  , _acb_poly_revert_series
  , acb_poly_revert_series
  -- * Evaluation
  , _acb_poly_evaluate_horner
  , acb_poly_evaluate_horner
  , _acb_poly_evaluate_rectangular
  , acb_poly_evaluate_rectangular
  , _acb_poly_evaluate
  , acb_poly_evaluate
  , _acb_poly_evaluate2_horner
  , acb_poly_evaluate2_horner
  , _acb_poly_evaluate2_rectangular
  , acb_poly_evaluate2_rectangular
  , _acb_poly_evaluate2
  , acb_poly_evaluate2
  -- * Product trees
  , _acb_poly_product_roots
  , acb_poly_product_roots
  , _acb_poly_tree_alloc
  , _acb_poly_tree_free
  , _acb_poly_tree_build
  -- * Multipoint evaluation
  , _acb_poly_evaluate_vec_iter
  , acb_poly_evaluate_vec_iter
  , _acb_poly_evaluate_vec_fast_precomp
  , _acb_poly_evaluate_vec_fast
  , acb_poly_evaluate_vec_fast
  -- * Interpolation
  , _acb_poly_interpolate_newton
  , acb_poly_interpolate_newton
  , _acb_poly_interpolate_barycentric
  , acb_poly_interpolate_barycentric
  , _acb_poly_interpolation_weights
  , _acb_poly_interpolate_fast_precomp
  , _acb_poly_interpolate_fast
  , acb_poly_interpolate_fast
  -- * Differentiation
  , _acb_poly_derivative
  , acb_poly_derivative
  , _acb_poly_nth_derivative
  , acb_poly_nth_derivative
  , _acb_poly_integral
  , acb_poly_integral
  -- * Transforms
  , _acb_poly_borel_transform
  , acb_poly_borel_transform
  , _acb_poly_inv_borel_transform
  , acb_poly_inv_borel_transform
  , _acb_poly_binomial_transform_basecase
  , acb_poly_binomial_transform_basecase
  , _acb_poly_binomial_transform_convolution
  , acb_poly_binomial_transform_convolution
  , _acb_poly_binomial_transform
  , acb_poly_binomial_transform
  , _acb_poly_graeffe_transform
  , acb_poly_graeffe_transform
  -- * Elementary functions
  , _acb_poly_pow_ui_trunc_binexp
  , acb_poly_pow_ui_trunc_binexp
  , _acb_poly_pow_ui
  , acb_poly_pow_ui
  , _acb_poly_pow_series
  , acb_poly_pow_series
  , _acb_poly_pow_acb_series
  , acb_poly_pow_acb_series
  , _acb_poly_sqrt_series
  , acb_poly_sqrt_series
  , _acb_poly_rsqrt_series
  , acb_poly_rsqrt_series
  , _acb_poly_log_series
  , acb_poly_log_series
  , _acb_poly_log1p_series
  , acb_poly_log1p_series
  , _acb_poly_atan_series
  , acb_poly_atan_series
  , _acb_poly_exp_series_basecase
  , acb_poly_exp_series_basecase
  , _acb_poly_exp_series
  , acb_poly_exp_series
  , _acb_poly_exp_pi_i_series
  , acb_poly_exp_pi_i_series
  , _acb_poly_sin_cos_series
  , _acb_poly_sin_series
  , acb_poly_sin_series
  , _acb_poly_cos_series
  , acb_poly_cos_series
  , _acb_poly_tan_series
  , acb_poly_tan_series
  , _acb_poly_sin_cos_pi_series
  , acb_poly_sin_cos_pi_series
  , _acb_poly_sin_pi_series
  , acb_poly_sin_pi_series
  , _acb_poly_cos_pi_series
  , acb_poly_cos_pi_series
  , _acb_poly_cot_pi_series
  , acb_poly_cot_pi_series
  , _acb_poly_sinh_cosh_series_basecase
  , acb_poly_sinh_cosh_series_basecase
  , _acb_poly_sinh_cosh_series_exponential
  , acb_poly_sinh_cosh_series_exponential
  , _acb_poly_sinh_cosh_series
  , acb_poly_sinh_cosh_series
  , _acb_poly_sinh_series
  , acb_poly_sinh_series
  , _acb_poly_cosh_series
  , acb_poly_cosh_series
  , _acb_poly_sinc_series
  , acb_poly_sinc_series
  -- * Lambert W function
  , _acb_poly_lambertw_series
  , acb_poly_lambertw_series
  -- * Gamma function
  , _acb_poly_gamma_series
  , acb_poly_gamma_series
  , _acb_poly_rgamma_series
  , acb_poly_rgamma_series
  , _acb_poly_lgamma_series
  , acb_poly_lgamma_series
  , _acb_poly_digamma_series
  , acb_poly_digamma_series
  , _acb_poly_rising_ui_series
  , acb_poly_rising_ui_series
  -- * Power sums
  , _acb_poly_powsum_series_naive
  , _acb_poly_powsum_series_naive_threaded
  , _acb_poly_powsum_one_series_sieved
  -- * Zeta function
  , _acb_poly_zeta_em_choose_param
  , _acb_poly_zeta_em_bound1
  , _acb_poly_zeta_em_bound
  , _acb_poly_zeta_em_tail_naive
  , _acb_poly_zeta_em_tail_bsplit
  , _acb_poly_zeta_em_sum
  , _acb_poly_zeta_cpx_series
  , _acb_poly_zeta_series
  , acb_poly_zeta_series
  -- * Other special functions
  , _acb_poly_polylog_cpx_small
  , _acb_poly_polylog_cpx_zeta
  , _acb_poly_polylog_cpx
  , _acb_poly_polylog_series
  , acb_poly_polylog_series
  , _acb_poly_erf_series
  , acb_poly_erf_series
  , _acb_poly_agm1_series
  , acb_poly_agm1_series
  , _acb_poly_elliptic_k_series
  , acb_poly_elliptic_k_series
  , _acb_poly_elliptic_p_series
  , acb_poly_elliptic_p_series
  -- * Root-finding
  , _acb_poly_root_bound_fujiwara
  , acb_poly_root_bound_fujiwara
  , _acb_poly_root_inclusion
  , _acb_poly_validate_roots
  , _acb_poly_refine_roots_durand_kerner
  , _acb_poly_find_roots
  , acb_poly_find_roots
  , _acb_poly_validate_real_roots
  , acb_poly_validate_real_roots
) where

-- Polynomials over the complex numbers ----------------------------------------

-- An @AcPoly@ represents a polynomial over the complex numbers,
-- implemented as an array of coefficients of type @acb_struct@.
--
-- Most functions are provided in two versions: an underscore method which
-- operates directly on pre-allocated arrays of coefficients and generally
-- has some restrictions (such as requiring the lengths to be nonzero and
-- not supporting aliasing of the input and output arrays), and a
-- non-underscore method which performs automatic memory management and
-- handles degenerate cases.
--

#include <flint/arb.h>
#include <flint/acb_poly.h>

import System.IO.Unsafe ( unsafePerformIO )

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr )
import Foreign.Marshal ( free )

import Foreign.Storable

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Poly
import Data.Number.Flint.Fmpq.Poly

import Data.Number.Flint.Arb
import Data.Number.Flint.Arb.Types

import Data.Number.Flint.Acb
import Data.Number.Flint.Acb.Types

-- Types -----------------------------------------------------------------------

data AcbPoly = AcbPoly {-# UNPACK #-} !(ForeignPtr CAcbPoly)
type CAcbPoly = CFlint AcbPoly

-- | Createst a new `CAcbPoly` structure encapsulated in `AcbPoly`.
{-# INLINE newAcbPoly #-}
newAcbPoly = do
  p <- mallocForeignPtr
  withForeignPtr p acb_poly_init
  addForeignPtrFinalizer p_acb_poly_clear p
  return $ AcbPoly p

-- | Use `AcbPoly` in f.
{-# INLINE withAcbPoly #-}
withAcbPoly (AcbPoly p) f = do
  withForeignPtr p $ \fp -> f fp >>= return . (AcbPoly p,)

-- | Use new `AcbPoly` ptr in f.
{-# INLINE withNewAcbPoly #-}
withNewAcbPoly f = do
  p <- newAcbPoly
  withAcbPoly p f
  
instance Storable CAcbPoly where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size acb_poly_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment acb_poly_t}
  peek = error "CAcbPoly.peek: Not defined"
  poke = error "CAcbPoly.poke: Not defined"

-- Memory management -----------------------------------------------------------

-- | /acb_poly_init/ /poly/ 
-- 
-- Initializes the polynomial for use, setting it to the zero polynomial.
foreign import ccall "acb_poly.h acb_poly_init"
  acb_poly_init :: Ptr CAcbPoly -> IO ()

-- | /acb_poly_clear/ /poly/ 
-- 
-- Clears the polynomial, deallocating all coefficients and the coefficient
-- array.
foreign import ccall "acb_poly.h acb_poly_clear"
  acb_poly_clear :: Ptr CAcbPoly -> IO ()

foreign import ccall "acb_poly.h &acb_poly_clear"
  p_acb_poly_clear :: FunPtr (Ptr CAcbPoly -> IO ())

-- | /acb_poly_fit_length/ /poly/ /len/ 
-- 
-- Makes sure that the coefficient array of the polynomial contains at
-- least /len/ initialized coefficients.
foreign import ccall "acb_poly.h acb_poly_fit_length"
  acb_poly_fit_length :: Ptr CAcbPoly -> CLong -> IO ()

-- | /_acb_poly_set_length/ /poly/ /len/ 
-- 
-- Directly changes the length of the polynomial, without allocating or
-- deallocating coefficients. The value should not exceed the allocation
-- length.
foreign import ccall "acb_poly.h _acb_poly_set_length"
  _acb_poly_set_length :: Ptr CAcbPoly -> CLong -> IO ()

-- | /_acb_poly_normalise/ /poly/ 
-- 
-- Strips any trailing coefficients which are identical to zero.
foreign import ccall "acb_poly.h _acb_poly_normalise"
  _acb_poly_normalise :: Ptr CAcbPoly -> IO ()

-- | /acb_poly_swap/ /poly1/ /poly2/ 
-- 
-- Swaps /poly1/ and /poly2/ efficiently.
foreign import ccall "acb_poly.h acb_poly_swap"
  acb_poly_swap :: Ptr CAcbPoly -> Ptr CAcbPoly -> IO ()

-- | /acb_poly_allocated_bytes/ /x/ 
-- 
-- Returns the total number of bytes heap-allocated internally by this
-- object. The count excludes the size of the structure itself. Add
-- @sizeof(acb_poly_struct)@ to get the size of the object as a whole.
foreign import ccall "acb_poly.h acb_poly_allocated_bytes"
  acb_poly_allocated_bytes :: Ptr CAcbPoly -> IO CLong

-- Basic properties and manipulation -------------------------------------------

-- | /acb_poly_length/ /poly/ 
-- 
-- Returns the length of /poly/, i.e. zero if /poly/ is identically zero,
-- and otherwise one more than the index of the highest term that is not
-- identically zero.
foreign import ccall "acb_poly.h acb_poly_length"
  acb_poly_length :: Ptr CAcbPoly -> IO CLong

-- | /acb_poly_degree/ /poly/ 
-- 
-- Returns the degree of /poly/, defined as one less than its length. Note
-- that if one or several leading coefficients are balls containing zero,
-- this value can be larger than the true degree of the exact polynomial
-- represented by /poly/, so the return value of this function is
-- effectively an upper bound.
foreign import ccall "acb_poly.h acb_poly_degree"
  acb_poly_degree :: Ptr CAcbPoly -> IO CLong

foreign import ccall "acb_poly.h acb_poly_is_zero"
  acb_poly_is_zero :: Ptr CAcbPoly -> IO CInt

foreign import ccall "acb_poly.h acb_poly_is_one"
  acb_poly_is_one :: Ptr CAcbPoly -> IO CInt

-- | /acb_poly_is_x/ /poly/ 
-- 
-- Returns 1 if /poly/ is exactly the polynomial 0, 1 or /x/ respectively.
-- Returns 0 otherwise.
foreign import ccall "acb_poly.h acb_poly_is_x"
  acb_poly_is_x :: Ptr CAcbPoly -> IO CInt

-- | /acb_poly_zero/ /poly/ 
-- 
-- Sets /poly/ to the zero polynomial.
foreign import ccall "acb_poly.h acb_poly_zero"
  acb_poly_zero :: Ptr CAcbPoly -> IO ()

-- | /acb_poly_one/ /poly/ 
-- 
-- Sets /poly/ to the constant polynomial 1.
foreign import ccall "acb_poly.h acb_poly_one"
  acb_poly_one :: Ptr CAcbPoly -> IO ()

-- | /acb_poly_set/ /dest/ /src/ 
-- 
-- Sets /dest/ to a copy of /src/.
foreign import ccall "acb_poly.h acb_poly_set"
  acb_poly_set :: Ptr CAcbPoly -> Ptr CAcbPoly -> IO ()

-- | /acb_poly_set_round/ /dest/ /src/ /prec/ 
-- 
-- Sets /dest/ to a copy of /src/, rounded to /prec/ bits.
foreign import ccall "acb_poly.h acb_poly_set_round"
  acb_poly_set_round :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> IO ()

foreign import ccall "acb_poly.h acb_poly_set_trunc"
  acb_poly_set_trunc :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> IO ()

-- | /acb_poly_set_trunc_round/ /dest/ /src/ /n/ /prec/ 
-- 
-- Sets /dest/ to a copy of /src/, truncated to length /n/ and rounded to
-- /prec/ bits.
foreign import ccall "acb_poly.h acb_poly_set_trunc_round"
  acb_poly_set_trunc_round :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h acb_poly_set_coeff_si"
  acb_poly_set_coeff_si :: Ptr CAcbPoly -> CLong -> CLong -> IO ()

-- | /acb_poly_set_coeff_acb/ /poly/ /n/ /c/ 
-- 
-- Sets the coefficient with index /n/ in /poly/ to the value /c/. We
-- require that /n/ is nonnegative.
foreign import ccall "acb_poly.h acb_poly_set_coeff_acb"
  acb_poly_set_coeff_acb :: Ptr CAcbPoly -> CLong -> Ptr CAcb -> IO ()

-- | /acb_poly_get_coeff_acb/ /v/ /poly/ /n/ 
-- 
-- Sets /v/ to the value of the coefficient with index /n/ in /poly/. We
-- require that /n/ is nonnegative.
foreign import ccall "acb_poly.h acb_poly_get_coeff_acb"
  acb_poly_get_coeff_acb :: Ptr CAcb -> Ptr CAcbPoly -> CLong -> IO ()




foreign import ccall "acb_poly.h _acb_poly_shift_right"
  _acb_poly_shift_right :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /acb_poly_shift_right/ /res/ /poly/ /n/ 
-- 
-- Sets /res/ to /poly/ divided by \(x^n\), throwing away the lower
-- coefficients. We require that /n/ is nonnegative.
foreign import ccall "acb_poly.h acb_poly_shift_right"
  acb_poly_shift_right :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_shift_left"
  _acb_poly_shift_left :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /acb_poly_shift_left/ /res/ /poly/ /n/ 
-- 
-- Sets /res/ to /poly/ multiplied by \(x^n\). We require that /n/ is
-- nonnegative.
foreign import ccall "acb_poly.h acb_poly_shift_left"
  acb_poly_shift_left :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> IO ()

-- | /acb_poly_truncate/ /poly/ /n/ 
-- 
-- Truncates /poly/ to have length at most /n/, i.e. degree strictly
-- smaller than /n/. We require that /n/ is nonnegative.
foreign import ccall "acb_poly.h acb_poly_truncate"
  acb_poly_truncate :: Ptr CAcbPoly -> CLong -> IO ()

-- | /acb_poly_valuation/ /poly/ 
-- 
-- Returns the degree of the lowest term that is not exactly zero in
-- /poly/. Returns -1 if /poly/ is the zero polynomial.
foreign import ccall "acb_poly.h acb_poly_valuation"
  acb_poly_valuation :: Ptr CAcbPoly -> IO CLong

-- Input and output ------------------------------------------------------------

foreign import ccall "acb_poly.h acb_poly_get_strd"
  acb_poly_get_strd :: Ptr CAcbPoly -> CLong -> IO CString

-- | /acb_poly_printd/ /poly/ /digits/ 
-- 
-- Prints the polynomial as an array of coefficients, printing each
-- coefficient using /acb_printd/.
acb_poly_printd :: Ptr CAcbPoly -> CLong -> IO ()
acb_poly_printd poly digits = do
  cs <- acb_poly_get_strd poly digits
  s <- peekCString cs
  free cs
  putStr s

-- | /acb_poly_fprintd/ /file/ /poly/ /digits/ 
-- 
-- Prints the polynomial as an array of coefficients to the stream /file/,
-- printing each coefficient using /acb_fprintd/.
foreign import ccall "acb_poly.h acb_poly_fprintd"
  acb_poly_fprintd :: Ptr CFile -> Ptr CAcbPoly -> CLong -> IO ()

-- Random generation -----------------------------------------------------------

-- | /acb_poly_randtest/ /poly/ /state/ /len/ /prec/ /mag_bits/ 
-- 
-- Creates a random polynomial with length at most /len/.
foreign import ccall "acb_poly.h acb_poly_randtest"
  acb_poly_randtest :: Ptr CAcbPoly -> Ptr CFRandState -> CLong -> CLong -> CLong -> IO ()

-- Comparisons -----------------------------------------------------------------

-- | /acb_poly_equal/ /A/ /B/ 
-- 
-- Returns nonzero iff /A/ and /B/ are identical as interval polynomials.
foreign import ccall "acb_poly.h acb_poly_equal"
  acb_poly_equal :: Ptr CAcbPoly -> Ptr CAcbPoly -> IO CInt

foreign import ccall "acb_poly.h acb_poly_contains"
  acb_poly_contains :: Ptr CAcbPoly -> Ptr CAcbPoly -> IO CInt

foreign import ccall "acb_poly.h acb_poly_contains_fmpz_poly"
  acb_poly_contains_fmpz_poly :: Ptr CAcbPoly -> Ptr CFmpzPoly -> IO CInt

-- | /acb_poly_contains_fmpq_poly/ /poly1/ /poly2/ 
-- 
-- Returns nonzero iff /poly2/ is contained in /poly1/.
foreign import ccall "acb_poly.h acb_poly_contains_fmpq_poly"
  acb_poly_contains_fmpq_poly :: Ptr CAcbPoly -> Ptr CFmpqPoly -> IO CInt

foreign import ccall "acb_poly.h _acb_poly_overlaps"
  _acb_poly_overlaps :: Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> IO CInt

-- | /acb_poly_overlaps/ /poly1/ /poly2/ 
-- 
-- Returns nonzero iff /poly1/ overlaps with /poly2/. The underscore
-- function requires that /len1/ ist at least as large as /len2/.
foreign import ccall "acb_poly.h acb_poly_overlaps"
  acb_poly_overlaps :: Ptr CAcbPoly -> Ptr CAcbPoly -> IO CInt

-- | /acb_poly_get_unique_fmpz_poly/ /z/ /x/ 
-- 
-- If /x/ contains a unique integer polynomial, sets /z/ to that value and
-- returns nonzero. Otherwise (if /x/ represents no integers or more than
-- one integer), returns zero, possibly partially modifying /z/.
foreign import ccall "acb_poly.h acb_poly_get_unique_fmpz_poly"
  acb_poly_get_unique_fmpz_poly :: Ptr CFmpzPoly -> Ptr CAcbPoly -> IO CInt

-- | /acb_poly_is_real/ /poly/ 
-- 
-- Returns nonzero iff all coefficients in /poly/ have zero imaginary part.
foreign import ccall "acb_poly.h acb_poly_is_real"
  acb_poly_is_real :: Ptr CAcbPoly -> IO CInt

-- Conversions -----------------------------------------------------------------

foreign import ccall "acb_poly.h acb_poly_set_fmpz_poly"
  acb_poly_set_fmpz_poly :: Ptr CAcbPoly -> Ptr CFmpzPoly -> CLong -> IO ()

foreign import ccall "acb_poly.h acb_poly_set2_fmpz_poly"
  acb_poly_set2_fmpz_poly :: Ptr CAcbPoly -> Ptr CFmpzPoly -> Ptr CFmpzPoly -> CLong -> IO ()

foreign import ccall "acb_poly.h acb_poly_set_arb_poly"
  acb_poly_set_arb_poly :: Ptr CAcbPoly -> Ptr CArbPoly -> IO ()

foreign import ccall "acb_poly.h acb_poly_set2_arb_poly"
  acb_poly_set2_arb_poly :: Ptr CAcbPoly -> Ptr CArbPoly -> Ptr CArbPoly -> IO ()

foreign import ccall "acb_poly.h acb_poly_set_fmpq_poly"
  acb_poly_set_fmpq_poly :: Ptr CAcbPoly -> Ptr CFmpqPoly -> CLong -> IO ()

-- | /acb_poly_set2_fmpq_poly/ /poly/ /re/ /im/ /prec/ 
-- 
-- Sets /poly/ to the given real part /re/ plus the imaginary part /im/,
-- both rounded to /prec/ bits.
foreign import ccall "acb_poly.h acb_poly_set2_fmpq_poly"
  acb_poly_set2_fmpq_poly :: Ptr CAcbPoly -> Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> IO ()

foreign import ccall "acb_poly.h acb_poly_set_acb"
  acb_poly_set_acb :: Ptr CAcbPoly -> Ptr CAcb -> IO ()

-- | /acb_poly_set_si/ /poly/ /src/ 
-- 
-- Sets /poly/ to /src/.
foreign import ccall "acb_poly.h acb_poly_set_si"
  acb_poly_set_si :: Ptr CAcbPoly -> CLong -> IO ()

-- Bounds ----------------------------------------------------------------------

foreign import ccall "acb_poly.h _acb_poly_majorant"
  _acb_poly_majorant :: Ptr CArb -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /acb_poly_majorant/ /res/ /poly/ /prec/ 
-- 
-- Sets /res/ to an exact real polynomial whose coefficients are upper
-- bounds for the absolute values of the coefficients in /poly/, rounded to
-- /prec/ bits.
foreign import ccall "acb_poly.h acb_poly_majorant"
  acb_poly_majorant :: Ptr CArbPoly -> Ptr CAcbPoly -> CLong -> IO ()

-- Arithmetic ------------------------------------------------------------------

-- | /_acb_poly_add/ /C/ /A/ /lenA/ /B/ /lenB/ /prec/ 
-- 
-- Sets /{C, max(lenA, lenB)}/ to the sum of /{A, lenA}/ and /{B, lenB}/.
-- Allows aliasing of the input and output operands.
foreign import ccall "acb_poly.h _acb_poly_add"
  _acb_poly_add :: Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h acb_poly_add"
  acb_poly_add :: Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> IO ()

-- | /acb_poly_add_si/ /C/ /A/ /B/ /prec/ 
-- 
-- Sets /C/ to the sum of /A/ and /B/.
foreign import ccall "acb_poly.h acb_poly_add_si"
  acb_poly_add_si :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

-- | /_acb_poly_sub/ /C/ /A/ /lenA/ /B/ /lenB/ /prec/ 
-- 
-- Sets /{C, max(lenA, lenB)}/ to the difference of /{A, lenA}/ and /{B,
-- lenB}/. Allows aliasing of the input and output operands.
foreign import ccall "acb_poly.h _acb_poly_sub"
  _acb_poly_sub :: Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /acb_poly_sub/ /C/ /A/ /B/ /prec/ 
-- 
-- Sets /C/ to the difference of /A/ and /B/.
foreign import ccall "acb_poly.h acb_poly_sub"
  acb_poly_sub :: Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> IO ()

-- | /acb_poly_add_series/ /C/ /A/ /B/ /len/ /prec/ 
-- 
-- Sets /C/ to the sum of /A/ and /B/, truncated to length /len/.
foreign import ccall "acb_poly.h acb_poly_add_series"
  acb_poly_add_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

-- | /acb_poly_sub_series/ /C/ /A/ /B/ /len/ /prec/ 
-- 
-- Sets /C/ to the difference of /A/ and /B/, truncated to length /len/.
foreign import ccall "acb_poly.h acb_poly_sub_series"
  acb_poly_sub_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

-- | /acb_poly_neg/ /C/ /A/ 
-- 
-- Sets /C/ to the negation of /A/.
foreign import ccall "acb_poly.h acb_poly_neg"
  acb_poly_neg :: Ptr CAcbPoly -> Ptr CAcbPoly -> IO ()

-- | /acb_poly_scalar_mul_2exp_si/ /C/ /A/ /c/ 
-- 
-- Sets /C/ to /A/ multiplied by \(2^c\).
foreign import ccall "acb_poly.h acb_poly_scalar_mul_2exp_si"
  acb_poly_scalar_mul_2exp_si :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> IO ()

-- | /acb_poly_scalar_mul/ /C/ /A/ /c/ /prec/ 
-- 
-- Sets /C/ to /A/ multiplied by /c/.
foreign import ccall "acb_poly.h acb_poly_scalar_mul"
  acb_poly_scalar_mul :: Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CAcb -> CLong -> IO ()

-- | /acb_poly_scalar_div/ /C/ /A/ /c/ /prec/ 
-- 
-- Sets /C/ to /A/ divided by /c/.
foreign import ccall "acb_poly.h acb_poly_scalar_div"
  acb_poly_scalar_div :: Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CAcb -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_mullow_classical"
  _acb_poly_mullow_classical :: Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_mullow_transpose"
  _acb_poly_mullow_transpose :: Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_mullow_transpose_gauss"
  _acb_poly_mullow_transpose_gauss :: Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

-- | /_acb_poly_mullow/ /C/ /A/ /lenA/ /B/ /lenB/ /n/ /prec/ 
-- 
-- Sets /{C, n}/ to the product of /{A, lenA}/ and /{B, lenB}/, truncated
-- to length /n/. The output is not allowed to be aliased with either of
-- the inputs. We require \(\mathrm{lenA} \ge \mathrm{lenB} > 0\),
-- \(n > 0\), \(\mathrm{lenA} + \mathrm{lenB} - 1 \ge n\).
-- 
-- The /classical/ version uses a plain loop.
-- 
-- The /transpose/ version evaluates the product using four real polynomial
-- multiplications (via @_arb_poly_mullow@).
-- 
-- The /transpose_gauss/ version evaluates the product using three real
-- polynomial multiplications. This is almost always faster than
-- /transpose/, but has worse numerical stability when the coefficients
-- vary in magnitude.
-- 
-- The default function @_acb_poly_mullow@ automatically switches been
-- /classical/ and /transpose/ multiplication.
-- 
-- If the input pointers are identical (and the lengths are the same), they
-- are assumed to represent the same polynomial, and its square is
-- computed.
foreign import ccall "acb_poly.h _acb_poly_mullow"
  _acb_poly_mullow :: Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h acb_poly_mullow_classical"
  acb_poly_mullow_classical :: Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h acb_poly_mullow_transpose"
  acb_poly_mullow_transpose :: Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h acb_poly_mullow_transpose_gauss"
  acb_poly_mullow_transpose_gauss :: Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

-- | /acb_poly_mullow/ /C/ /A/ /B/ /n/ /prec/ 
-- 
-- Sets /C/ to the product of /A/ and /B/, truncated to length /n/. If the
-- same variable is passed for /A/ and /B/, sets /C/ to the square of /A/
-- truncated to length /n/.
foreign import ccall "acb_poly.h acb_poly_mullow"
  acb_poly_mullow :: Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

-- | /_acb_poly_mul/ /C/ /A/ /lenA/ /B/ /lenB/ /prec/ 
-- 
-- Sets /{C, lenA + lenB - 1}/ to the product of /{A, lenA}/ and /{B,
-- lenB}/. The output is not allowed to be aliased with either of the
-- inputs. We require \(\mathrm{lenA} \ge \mathrm{lenB} > 0\). This
-- function is implemented as a simple wrapper for @_acb_poly_mullow@.
-- 
-- If the input pointers are identical (and the lengths are the same), they
-- are assumed to represent the same polynomial, and its square is
-- computed.
foreign import ccall "acb_poly.h _acb_poly_mul"
  _acb_poly_mul :: Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /acb_poly_mul/ /C/ /A1/ /B2/ /prec/ 
-- 
-- Sets /C/ to the product of /A/ and /B/. If the same variable is passed
-- for /A/ and /B/, sets /C/ to the square of /A/.
foreign import ccall "acb_poly.h acb_poly_mul"
  acb_poly_mul :: Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> IO ()

-- | /_acb_poly_inv_series/ /Qinv/ /Q/ /Qlen/ /len/ /prec/ 
-- 
-- Sets /{Qinv, len}/ to the power series inverse of /{Q, Qlen}/. Uses
-- Newton iteration.
foreign import ccall "acb_poly.h _acb_poly_inv_series"
  _acb_poly_inv_series :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

-- | /acb_poly_inv_series/ /Qinv/ /Q/ /n/ /prec/ 
-- 
-- Sets /Qinv/ to the power series inverse of /Q/.
foreign import ccall "acb_poly.h acb_poly_inv_series"
  acb_poly_inv_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

-- | /_acb_poly_div_series/ /Q/ /A/ /Alen/ /B/ /Blen/ /n/ /prec/ 
-- 
-- Sets /{Q, n}/ to the power series quotient of /{A, Alen}/ by /{B,
-- Blen}/. Uses Newton iteration followed by multiplication.
foreign import ccall "acb_poly.h _acb_poly_div_series"
  _acb_poly_div_series :: Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

-- | /acb_poly_div_series/ /Q/ /A/ /B/ /n/ /prec/ 
-- 
-- Sets /Q/ to the power series quotient /A/ divided by /B/, truncated to
-- length /n/.
foreign import ccall "acb_poly.h acb_poly_div_series"
  acb_poly_div_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_div"
  _acb_poly_div :: Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_rem"
  _acb_poly_rem :: Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_divrem"
  _acb_poly_divrem :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /acb_poly_divrem/ /Q/ /R/ /A/ /B/ /prec/ 
-- 
-- Performs polynomial division with remainder, computing a quotient \(Q\)
-- and a remainder \(R\) such that \(A = BQ + R\). The implementation
-- reverses the inputs and performs power series division.
-- 
-- If the leading coefficient of \(B\) contains zero (or if \(B\) is
-- identically zero), returns 0 indicating failure without modifying the
-- outputs. Otherwise returns nonzero.
foreign import ccall "acb_poly.h acb_poly_divrem"
  acb_poly_divrem :: Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> IO CInt

-- | /_acb_poly_div_root/ /Q/ /R/ /A/ /len/ /c/ /prec/ 
-- 
-- Divides \(A\) by the polynomial \(x - c\), computing the quotient \(Q\)
-- as well as the remainder \(R = f(c)\).
foreign import ccall "acb_poly.h _acb_poly_div_root"
  _acb_poly_div_root :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> IO ()

-- Composition -----------------------------------------------------------------

-- | /_acb_poly_taylor_shift/ /g/ /c/ /n/ /prec/ 
-- 
-- Sets /g/ to the Taylor shift \(f(x+c)\). The underscore methods act
-- in-place on /g/ = /f/ which has length /n/.
foreign import ccall "acb_poly.h _acb_poly_taylor_shift"
  _acb_poly_taylor_shift :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /_acb_poly_compose/ /res/ /poly1/ /len1/ /poly2/ /len2/ /prec/ 
-- 
-- Sets /res/ to the composition \(h(x) = f(g(x))\) where \(f\) is given by
-- /poly1/ and \(g\) is given by /poly2/. The underscore method does not
-- support aliasing of the output with either input polynomial.
foreign import ccall "acb_poly.h _acb_poly_compose"
  _acb_poly_compose :: Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /_acb_poly_compose_series/ /res/ /poly1/ /len1/ /poly2/ /len2/ /n/ /prec/ 
-- 
-- Sets /res/ to the power series composition \(h(x) = f(g(x))\) truncated
-- to order \(O(x^n)\) where \(f\) is given by /poly1/ and \(g\) is given
-- by /poly2/. Wraps @_gr_poly_compose_series@ which chooses automatically
-- between various algorithms.
-- 
-- We require that the constant term in \(g(x)\) is exactly zero. The
-- underscore method does not support aliasing of the output with either
-- input polynomial.
foreign import ccall "acb_poly.h _acb_poly_compose_series"
  _acb_poly_compose_series :: Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_revert_series_lagrange"
  _acb_poly_revert_series_lagrange :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h acb_poly_revert_series_lagrange"
  acb_poly_revert_series_lagrange :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_revert_series_newton"
  _acb_poly_revert_series_newton :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h acb_poly_revert_series_newton"
  acb_poly_revert_series_newton :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_revert_series_lagrange_fast"
  _acb_poly_revert_series_lagrange_fast :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h acb_poly_revert_series_lagrange_fast"
  acb_poly_revert_series_lagrange_fast :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_revert_series"
  _acb_poly_revert_series :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

-- | /acb_poly_revert_series/ /h/ /f/ /n/ /prec/ 
-- 
-- Sets \(h\) to the power series reversion of \(f\), i.e. the expansion of
-- the compositional inverse function \(f^{-1}(x)\), truncated to order
-- \(O(x^n)\), using respectively Lagrange inversion, Newton iteration,
-- fast Lagrange inversion, and a default algorithm choice.
-- 
-- We require that the constant term in \(f\) is exactly zero and that the
-- linear term is nonzero. The underscore methods assume that /flen/ is at
-- least 2, and do not support aliasing.
foreign import ccall "acb_poly.h acb_poly_revert_series"
  acb_poly_revert_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

-- Evaluation ------------------------------------------------------------------

foreign import ccall "acb_poly.h _acb_poly_evaluate_horner"
  _acb_poly_evaluate_horner :: Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> IO ()

foreign import ccall "acb_poly.h acb_poly_evaluate_horner"
  acb_poly_evaluate_horner :: Ptr CAcb -> Ptr CAcbPoly -> Ptr CAcb -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_evaluate_rectangular"
  _acb_poly_evaluate_rectangular :: Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> IO ()

foreign import ccall "acb_poly.h acb_poly_evaluate_rectangular"
  acb_poly_evaluate_rectangular :: Ptr CAcb -> Ptr CAcbPoly -> Ptr CAcb -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_evaluate"
  _acb_poly_evaluate :: Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> IO ()

-- | /acb_poly_evaluate/ /y/ /f/ /x/ /prec/ 
-- 
-- Sets \(y = f(x)\), evaluated respectively using Horner\'s rule,
-- rectangular splitting, and an automatic algorithm choice.
foreign import ccall "acb_poly.h acb_poly_evaluate"
  acb_poly_evaluate :: Ptr CAcb -> Ptr CAcbPoly -> Ptr CAcb -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_evaluate2_horner"
  _acb_poly_evaluate2_horner :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> IO ()

foreign import ccall "acb_poly.h acb_poly_evaluate2_horner"
  acb_poly_evaluate2_horner :: Ptr CAcb -> Ptr CAcb -> Ptr CAcbPoly -> Ptr CAcb -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_evaluate2_rectangular"
  _acb_poly_evaluate2_rectangular :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> IO ()

foreign import ccall "acb_poly.h acb_poly_evaluate2_rectangular"
  acb_poly_evaluate2_rectangular :: Ptr CAcb -> Ptr CAcb -> Ptr CAcbPoly -> Ptr CAcb -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_evaluate2"
  _acb_poly_evaluate2 :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> IO ()

-- | /acb_poly_evaluate2/ /y/ /z/ /f/ /x/ /prec/ 
-- 
-- Sets \(y = f(x), z = f'(x)\), evaluated respectively using Horner\'s
-- rule, rectangular splitting, and an automatic algorithm choice.
-- 
-- When Horner\'s rule is used, the only advantage of evaluating the
-- function and its derivative simultaneously is that one does not have to
-- generate the derivative polynomial explicitly. With the rectangular
-- splitting algorithm, the powers can be reused, making simultaneous
-- evaluation slightly faster.
foreign import ccall "acb_poly.h acb_poly_evaluate2"
  acb_poly_evaluate2 :: Ptr CAcb -> Ptr CAcb -> Ptr CAcbPoly -> Ptr CAcb -> CLong -> IO ()

-- Product trees ---------------------------------------------------------------

foreign import ccall "acb_poly.h _acb_poly_product_roots"
  _acb_poly_product_roots :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /acb_poly_product_roots/ /poly/ /xs/ /n/ /prec/ 
-- 
-- Generates the polynomial \((x-x_0)(x-x_1)\cdots(x-x_{n-1})\).
foreign import ccall "acb_poly.h acb_poly_product_roots"
  acb_poly_product_roots :: Ptr CAcbPoly -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /_acb_poly_tree_alloc/ /len/ 
-- 
-- Returns an initialized data structured capable of representing a
-- remainder tree (product tree) of /len/ roots.
foreign import ccall "acb_poly.h _acb_poly_tree_alloc"
  _acb_poly_tree_alloc :: CLong -> IO (Ptr (Ptr CAcb))

-- | /_acb_poly_tree_free/ /tree/ /len/ 
-- 
-- Deallocates a tree structure as allocated using /_acb_poly_tree_alloc/.
foreign import ccall "acb_poly.h _acb_poly_tree_free"
  _acb_poly_tree_free :: Ptr (Ptr CAcb) -> CLong -> IO ()

-- | /_acb_poly_tree_build/ /tree/ /roots/ /len/ /prec/ 
-- 
-- Constructs a product tree from a given array of /len/ roots. The tree
-- structure must be pre-allocated to the specified length using
-- @_acb_poly_tree_alloc@.
foreign import ccall "acb_poly.h _acb_poly_tree_build"
  _acb_poly_tree_build :: Ptr (Ptr CAcb) -> Ptr CAcb -> CLong -> CLong -> IO ()

-- Multipoint evaluation -------------------------------------------------------

foreign import ccall "acb_poly.h _acb_poly_evaluate_vec_iter"
  _acb_poly_evaluate_vec_iter :: Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /acb_poly_evaluate_vec_iter/ /ys/ /poly/ /xs/ /n/ /prec/ 
-- 
-- Evaluates the polynomial simultaneously at /n/ given points, calling
-- @_acb_poly_evaluate@ repeatedly.
foreign import ccall "acb_poly.h acb_poly_evaluate_vec_iter"
  acb_poly_evaluate_vec_iter :: Ptr CAcb -> Ptr CAcbPoly -> Ptr CAcb -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_evaluate_vec_fast_precomp"
  _acb_poly_evaluate_vec_fast_precomp :: Ptr CAcb -> Ptr CAcb -> CLong -> Ptr (Ptr CAcb) -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_evaluate_vec_fast"
  _acb_poly_evaluate_vec_fast :: Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /acb_poly_evaluate_vec_fast/ /ys/ /poly/ /xs/ /n/ /prec/ 
-- 
-- Evaluates the polynomial simultaneously at /n/ given points, using fast
-- multipoint evaluation.
foreign import ccall "acb_poly.h acb_poly_evaluate_vec_fast"
  acb_poly_evaluate_vec_fast :: Ptr CAcb -> Ptr CAcbPoly -> Ptr CAcb -> CLong -> CLong -> IO ()

-- Interpolation ---------------------------------------------------------------

foreign import ccall "acb_poly.h _acb_poly_interpolate_newton"
  _acb_poly_interpolate_newton :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /acb_poly_interpolate_newton/ /poly/ /xs/ /ys/ /n/ /prec/ 
-- 
-- Recovers the unique polynomial of length at most /n/ that interpolates
-- the given /x/ and /y/ values. This implementation first interpolates in
-- the Newton basis and then converts back to the monomial basis.
foreign import ccall "acb_poly.h acb_poly_interpolate_newton"
  acb_poly_interpolate_newton :: Ptr CAcbPoly -> Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_interpolate_barycentric"
  _acb_poly_interpolate_barycentric :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /acb_poly_interpolate_barycentric/ /poly/ /xs/ /ys/ /n/ /prec/ 
-- 
-- Recovers the unique polynomial of length at most /n/ that interpolates
-- the given /x/ and /y/ values. This implementation uses the barycentric
-- form of Lagrange interpolation.
foreign import ccall "acb_poly.h acb_poly_interpolate_barycentric"
  acb_poly_interpolate_barycentric :: Ptr CAcbPoly -> Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_interpolation_weights"
  _acb_poly_interpolation_weights :: Ptr CAcb -> Ptr (Ptr CAcb) -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_interpolate_fast_precomp"
  _acb_poly_interpolate_fast_precomp :: Ptr CAcb -> Ptr CAcb -> Ptr (Ptr CAcb) -> Ptr CAcb -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_interpolate_fast"
  _acb_poly_interpolate_fast :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /acb_poly_interpolate_fast/ /poly/ /xs/ /ys/ /n/ /prec/ 
-- 
-- Recovers the unique polynomial of length at most /n/ that interpolates
-- the given /x/ and /y/ values, using fast Lagrange interpolation. The
-- precomp function takes a precomputed product tree over the /x/ values
-- and a vector of interpolation weights as additional inputs.
foreign import ccall "acb_poly.h acb_poly_interpolate_fast"
  acb_poly_interpolate_fast :: Ptr CAcbPoly -> Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

-- Differentiation -------------------------------------------------------------

-- | /_acb_poly_derivative/ /res/ /poly/ /len/ /prec/ 
-- 
-- Sets /{res, len - 1}/ to the derivative of /{poly, len}/. Allows
-- aliasing of the input and output.
foreign import ccall "acb_poly.h _acb_poly_derivative"
  _acb_poly_derivative :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /acb_poly_derivative/ /res/ /poly/ /prec/ 
-- 
-- Sets /res/ to the derivative of /poly/.
foreign import ccall "acb_poly.h acb_poly_derivative"
  acb_poly_derivative :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> IO ()

-- | /_acb_poly_nth_derivative/ /res/ /poly/ /n/ /len/ /prec/ 
-- 
-- Sets /{res, len - n}/ to the nth derivative of /{poly, len}/. Does
-- nothing if /len \<= n/. Allows aliasing of the input and output.
foreign import ccall "acb_poly.h _acb_poly_nth_derivative"
  _acb_poly_nth_derivative :: Ptr CAcb -> Ptr CAcb -> CULong -> CLong -> CLong -> IO ()

-- | /acb_poly_nth_derivative/ /res/ /poly/ /n/ /prec/ 
-- 
-- Sets /res/ to the nth derivative of /poly/.
foreign import ccall "acb_poly.h acb_poly_nth_derivative"
  acb_poly_nth_derivative :: Ptr CAcbPoly -> Ptr CAcbPoly -> CULong -> CLong -> IO ()

-- | /_acb_poly_integral/ /res/ /poly/ /len/ /prec/ 
-- 
-- Sets /{res, len}/ to the integral of /{poly, len - 1}/. Allows aliasing
-- of the input and output.
foreign import ccall "acb_poly.h _acb_poly_integral"
  _acb_poly_integral :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /acb_poly_integral/ /res/ /poly/ /prec/ 
-- 
-- Sets /res/ to the integral of /poly/.
foreign import ccall "acb_poly.h acb_poly_integral"
  acb_poly_integral :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> IO ()

-- Transforms ------------------------------------------------------------------

foreign import ccall "acb_poly.h _acb_poly_borel_transform"
  _acb_poly_borel_transform :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /acb_poly_borel_transform/ /res/ /poly/ /prec/ 
-- 
-- Computes the Borel transform of the input polynomial, mapping
-- \(\sum_k a_k x^k\) to \(\sum_k (a_k / k!) x^k\). The underscore method
-- allows aliasing.
foreign import ccall "acb_poly.h acb_poly_borel_transform"
  acb_poly_borel_transform :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_inv_borel_transform"
  _acb_poly_inv_borel_transform :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /acb_poly_inv_borel_transform/ /res/ /poly/ /prec/ 
-- 
-- Computes the inverse Borel transform of the input polynomial, mapping
-- \(\sum_k a_k x^k\) to \(\sum_k a_k k! x^k\). The underscore method
-- allows aliasing.
foreign import ccall "acb_poly.h acb_poly_inv_borel_transform"
  acb_poly_inv_borel_transform :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_binomial_transform_basecase"
  _acb_poly_binomial_transform_basecase :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h acb_poly_binomial_transform_basecase"
  acb_poly_binomial_transform_basecase :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_binomial_transform_convolution"
  _acb_poly_binomial_transform_convolution :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h acb_poly_binomial_transform_convolution"
  acb_poly_binomial_transform_convolution :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_binomial_transform"
  _acb_poly_binomial_transform :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

-- | /acb_poly_binomial_transform/ /b/ /a/ /len/ /prec/ 
-- 
-- Computes the binomial transform of the input polynomial, truncating the
-- output to length /len/. See @arb_poly_binomial_transform@ for details.
-- 
-- The underscore methods do not support aliasing, and assume that the
-- lengths are nonzero.
foreign import ccall "acb_poly.h acb_poly_binomial_transform"
  acb_poly_binomial_transform :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_graeffe_transform"
  _acb_poly_graeffe_transform :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /acb_poly_graeffe_transform/ /b/ /a/ /prec/ 
-- 
-- Computes the Graeffe transform of input polynomial, which is of length
-- /len/. See @arb_poly_graeffe_transform@ for details.
-- 
-- The underscore method assumes that /a/ and /b/ are initialized, /a/ is
-- of length /len/, and /b/ is of length at least /len/. Both methods allow
-- aliasing.
foreign import ccall "acb_poly.h acb_poly_graeffe_transform"
  acb_poly_graeffe_transform :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> IO ()

-- Elementary functions --------------------------------------------------------

-- | /_acb_poly_pow_ui_trunc_binexp/ /res/ /f/ /flen/ /exp/ /len/ /prec/ 
-- 
-- Sets /{res, len}/ to /{f, flen}/ raised to the power /exp/, truncated to
-- length /len/. Requires that /len/ is no longer than the length of the
-- power as computed without truncation (i.e. no zero-padding is
-- performed). Does not support aliasing of the input and output, and
-- requires that /flen/ and /len/ are positive. Uses binary exponentiation.
foreign import ccall "acb_poly.h _acb_poly_pow_ui_trunc_binexp"
  _acb_poly_pow_ui_trunc_binexp :: Ptr CAcb -> Ptr CAcb -> CLong -> CULong -> CLong -> CLong -> IO ()

-- | /acb_poly_pow_ui_trunc_binexp/ /res/ /poly/ /exp/ /len/ /prec/ 
-- 
-- Sets /res/ to /poly/ raised to the power /exp/, truncated to length
-- /len/. Uses binary exponentiation.
foreign import ccall "acb_poly.h acb_poly_pow_ui_trunc_binexp"
  acb_poly_pow_ui_trunc_binexp :: Ptr CAcbPoly -> Ptr CAcbPoly -> CULong -> CLong -> CLong -> IO ()

-- | /_acb_poly_pow_ui/ /res/ /f/ /flen/ /exp/ /prec/ 
-- 
-- Sets /res/ to /{f, flen}/ raised to the power /exp/. Does not support
-- aliasing of the input and output, and requires that /flen/ is positive.
foreign import ccall "acb_poly.h _acb_poly_pow_ui"
  _acb_poly_pow_ui :: Ptr CAcb -> Ptr CAcb -> CLong -> CULong -> CLong -> IO ()

-- | /acb_poly_pow_ui/ /res/ /poly/ /exp/ /prec/ 
-- 
-- Sets /res/ to /poly/ raised to the power /exp/.
foreign import ccall "acb_poly.h acb_poly_pow_ui"
  acb_poly_pow_ui :: Ptr CAcbPoly -> Ptr CAcbPoly -> CULong -> CLong -> IO ()

-- | /_acb_poly_pow_series/ /h/ /f/ /flen/ /g/ /glen/ /len/ /prec/ 
-- 
-- Sets /{h, len}/ to the power series
-- \(f(x)^{g(x)} = \exp(g(x) \log f(x))\) truncated to length /len/. This
-- function detects special cases such as /g/ being an exact small integer
-- or \(\pm 1/2\), and computes such powers more efficiently. This function
-- does not support aliasing of the output with either of the input
-- operands. It requires that all lengths are positive, and assumes that
-- /flen/ and /glen/ do not exceed /len/.
foreign import ccall "acb_poly.h _acb_poly_pow_series"
  _acb_poly_pow_series :: Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

-- | /acb_poly_pow_series/ /h/ /f/ /g/ /len/ /prec/ 
-- 
-- Sets /h/ to the power series \(f(x)^{g(x)} = \exp(g(x) \log f(x))\)
-- truncated to length /len/. This function detects special cases such as
-- /g/ being an exact small integer or \(\pm 1/2\), and computes such
-- powers more efficiently.
foreign import ccall "acb_poly.h acb_poly_pow_series"
  acb_poly_pow_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

-- | /_acb_poly_pow_acb_series/ /h/ /f/ /flen/ /g/ /len/ /prec/ 
-- 
-- Sets /{h, len}/ to the power series \(f(x)^g = \exp(g \log f(x))\)
-- truncated to length /len/. This function detects special cases such as
-- /g/ being an exact small integer or \(\pm 1/2\), and computes such
-- powers more efficiently. This function does not support aliasing of the
-- output with either of the input operands. It requires that all lengths
-- are positive, and assumes that /flen/ does not exceed /len/.
foreign import ccall "acb_poly.h _acb_poly_pow_acb_series"
  _acb_poly_pow_acb_series :: Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /acb_poly_pow_acb_series/ /h/ /f/ /g/ /len/ /prec/ 
-- 
-- Sets /h/ to the power series \(f(x)^g = \exp(g \log f(x))\) truncated to
-- length /len/.
foreign import ccall "acb_poly.h acb_poly_pow_acb_series"
  acb_poly_pow_acb_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CAcb -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_sqrt_series"
  _acb_poly_sqrt_series :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

-- | /acb_poly_sqrt_series/ /g/ /h/ /n/ /prec/ 
-- 
-- Sets /g/ to the power series square root of /h/, truncated to length
-- /n/. Uses division-free Newton iteration for the reciprocal square root,
-- followed by a multiplication.
-- 
-- The underscore method does not support aliasing of the input and output
-- arrays. It requires that /hlen/ and /n/ are greater than zero.
foreign import ccall "acb_poly.h acb_poly_sqrt_series"
  acb_poly_sqrt_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_rsqrt_series"
  _acb_poly_rsqrt_series :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

-- | /acb_poly_rsqrt_series/ /g/ /h/ /n/ /prec/ 
-- 
-- Sets /g/ to the reciprocal power series square root of /h/, truncated to
-- length /n/. Uses division-free Newton iteration.
-- 
-- The underscore method does not support aliasing of the input and output
-- arrays. It requires that /hlen/ and /n/ are greater than zero.
foreign import ccall "acb_poly.h acb_poly_rsqrt_series"
  acb_poly_rsqrt_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_log_series"
  _acb_poly_log_series :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

-- | /acb_poly_log_series/ /res/ /f/ /n/ /prec/ 
-- 
-- Sets /res/ to the power series logarithm of /f/, truncated to length
-- /n/. Uses the formula \(\log(f(x)) = \int f'(x) / f(x) dx\), adding the
-- logarithm of the constant term in /f/ as the constant of integration.
-- 
-- The underscore method supports aliasing of the input and output arrays.
-- It requires that /flen/ and /n/ are greater than zero.
foreign import ccall "acb_poly.h acb_poly_log_series"
  acb_poly_log_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_log1p_series"
  _acb_poly_log1p_series :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

-- | /acb_poly_log1p_series/ /res/ /f/ /n/ /prec/ 
-- 
-- Computes the power series \(\log(1+f)\), with better accuracy when the
-- constant term of /f/ is small.
foreign import ccall "acb_poly.h acb_poly_log1p_series"
  acb_poly_log1p_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_atan_series"
  _acb_poly_atan_series :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

-- | /acb_poly_atan_series/ /res/ /f/ /n/ /prec/ 
-- 
-- Sets /res/ the power series inverse tangent of /f/, truncated to length
-- /n/.
-- 
-- Uses the formula
-- 
-- \[`\]
-- \[\tan^{-1}(f(x)) = \int f'(x) / (1+f(x)^2) dx,\]
-- 
-- adding the function of the constant term in /f/ as the constant of
-- integration.
-- 
-- The underscore method supports aliasing of the input and output arrays.
-- It requires that /flen/ and /n/ are greater than zero.
foreign import ccall "acb_poly.h acb_poly_atan_series"
  acb_poly_atan_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_exp_series_basecase"
  _acb_poly_exp_series_basecase :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h acb_poly_exp_series_basecase"
  acb_poly_exp_series_basecase :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_exp_series"
  _acb_poly_exp_series :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

-- | /acb_poly_exp_series/ /f/ /h/ /n/ /prec/ 
-- 
-- Sets \(f\) to the power series exponential of \(h\), truncated to length
-- \(n\).
-- 
-- The basecase version uses a simple recurrence for the coefficients,
-- requiring \(O(nm)\) operations where \(m\) is the length of \(h\).
-- 
-- The main implementation uses Newton iteration, starting from a small
-- number of terms given by the basecase algorithm. The complexity is
-- \(O(M(n))\). Redundant operations in the Newton iteration are avoided by
-- using the scheme described in < [HZ2004]>.
-- 
-- The underscore methods support aliasing and allow the input to be
-- shorter than the output, but require the lengths to be nonzero.
foreign import ccall "acb_poly.h acb_poly_exp_series"
  acb_poly_exp_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_exp_pi_i_series"
  _acb_poly_exp_pi_i_series :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

-- | /acb_poly_exp_pi_i_series/ /f/ /h/ /n/ /prec/ 
-- 
-- Sets /f/ to the power series \(\exp(\pi i h)\) truncated to length /n/.
-- The underscore method supports aliasing and allows the input to be
-- shorter than the output, but requires the lengths to be nonzero.
foreign import ccall "acb_poly.h acb_poly_exp_pi_i_series"
  acb_poly_exp_pi_i_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

-- | /_acb_poly_sin_cos_series/ /s/ /c/ /h/ /hlen/ /n/ /prec/ 
-- 
-- Sets /s/ and /c/ to the power series sine and cosine of /h/, computed
-- simultaneously. The underscore method supports aliasing and requires the
-- lengths to be nonzero.
foreign import ccall "acb_poly.h _acb_poly_sin_cos_series"
  _acb_poly_sin_cos_series :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_sin_series"
  _acb_poly_sin_series :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h acb_poly_sin_series"
  acb_poly_sin_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_cos_series"
  _acb_poly_cos_series :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

-- | /acb_poly_cos_series/ /c/ /h/ /n/ /prec/ 
-- 
-- Respectively evaluates the power series sine or cosine. These functions
-- simply wrap @_acb_poly_sin_cos_series@. The underscore methods support
-- aliasing and require the lengths to be nonzero.
foreign import ccall "acb_poly.h acb_poly_cos_series"
  acb_poly_cos_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_tan_series"
  _acb_poly_tan_series :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

-- | /acb_poly_tan_series/ /g/ /h/ /n/ /prec/ 
-- 
-- Sets /g/ to the power series tangent of /h/.
-- 
-- For small /n/ takes the quotient of the sine and cosine as computed
-- using the basecase algorithm. For large /n/, uses Newton iteration to
-- invert the inverse tangent series. The complexity is \(O(M(n))\).
-- 
-- The underscore version does not support aliasing, and requires the
-- lengths to be nonzero.
foreign import ccall "acb_poly.h acb_poly_tan_series"
  acb_poly_tan_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_sin_cos_pi_series"
  _acb_poly_sin_cos_pi_series :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h acb_poly_sin_cos_pi_series"
  acb_poly_sin_cos_pi_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_sin_pi_series"
  _acb_poly_sin_pi_series :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h acb_poly_sin_pi_series"
  acb_poly_sin_pi_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_cos_pi_series"
  _acb_poly_cos_pi_series :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h acb_poly_cos_pi_series"
  acb_poly_cos_pi_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_cot_pi_series"
  _acb_poly_cot_pi_series :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

-- | /acb_poly_cot_pi_series/ /c/ /h/ /n/ /prec/ 
-- 
-- Compute the respective trigonometric functions of the input multiplied
-- by \(\pi\).
foreign import ccall "acb_poly.h acb_poly_cot_pi_series"
  acb_poly_cot_pi_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_sinh_cosh_series_basecase"
  _acb_poly_sinh_cosh_series_basecase :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h acb_poly_sinh_cosh_series_basecase"
  acb_poly_sinh_cosh_series_basecase :: Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_sinh_cosh_series_exponential"
  _acb_poly_sinh_cosh_series_exponential :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h acb_poly_sinh_cosh_series_exponential"
  acb_poly_sinh_cosh_series_exponential :: Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_sinh_cosh_series"
  _acb_poly_sinh_cosh_series :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h acb_poly_sinh_cosh_series"
  acb_poly_sinh_cosh_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_sinh_series"
  _acb_poly_sinh_series :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h acb_poly_sinh_series"
  acb_poly_sinh_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_cosh_series"
  _acb_poly_cosh_series :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

-- | /acb_poly_cosh_series/ /c/ /h/ /n/ /prec/ 
-- 
-- Sets /s/ and /c/ respectively to the hyperbolic sine and cosine of the
-- power series /h/, truncated to length /n/.
-- 
-- The implementations mirror those for sine and cosine, except that the
-- /exponential/ version computes both functions using the exponential
-- function instead of the hyperbolic tangent.
foreign import ccall "acb_poly.h acb_poly_cosh_series"
  acb_poly_cosh_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_sinc_series"
  _acb_poly_sinc_series :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

-- | /acb_poly_sinc_series/ /s/ /h/ /n/ /prec/ 
-- 
-- Sets /s/ to the sinc function of the power series /h/, truncated to
-- length /n/.
foreign import ccall "acb_poly.h acb_poly_sinc_series"
  acb_poly_sinc_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

-- Lambert W function ----------------------------------------------------------

foreign import ccall "acb_poly.h _acb_poly_lambertw_series"
  _acb_poly_lambertw_series :: Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CFmpz -> CInt -> CLong -> CLong -> IO ()

-- | /acb_poly_lambertw_series/ /res/ /z/ /k/ /flags/ /len/ /prec/ 
-- 
-- Sets /res/ to branch /k/ of the Lambert W function of the power series
-- /z/. The argument /flags/ is reserved for future use. The underscore
-- method allows aliasing, but assumes that the lengths are nonzero.
foreign import ccall "acb_poly.h acb_poly_lambertw_series"
  acb_poly_lambertw_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CFmpz -> CInt -> CLong -> CLong -> IO ()

-- Gamma function --------------------------------------------------------------

foreign import ccall "acb_poly.h _acb_poly_gamma_series"
  _acb_poly_gamma_series :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h acb_poly_gamma_series"
  acb_poly_gamma_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_rgamma_series"
  _acb_poly_rgamma_series :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h acb_poly_rgamma_series"
  acb_poly_rgamma_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_lgamma_series"
  _acb_poly_lgamma_series :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h acb_poly_lgamma_series"
  acb_poly_lgamma_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_digamma_series"
  _acb_poly_digamma_series :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

-- | /acb_poly_digamma_series/ /res/ /h/ /n/ /prec/ 
-- 
-- Sets /res/ to the series expansion of \(\Gamma(h(x))\),
-- \(1/\Gamma(h(x))\), or \(\log \Gamma(h(x))\), \(\psi(h(x))\), truncated
-- to length /n/.
-- 
-- These functions first generate the Taylor series at the constant term of
-- /h/, and then call @_acb_poly_compose_series@. The Taylor coefficients
-- are generated using Stirling\'s series.
-- 
-- The underscore methods support aliasing of the input and output arrays,
-- and require that /hlen/ and /n/ are greater than zero.
foreign import ccall "acb_poly.h acb_poly_digamma_series"
  acb_poly_digamma_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_rising_ui_series"
  _acb_poly_rising_ui_series :: Ptr CAcb -> Ptr CAcb -> CLong -> CULong -> CLong -> CLong -> IO ()

-- | /acb_poly_rising_ui_series/ /res/ /f/ /r/ /trunc/ /prec/ 
-- 
-- Sets /res/ to the rising factorial \((f) (f+1) (f+2) \cdots (f+r-1)\),
-- truncated to length /trunc/. The underscore method assumes that /flen/,
-- /r/ and /trunc/ are at least 1, and does not support aliasing. Uses
-- binary splitting.
foreign import ccall "acb_poly.h acb_poly_rising_ui_series"
  acb_poly_rising_ui_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> CULong -> CLong -> CLong -> IO ()

-- Power sums ------------------------------------------------------------------

foreign import ccall "acb_poly.h _acb_poly_powsum_series_naive"
  _acb_poly_powsum_series_naive :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

-- | /_acb_poly_powsum_series_naive_threaded/ /z/ /s/ /a/ /q/ /n/ /len/ /prec/ 
-- 
-- Computes
-- 
-- \[`\]
-- \[z = S(s,a,n) = \sum_{k=0}^{n-1} \frac{q^k}{(k+a)^{s+t}}\]
-- 
-- as a power series in \(t\) truncated to length /len/. This function
-- evaluates the sum naively term by term. The /threaded/ version splits
-- the computation over the number of threads returned by
-- /flint_get_num_threads()/.
foreign import ccall "acb_poly.h _acb_poly_powsum_series_naive_threaded"
  _acb_poly_powsum_series_naive_threaded :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

-- | /_acb_poly_powsum_one_series_sieved/ /z/ /s/ /n/ /len/ /prec/ 
-- 
-- Computes
-- 
-- \[`\]
-- \[z = S(s,1,n) \sum_{k=1}^n \frac{1}{k^{s+t}}\]
-- 
-- as a power series in \(t\) truncated to length /len/. This function
-- stores a table of powers that have already been calculated, computing
-- \((ij)^r\) as \(i^r j^r\) whenever \(k = ij\) is composite. As a further
-- optimization, it groups all even \(k\) and evaluates the sum as a
-- polynomial in \(2^{-(s+t)}\). This scheme requires about \(n / \log n\)
-- powers, \(n / 2\) multiplications, and temporary storage of \(n / 6\)
-- power series. Due to the extra power series multiplications, it is only
-- faster than the naive algorithm when /len/ is small.
foreign import ccall "acb_poly.h _acb_poly_powsum_one_series_sieved"
  _acb_poly_powsum_one_series_sieved :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

-- Zeta function ---------------------------------------------------------------

-- | /_acb_poly_zeta_em_choose_param/ /bound/ /N/ /M/ /s/ /a/ /d/ /target/ /prec/ 
-- 
-- Chooses /N/ and /M/ for Euler-Maclaurin summation of the Hurwitz zeta
-- function, using a default algorithm.
foreign import ccall "acb_poly.h _acb_poly_zeta_em_choose_param"
  _acb_poly_zeta_em_choose_param :: Ptr CMag -> Ptr CULong -> Ptr CULong -> Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_zeta_em_bound1"
  _acb_poly_zeta_em_bound1 :: Ptr CMag -> Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> CLong -> IO ()

-- | /_acb_poly_zeta_em_bound/ /vec/ /s/ /a/ /N/ /M/ /d/ /wp/ 
-- 
-- Compute bounds for Euler-Maclaurin evaluation of the Hurwitz zeta
-- function or its power series, using the formulas in < [Joh2013]>.
foreign import ccall "acb_poly.h _acb_poly_zeta_em_bound"
  _acb_poly_zeta_em_bound :: Ptr CArb -> Ptr CAcb -> Ptr CAcb -> CULong -> CULong -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_zeta_em_tail_naive"
  _acb_poly_zeta_em_tail_naive :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

-- | /_acb_poly_zeta_em_tail_bsplit/ /z/ /s/ /Na/ /Nasx/ /M/ /len/ /prec/ 
-- 
-- Evaluates the tail in the Euler-Maclaurin sum for the Hurwitz zeta
-- function, respectively using the naive recurrence and binary splitting.
foreign import ccall "acb_poly.h _acb_poly_zeta_em_tail_bsplit"
  _acb_poly_zeta_em_tail_bsplit :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

-- | /_acb_poly_zeta_em_sum/ /z/ /s/ /a/ /deflate/ /N/ /M/ /d/ /prec/ 
-- 
-- Evaluates the truncated Euler-Maclaurin sum of order \(N, M\) for the
-- length-/d/ truncated Taylor series of the Hurwitz zeta function
-- \(\zeta(s,a)\) at \(s\), using a working precision of /prec/ bits. With
-- \(a = 1\), this gives the usual Riemann zeta function.
-- 
-- If /deflate/ is nonzero, \(\zeta(s,a) - 1/(s-1)\) is evaluated (which
-- permits series expansion at \(s = 1\)).
foreign import ccall "acb_poly.h _acb_poly_zeta_em_sum"
  _acb_poly_zeta_em_sum :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CInt -> CULong -> CULong -> CLong -> CLong -> IO ()

-- | /_acb_poly_zeta_cpx_series/ /z/ /s/ /a/ /deflate/ /d/ /prec/ 
-- 
-- Computes the series expansion of \(\zeta(s+x,a)\) (or
-- \(\zeta(s+x,a) - 1/(s+x-1)\) if /deflate/ is nonzero) to order /d/.
-- 
-- This function wraps @_acb_poly_zeta_em_sum@, automatically choosing
-- default values for \(N, M\) using @_acb_poly_zeta_em_choose_param@ to
-- target an absolute truncation error of \(2^{-\operatorname{prec}}\).
foreign import ccall "acb_poly.h _acb_poly_zeta_cpx_series"
  _acb_poly_zeta_cpx_series :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_zeta_series"
  _acb_poly_zeta_series :: Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CAcb -> CInt -> CLong -> CLong -> IO ()

-- | /acb_poly_zeta_series/ /res/ /f/ /a/ /deflate/ /n/ /prec/ 
-- 
-- Sets /res/ to the Hurwitz zeta function \(\zeta(s,a)\) where \(s\) a
-- power series and \(a\) is a constant, truncated to length /n/. To
-- evaluate the usual Riemann zeta function, set \(a = 1\).
-- 
-- If /deflate/ is nonzero, evaluates \(\zeta(s,a) + 1/(1-s)\), which is
-- well-defined as a limit when the constant term of \(s\) is 1. In
-- particular, expanding \(\zeta(s,a) + 1/(1-s)\) with \(s = 1+x\) gives
-- the Stieltjes constants
-- 
-- \[`\]
-- \[\sum_{k=0}^{n-1} \frac{(-1)^k}{k!} \gamma_k(a) x^k`.\]
-- 
-- If \(a = 1\), this implementation uses the reflection formula if the
-- midpoint of the constant term of \(s\) is negative.
foreign import ccall "acb_poly.h acb_poly_zeta_series"
  acb_poly_zeta_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CAcb -> CInt -> CLong -> CLong -> IO ()

-- Other special functions -----------------------------------------------------

foreign import ccall "acb_poly.h _acb_poly_polylog_cpx_small"
  _acb_poly_polylog_cpx_small :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_polylog_cpx_zeta"
  _acb_poly_polylog_cpx_zeta :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /_acb_poly_polylog_cpx/ /w/ /s/ /z/ /len/ /prec/ 
-- 
-- Sets /w/ to the Taylor series with respect to /x/ of the polylogarithm
-- \(\operatorname{Li}_{s+x}(z)\), where /s/ and /z/ are given complex
-- constants. The output is computed to length /len/ which must be
-- positive. Aliasing between /w/ and /s/ or /z/ is not permitted.
-- 
-- The /small/ version uses the standard power series expansion with
-- respect to /z/, convergent when \(|z| < 1\). The /zeta/ version
-- evaluates the polylogarithm as a sum of two Hurwitz zeta functions. The
-- default version automatically delegates to the /small/ version when /z/
-- is close to zero, and the /zeta/ version otherwise. For further details,
-- see @algorithms_polylogarithms@.
foreign import ccall "acb_poly.h _acb_poly_polylog_cpx"
  _acb_poly_polylog_cpx :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_polylog_series"
  _acb_poly_polylog_series :: Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /acb_poly_polylog_series/ /w/ /s/ /z/ /len/ /prec/ 
-- 
-- Sets /w/ to the polylogarithm \(\operatorname{Li}_{s}(z)\) where /s/ is
-- a given power series, truncating the output to length /len/. The
-- underscore method requires all lengths to be positive and supports
-- aliasing between all inputs and outputs.
foreign import ccall "acb_poly.h acb_poly_polylog_series"
  acb_poly_polylog_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CAcb -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_erf_series"
  _acb_poly_erf_series :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

-- | /acb_poly_erf_series/ /res/ /z/ /n/ /prec/ 
-- 
-- Sets /res/ to the error function of the power series /z/, truncated to
-- length /n/. These methods are provided for backwards compatibility. See
-- @acb_hypgeom_erf_series@, @acb_hypgeom_erfc_series@,
-- @acb_hypgeom_erfi_series@.
foreign import ccall "acb_poly.h acb_poly_erf_series"
  acb_poly_erf_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_agm1_series"
  _acb_poly_agm1_series :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

-- | /acb_poly_agm1_series/ /res/ /z/ /n/ /prec/ 
-- 
-- Sets /res/ to the arithmetic-geometric mean of 1 and the power series
-- /z/, truncated to length /n/.
foreign import ccall "acb_poly.h acb_poly_agm1_series"
  acb_poly_agm1_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

-- See the @acb_elliptic.h \<acb-elliptic>@ module for power series of
-- elliptic functions. The following wrappers are available for backwards
-- compatibility.
--
foreign import ccall "acb_poly.h _acb_poly_elliptic_k_series"
  _acb_poly_elliptic_k_series :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h acb_poly_elliptic_k_series"
  acb_poly_elliptic_k_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_elliptic_p_series"
  _acb_poly_elliptic_p_series :: Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h acb_poly_elliptic_p_series"
  acb_poly_elliptic_p_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CAcb -> CLong -> CLong -> IO ()

-- Root-finding ----------------------------------------------------------------

foreign import ccall "acb_poly.h _acb_poly_root_bound_fujiwara"
  _acb_poly_root_bound_fujiwara :: Ptr CMag -> Ptr CAcb -> CLong -> IO ()

-- | /acb_poly_root_bound_fujiwara/ /bound/ /poly/ 
-- 
-- Sets /bound/ to an upper bound for the magnitude of all the complex
-- roots of /poly/. Uses Fujiwara\'s bound
-- 
-- \[`\]
-- \[2 \max \left\{\left|\frac{a_{n-1}}{a_n}\right|,
--               \left|\frac{a_{n-2}}{a_n}\right|^{1/2},
--               \cdots,
--               \left|\frac{a_1}{a_n}\right|^{1/(n-1)},
--               \left|\frac{a_0}{2a_n}\right|^{1/n}
--        \right\}\]
-- 
-- where \(a_0, \ldots, a_n\) are the coefficients of /poly/.
foreign import ccall "acb_poly.h acb_poly_root_bound_fujiwara"
  acb_poly_root_bound_fujiwara :: Ptr CMag -> Ptr CAcbPoly -> IO ()

-- | /_acb_poly_root_inclusion/ /r/ /m/ /poly/ /polyder/ /len/ /prec/ 
-- 
-- Given any complex number \(m\), and a nonconstant polynomial \(f\) and
-- its derivative \(f'\), sets /r/ to a complex interval centered on \(m\)
-- that is guaranteed to contain at least one root of \(f\). Such an
-- interval is obtained by taking a ball of radius \(|f(m)/f'(m)| n\) where
-- \(n\) is the degree of \(f\). Proof: assume that the distance to the
-- nearest root exceeds \(r = |f(m)/f'(m)| n\). Then
-- 
-- \[`\]
-- \[\left|\frac{f'(m)}{f(m)}\right| =
--     \left|\sum_i \frac{1}{m-\zeta_i}\right|
--     \le \sum_i \frac{1}{|m-\zeta_i|}
--     < \frac{n}{r} = \left|\frac{f'(m)}{f(m)}\right|\]
-- 
-- which is a contradiction (see < [Kob2010]>).
foreign import ccall "acb_poly.h _acb_poly_root_inclusion"
  _acb_poly_root_inclusion :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /_acb_poly_validate_roots/ /roots/ /poly/ /len/ /prec/ 
-- 
-- Given a list of approximate roots of the input polynomial, this function
-- sets a rigorous bounding interval for each root, and determines which
-- roots are isolated from all the other roots. It then rearranges the list
-- of roots so that the isolated roots are at the front of the list, and
-- returns the count of isolated roots.
-- 
-- If the return value equals the degree of the polynomial, then all roots
-- have been found. If the return value is smaller, all the remaining
-- output intervals are guaranteed to contain roots, but it is possible
-- that not all of the polynomial\'s roots are contained among them.
foreign import ccall "acb_poly.h _acb_poly_validate_roots"
  _acb_poly_validate_roots :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO CLong

-- | /_acb_poly_refine_roots_durand_kerner/ /roots/ /poly/ /len/ /prec/ 
-- 
-- Refines the given roots simultaneously using a single iteration of the
-- Durand-Kerner method. The radius of each root is set to an approximation
-- of the correction, giving a rough estimate of its error (not a rigorous
-- bound).
foreign import ccall "acb_poly.h _acb_poly_refine_roots_durand_kerner"
  _acb_poly_refine_roots_durand_kerner :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

foreign import ccall "acb_poly.h _acb_poly_find_roots"
  _acb_poly_find_roots :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO CLong

-- | /acb_poly_find_roots/ /roots/ /poly/ /initial/ /maxiter/ /prec/ 
-- 
-- Attempts to compute all the roots of the given nonzero polynomial /poly/
-- using a working precision of /prec/ bits. If /n/ denotes the degree of
-- /poly/, the function writes /n/ approximate roots with rigorous error
-- bounds to the preallocated array /roots/, and returns the number of
-- roots that are isolated.
-- 
-- If the return value equals the degree of the polynomial, then all roots
-- have been found. If the return value is smaller, all the output
-- intervals are guaranteed to contain roots, but it is possible that not
-- all of the polynomial\'s roots are contained among them.
-- 
-- The roots are computed numerically by performing several steps with the
-- Durand-Kerner method and terminating if the estimated accuracy of the
-- roots approaches the working precision or if the number of steps exceeds
-- /maxiter/, which can be set to zero in order to use a default value.
-- Finally, the approximate roots are validated rigorously.
-- 
-- Initial values for the iteration can be provided as the array /initial/.
-- If /initial/ is set to /NULL/, default values \((0.4+0.9i)^k\) are used.
-- 
-- The polynomial is assumed to be squarefree. If there are repeated roots,
-- the iteration is likely to find them (with low numerical accuracy), but
-- the error bounds will not converge as the precision increases.
foreign import ccall "acb_poly.h acb_poly_find_roots"
  acb_poly_find_roots :: Ptr CAcb -> Ptr CAcbPoly -> Ptr CAcb -> CLong -> CLong -> IO CLong

foreign import ccall "acb_poly.h _acb_poly_validate_real_roots"
  _acb_poly_validate_real_roots :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO CInt

-- | /acb_poly_validate_real_roots/ /roots/ /poly/ /prec/ 
-- 
-- Given a strictly real polynomial /poly/ (of length /len/) and isolating
-- intervals for all its complex roots, determines if all the real roots
-- are separated from the non-real roots. If this function returns nonzero,
-- every root enclosure that touches the real axis (as tested by applying
-- @arb_contains_zero@ to the imaginary part) corresponds to a real root
-- (its imaginary part can be set to zero), and every other root enclosure
-- corresponds to a non-real root (with known sign for the imaginary part).
-- 
-- If this function returns zero, then the signs of the imaginary parts are
-- not known for certain, based on the accuracy of the inputs and the
-- working precision /prec/.
foreign import ccall "acb_poly.h acb_poly_validate_real_roots"
  acb_poly_validate_real_roots :: Ptr CAcb -> Ptr CAcbPoly -> CLong -> IO CInt

