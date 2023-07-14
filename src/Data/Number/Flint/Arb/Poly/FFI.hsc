{-|
module      :  Data.Number.Flint.Arb.Poly.FFI
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de
-}
module Data.Number.Flint.Arb.Poly.FFI (
  -- * Polynomials over the real numbers
    ArbPoly (..)
  , CArbPoly (..)
  , newArbPoly
  , newArbPolyFromFmpzPoly
  , newArbPolyFromFmpqPoly
  , withArbPoly
  , withNewArbPoly
  , withNewArbPolyFromFmpzPoly
  , withNewArbPolyFromFmpqPoly
  -- * Memory management
  , arb_poly_init
  , arb_poly_clear
  , arb_poly_fit_length
  , _arb_poly_set_length
  , _arb_poly_normalise
  , arb_poly_allocated_bytes
  -- * Basic manipulation
  , arb_poly_length
  , arb_poly_degree
  , arb_poly_is_zero
  , arb_poly_is_one
  , arb_poly_is_x
  , arb_poly_zero
  , arb_poly_one
  , arb_poly_set
  , arb_poly_set_round
  , arb_poly_set_trunc
  , arb_poly_set_trunc_round
  , arb_poly_set_coeff_si
  , arb_poly_set_coeff_arb
  , arb_poly_get_coeff_arb
  , _arb_poly_shift_right
  , arb_poly_shift_right
  , _arb_poly_shift_left
  , arb_poly_shift_left
  , arb_poly_truncate
  , arb_poly_valuation
  -- * Conversions
  , arb_poly_set_fmpz_poly
  , arb_poly_set_fmpq_poly
  , arb_poly_set_si
  -- * Input and output
  , arb_poly_get_strd
  , arb_poly_printd
  , arb_poly_fprintd
  -- * Random generation
  , arb_poly_randtest
  -- * Comparisons
  , arb_poly_contains
  , arb_poly_contains_fmpz_poly
  , arb_poly_contains_fmpq_poly
  , arb_poly_equal
  , _arb_poly_overlaps
  , arb_poly_overlaps
  , arb_poly_get_unique_fmpz_poly
  -- * Bounds
  , _arb_poly_majorant
  , arb_poly_majorant
  -- * Arithmetic
  , _arb_poly_add
  , arb_poly_add
  , arb_poly_add_si
  , _arb_poly_sub
  , arb_poly_sub
  , arb_poly_add_series
  , arb_poly_sub_series
  , arb_poly_neg
  , arb_poly_scalar_mul_2exp_si
  , arb_poly_scalar_mul
  , arb_poly_scalar_div
  , _arb_poly_mullow_classical
  , _arb_poly_mullow_block
  , _arb_poly_mullow
  , arb_poly_mullow_classical
  --, arb_poly_mullow_ztrunc
  , arb_poly_mullow_block
  , arb_poly_mullow
  , _arb_poly_mul
  , arb_poly_mul
  , _arb_poly_inv_series
  , arb_poly_inv_series
  , _arb_poly_div_series
  , arb_poly_div_series
  , _arb_poly_div
  , _arb_poly_rem
  , _arb_poly_divrem
  , arb_poly_divrem
  , _arb_poly_div_root
  -- * Composition
  , _arb_poly_taylor_shift
  , arb_poly_taylor_shift
  , _arb_poly_compose
  , arb_poly_compose
  , _arb_poly_compose_series
  , arb_poly_compose_series
  , _arb_poly_revert_series_lagrange
  , arb_poly_revert_series_lagrange
  , _arb_poly_revert_series_newton
  , arb_poly_revert_series_newton
  , _arb_poly_revert_series_lagrange_fast
  , arb_poly_revert_series_lagrange_fast
  , _arb_poly_revert_series
  , arb_poly_revert_series
  -- * Evaluation
  , _arb_poly_evaluate_horner
  , arb_poly_evaluate_horner
  , _arb_poly_evaluate_rectangular
  , arb_poly_evaluate_rectangular
  , _arb_poly_evaluate
  , arb_poly_evaluate
  , _arb_poly_evaluate_acb_horner
  , arb_poly_evaluate_acb_horner
  , _arb_poly_evaluate_acb_rectangular
  , arb_poly_evaluate_acb_rectangular
  , _arb_poly_evaluate_acb
  , arb_poly_evaluate_acb
  , _arb_poly_evaluate2_horner
  , arb_poly_evaluate2_horner
  , _arb_poly_evaluate2_rectangular
  , arb_poly_evaluate2_rectangular
  , _arb_poly_evaluate2
  , arb_poly_evaluate2
  , _arb_poly_evaluate2_acb_horner
  , arb_poly_evaluate2_acb_horner
  , _arb_poly_evaluate2_acb_rectangular
  , arb_poly_evaluate2_acb_rectangular
  , _arb_poly_evaluate2_acb
  , arb_poly_evaluate2_acb
  -- * Product trees
  , _arb_poly_product_roots
  , arb_poly_product_roots
  , _arb_poly_product_roots_complex
  , arb_poly_product_roots_complex
  , _arb_poly_tree_alloc
  , _arb_poly_tree_free
  , _arb_poly_tree_build
  -- * Multipoint evaluation
  , _arb_poly_evaluate_vec_iter
  , arb_poly_evaluate_vec_iter
  , _arb_poly_evaluate_vec_fast_precomp
  , _arb_poly_evaluate_vec_fast
  , arb_poly_evaluate_vec_fast
  -- * Interpolation
  , _arb_poly_interpolate_newton
  , arb_poly_interpolate_newton
  , _arb_poly_interpolate_barycentric
  , arb_poly_interpolate_barycentric
  , _arb_poly_interpolation_weights
  , _arb_poly_interpolate_fast_precomp
  , _arb_poly_interpolate_fast
  , arb_poly_interpolate_fast
  -- * Differentiation
  , _arb_poly_derivative
  , arb_poly_derivative
  , _arb_poly_nth_derivative
  , arb_poly_nth_derivative
  , _arb_poly_integral
  , arb_poly_integral
  -- * Transforms
  , _arb_poly_borel_transform
  , arb_poly_borel_transform
  , _arb_poly_inv_borel_transform
  , arb_poly_inv_borel_transform
  , _arb_poly_binomial_transform_basecase
  , arb_poly_binomial_transform_basecase
  , _arb_poly_binomial_transform_convolution
  , arb_poly_binomial_transform_convolution
  , _arb_poly_binomial_transform
  , arb_poly_binomial_transform
  , _arb_poly_graeffe_transform
  , arb_poly_graeffe_transform
  -- * Powers and elementary functions
  , _arb_poly_pow_ui_trunc_binexp
  , arb_poly_pow_ui_trunc_binexp
  , _arb_poly_pow_ui
  , arb_poly_pow_ui
  , _arb_poly_pow_series
  , arb_poly_pow_series
  , _arb_poly_pow_arb_series
  , arb_poly_pow_arb_series
  , _arb_poly_sqrt_series
  , arb_poly_sqrt_series
  , _arb_poly_rsqrt_series
  , arb_poly_rsqrt_series
  , _arb_poly_log_series
  , arb_poly_log_series
  , _arb_poly_log1p_series
  , arb_poly_log1p_series
  , _arb_poly_atan_series
  , arb_poly_atan_series
  , _arb_poly_asin_series
  , arb_poly_asin_series
  , _arb_poly_acos_series
  , arb_poly_acos_series
  , _arb_poly_exp_series_basecase
  , arb_poly_exp_series_basecase
  , _arb_poly_exp_series
  , arb_poly_exp_series
  , _arb_poly_sin_cos_series
  , arb_poly_sin_cos_series
  , _arb_poly_sin_series
  , arb_poly_sin_series
  , _arb_poly_cos_series
  , arb_poly_cos_series
  , _arb_poly_tan_series
  , arb_poly_tan_series
  , _arb_poly_sin_cos_pi_series
  , arb_poly_sin_cos_pi_series
  , _arb_poly_sin_pi_series
  , arb_poly_sin_pi_series
  , _arb_poly_cos_pi_series
  , arb_poly_cos_pi_series
  , _arb_poly_cot_pi_series
  , arb_poly_cot_pi_series
  , _arb_poly_sinh_cosh_series_basecase
  , arb_poly_sinh_cosh_series_basecase
  , _arb_poly_sinh_cosh_series_exponential
  , arb_poly_sinh_cosh_series_exponential
  , _arb_poly_sinh_cosh_series
  , arb_poly_sinh_cosh_series
  , _arb_poly_sinh_series
  , arb_poly_sinh_series
  , _arb_poly_cosh_series
  , arb_poly_cosh_series
  , _arb_poly_sinc_series
  , arb_poly_sinc_series
  , _arb_poly_sinc_pi_series
  , arb_poly_sinc_pi_series
  -- * Lambert W function
  , _arb_poly_lambertw_series
  , arb_poly_lambertw_series
  -- * Gamma function and factorials
  , _arb_poly_gamma_series
  , arb_poly_gamma_series
  , _arb_poly_rgamma_series
  , arb_poly_rgamma_series
  , _arb_poly_lgamma_series
  , arb_poly_lgamma_series
  , _arb_poly_digamma_series
  , arb_poly_digamma_series
  , _arb_poly_rising_ui_series
  , arb_poly_rising_ui_series
  -- * Zeta function
  , arb_poly_zeta_series
  , _arb_poly_riemann_siegel_theta_series
  , arb_poly_riemann_siegel_theta_series
  , _arb_poly_riemann_siegel_z_series
  , arb_poly_riemann_siegel_z_series
  -- * Root-finding
  , _arb_poly_root_bound_fujiwara
  , arb_poly_root_bound_fujiwara
  , _arb_poly_newton_convergence_factor
  , _arb_poly_newton_step
  , _arb_poly_newton_refine_root
  -- * Other special polynomials
  , _arb_poly_swinnerton_dyer_ui
  , arb_poly_swinnerton_dyer_ui
) where

-- Polynomials over the real numbers -------------------------------------------

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

-- arb_poly_t ------------------------------------------------------------------

-- | Createst a new `CArbPoly` structure encapsulated in `ArbPoly`.
{-# INLINE newArbPoly #-}
newArbPoly = do
  p <- mallocForeignPtr
  withForeignPtr p arb_poly_init
  addForeignPtrFinalizer p_arb_poly_clear p
  return $ ArbPoly p

newArbPolyFromFmpzPoly poly prec = do
  p <- mallocForeignPtr
  withForeignPtr p $ \p -> do
    arb_poly_init p
    withFmpzPoly poly $ \poly -> arb_poly_set_fmpz_poly p poly prec
  addForeignPtrFinalizer p_arb_poly_clear p
  return $ ArbPoly p

newArbPolyFromFmpqPoly poly prec = do 
  p <- mallocForeignPtr
  withForeignPtr p $ \p -> do
    arb_poly_init p
    withFmpqPoly poly $ \poly -> arb_poly_set_fmpq_poly p poly prec
  addForeignPtrFinalizer p_arb_poly_clear p
  return $ ArbPoly p

-- | Use `ArbPoly` in f.
{-# INLINE withArbPoly #-}
withArbPoly (ArbPoly p) f = do
  withForeignPtr p $ \fp -> f fp >>= return . (ArbPoly p,)

-- | Use new `ArbPoly` ptr in f.
{-# INLINE withNewArbPoly #-}
withNewArbPoly f = do
  p <- newArbPoly
  withArbPoly p f

withNewArbPolyFromFmpzPoly poly prec f = do
  p <- newArbPolyFromFmpzPoly poly prec
  withArbPoly p f

withNewArbPolyFromFmpqPoly poly prec f = do
  p <- newArbPolyFromFmpqPoly poly prec
  withArbPoly p f

instance Storable CArbPoly where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size arb_poly_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment arb_poly_t}
  peek = error "CArbPoly.peek: Not defined"
  poke = error "CArbPoly.poke: Not defined"

-- Memory management -----------------------------------------------------------

-- | /arb_poly_init/ /poly/ 
--
-- Initializes the polynomial for use, setting it to the zero polynomial.
foreign import ccall "arb_poly.h arb_poly_init"
  arb_poly_init :: Ptr CArbPoly -> IO ()

-- | /arb_poly_clear/ /poly/ 
--
-- Clears the polynomial, deallocating all coefficients and the coefficient
-- array.
foreign import ccall "arb_poly.h arb_poly_clear"
  arb_poly_clear :: Ptr CArbPoly -> IO ()

foreign import ccall "arb_poly.h &arb_poly_clear"
  p_arb_poly_clear :: FunPtr (Ptr CArbPoly -> IO ())

-- | /arb_poly_fit_length/ /poly/ /len/ 
--
-- Makes sure that the coefficient array of the polynomial contains at
-- least /len/ initialized coefficients.
foreign import ccall "arb_poly.h arb_poly_fit_length"
  arb_poly_fit_length :: Ptr CArbPoly -> CLong -> IO ()

-- | /_arb_poly_set_length/ /poly/ /len/ 
--
-- Directly changes the length of the polynomial, without allocating or
-- deallocating coefficients. The value should not exceed the allocation
-- length.
foreign import ccall "arb_poly.h _arb_poly_set_length"
  _arb_poly_set_length :: Ptr CArbPoly -> CLong -> IO ()

-- | /_arb_poly_normalise/ /poly/ 
--
-- Strips any trailing coefficients which are identical to zero.
foreign import ccall "arb_poly.h _arb_poly_normalise"
  _arb_poly_normalise :: Ptr CArbPoly -> IO ()

-- | /arb_poly_allocated_bytes/ /x/ 
--
-- Returns the total number of bytes heap-allocated internally by this
-- object. The count excludes the size of the structure itself. Add
-- @sizeof(arb_poly_struct)@ to get the size of the object as a whole.
foreign import ccall "arb_poly.h arb_poly_allocated_bytes"
  arb_poly_allocated_bytes :: Ptr CArbPoly -> IO CLong

-- Basic manipulation ----------------------------------------------------------

-- | /arb_poly_length/ /poly/ 
--
-- Returns the length of /poly/, i.e. zero if /poly/ is identically zero,
-- and otherwise one more than the index of the highest term that is not
-- identically zero.
foreign import ccall "arb_poly.h arb_poly_length"
  arb_poly_length :: Ptr CArbPoly -> IO CLong

-- | /arb_poly_degree/ /poly/ 
--
-- Returns the degree of /poly/, defined as one less than its length. Note
-- that if one or several leading coefficients are balls containing zero,
-- this value can be larger than the true degree of the exact polynomial
-- represented by /poly/, so the return value of this function is
-- effectively an upper bound.
foreign import ccall "arb_poly.h arb_poly_degree"
  arb_poly_degree :: Ptr CArbPoly -> IO CLong

-- | /arb_poly_is_zero/ /poly/ 
--
foreign import ccall "arb_poly.h arb_poly_is_zero"
  arb_poly_is_zero :: Ptr CArbPoly -> IO CInt

-- | /arb_poly_is_one/ /poly/ 
--
foreign import ccall "arb_poly.h arb_poly_is_one"
  arb_poly_is_one :: Ptr CArbPoly -> IO CInt

-- | /arb_poly_is_x/ /poly/ 
--
-- Returns 1 if /poly/ is exactly the polynomial 0, 1 or /x/ respectively.
-- Returns 0 otherwise.
foreign import ccall "arb_poly.h arb_poly_is_x"
  arb_poly_is_x :: Ptr CArbPoly -> IO CInt

-- | /arb_poly_zero/ /poly/ 
--
foreign import ccall "arb_poly.h arb_poly_zero"
  arb_poly_zero :: Ptr CArbPoly -> IO ()

-- | /arb_poly_one/ /poly/ 
--
-- Sets /poly/ to the constant 0 respectively 1.
foreign import ccall "arb_poly.h arb_poly_one"
  arb_poly_one :: Ptr CArbPoly -> IO ()

-- | /arb_poly_set/ /dest/ /src/ 
--
-- Sets /dest/ to a copy of /src/.
foreign import ccall "arb_poly.h arb_poly_set"
  arb_poly_set :: Ptr CArbPoly -> Ptr CArbPoly -> IO ()

-- | /arb_poly_set_round/ /dest/ /src/ /prec/ 
--
-- Sets /dest/ to a copy of /src/, rounded to /prec/ bits.
foreign import ccall "arb_poly.h arb_poly_set_round"
  arb_poly_set_round :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> IO ()

-- | /arb_poly_set_trunc/ /dest/ /src/ /n/ 
--
foreign import ccall "arb_poly.h arb_poly_set_trunc"
  arb_poly_set_trunc :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> IO ()

-- | /arb_poly_set_trunc_round/ /dest/ /src/ /n/ /prec/ 
--
-- Sets /dest/ to a copy of /src/, truncated to length /n/ and rounded to
-- /prec/ bits.
foreign import ccall "arb_poly.h arb_poly_set_trunc_round"
  arb_poly_set_trunc_round :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /arb_poly_set_coeff_si/ /poly/ /n/ /c/ 
--
foreign import ccall "arb_poly.h arb_poly_set_coeff_si"
  arb_poly_set_coeff_si :: Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /arb_poly_set_coeff_arb/ /poly/ /n/ /c/ 
--
-- Sets the coefficient with index /n/ in /poly/ to the value /c/. We
-- require that /n/ is nonnegative.
foreign import ccall "arb_poly.h arb_poly_set_coeff_arb"
  arb_poly_set_coeff_arb :: Ptr CArbPoly -> CLong -> Ptr CArb -> IO ()

-- | /arb_poly_get_coeff_arb/ /v/ /poly/ /n/ 
--
-- Sets /v/ to the value of the coefficient with index /n/ in /poly/. We
-- require that /n/ is nonnegative.
foreign import ccall "arb_poly.h arb_poly_get_coeff_arb"
  arb_poly_get_coeff_arb :: Ptr CArb -> Ptr CArbPoly -> CLong -> IO ()

-- | /_arb_poly_shift_right/ /res/ /poly/ /len/ /n/ 
--
foreign import ccall "arb_poly.h _arb_poly_shift_right"
  _arb_poly_shift_right :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /arb_poly_shift_right/ /res/ /poly/ /n/ 
--
-- Sets /res/ to /poly/ divided by \(x^n\), throwing away the lower
-- coefficients. We require that /n/ is nonnegative.
foreign import ccall "arb_poly.h arb_poly_shift_right"
  arb_poly_shift_right :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> IO ()

-- | /_arb_poly_shift_left/ /res/ /poly/ /len/ /n/ 
--
foreign import ccall "arb_poly.h _arb_poly_shift_left"
  _arb_poly_shift_left :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /arb_poly_shift_left/ /res/ /poly/ /n/ 
--
-- Sets /res/ to /poly/ multiplied by \(x^n\). We require that /n/ is
-- nonnegative.
foreign import ccall "arb_poly.h arb_poly_shift_left"
  arb_poly_shift_left :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> IO ()

-- | /arb_poly_truncate/ /poly/ /n/ 
--
-- Truncates /poly/ to have length at most /n/, i.e. degree strictly
-- smaller than /n/. We require that /n/ is nonnegative.
foreign import ccall "arb_poly.h arb_poly_truncate"
  arb_poly_truncate :: Ptr CArbPoly -> CLong -> IO ()

-- | /arb_poly_valuation/ /poly/ 
--
-- Returns the degree of the lowest term that is not exactly zero in
-- /poly/. Returns -1 if /poly/ is the zero polynomial.
foreign import ccall "arb_poly.h arb_poly_valuation"
  arb_poly_valuation :: Ptr CArbPoly -> IO CLong

-- Conversions -----------------------------------------------------------------

-- | /arb_poly_set_fmpz_poly/ /poly/ /src/ /prec/ 
--
foreign import ccall "arb_poly.h arb_poly_set_fmpz_poly"
  arb_poly_set_fmpz_poly :: Ptr CArbPoly -> Ptr CFmpzPoly -> CLong -> IO ()

-- | /arb_poly_set_fmpq_poly/ /poly/ /src/ /prec/ 
--
foreign import ccall "arb_poly.h arb_poly_set_fmpq_poly"
  arb_poly_set_fmpq_poly :: Ptr CArbPoly -> Ptr CFmpqPoly -> CLong -> IO ()

-- | /arb_poly_set_si/ /poly/ /src/ 
--
-- Sets /poly/ to /src/, rounding the coefficients to /prec/ bits.
foreign import ccall "arb_poly.h arb_poly_set_si"
  arb_poly_set_si :: Ptr CArbPoly -> CLong -> IO ()

-- Input and output ------------------------------------------------------------

foreign import ccall "arb_poly.h arb_poly_get_strd"
  arb_poly_get_strd :: Ptr CArbPoly -> CLong -> IO CString

-- | /arb_poly_printd/ /poly/ /digits/ 
--
-- Prints the polynomial as an array of coefficients, printing each
-- coefficient using /arb_printd/.
arb_poly_printd :: Ptr CArbPoly -> CLong -> IO ()
arb_poly_printd poly digits = do
  printCStr (flip arb_poly_get_strd digits) poly
  return ()
  
-- | /arb_poly_fprintd/ /file/ /poly/ /digits/ 
--
-- Prints the polynomial as an array of coefficients to the stream /file/,
-- printing each coefficient using /arb_fprintd/.
foreign import ccall "arb_poly.h arb_poly_fprintd"
  arb_poly_fprintd :: Ptr CFile -> Ptr CArbPoly -> CLong -> IO ()

-- Random generation -----------------------------------------------------------

-- | /arb_poly_randtest/ /poly/ /state/ /len/ /prec/ /mag_bits/ 
--
-- Creates a random polynomial with length at most /len/.
foreign import ccall "arb_poly.h arb_poly_randtest"
  arb_poly_randtest :: Ptr CArbPoly -> Ptr CFRandState -> CLong -> CLong -> CLong -> IO ()

-- Comparisons -----------------------------------------------------------------

-- | /arb_poly_contains/ /poly1/ /poly2/ 
--
foreign import ccall "arb_poly.h arb_poly_contains"
  arb_poly_contains :: Ptr CArbPoly -> Ptr CArbPoly -> IO CInt

-- | /arb_poly_contains_fmpz_poly/ /poly1/ /poly2/ 
--
foreign import ccall "arb_poly.h arb_poly_contains_fmpz_poly"
  arb_poly_contains_fmpz_poly :: Ptr CArbPoly -> Ptr CFmpzPoly -> IO CInt

-- | /arb_poly_contains_fmpq_poly/ /poly1/ /poly2/ 
--
-- Returns nonzero iff /poly1/ contains /poly2/.
foreign import ccall "arb_poly.h arb_poly_contains_fmpq_poly"
  arb_poly_contains_fmpq_poly :: Ptr CArbPoly -> Ptr CFmpqPoly -> IO CInt

-- | /arb_poly_equal/ /A/ /B/ 
--
-- Returns nonzero iff /A/ and /B/ are equal as polynomial balls, i.e. all
-- coefficients have equal midpoint and radius.
foreign import ccall "arb_poly.h arb_poly_equal"
  arb_poly_equal :: Ptr CArbPoly -> Ptr CArbPoly -> IO CInt

-- | /_arb_poly_overlaps/ /poly1/ /len1/ /poly2/ /len2/ 
--
foreign import ccall "arb_poly.h _arb_poly_overlaps"
  _arb_poly_overlaps :: Ptr CArb -> CLong -> Ptr CArb -> CLong -> IO CInt

-- | /arb_poly_overlaps/ /poly1/ /poly2/ 
--
-- Returns nonzero iff /poly1/ overlaps with /poly2/. The underscore
-- function requires that /len1/ ist at least as large as /len2/.
foreign import ccall "arb_poly.h arb_poly_overlaps"
  arb_poly_overlaps :: Ptr CArbPoly -> Ptr CArbPoly -> IO CInt

-- | /arb_poly_get_unique_fmpz_poly/ /z/ /x/ 
--
-- If /x/ contains a unique integer polynomial, sets /z/ to that value and
-- returns nonzero. Otherwise (if /x/ represents no integers or more than
-- one integer), returns zero, possibly partially modifying /z/.
foreign import ccall "arb_poly.h arb_poly_get_unique_fmpz_poly"
  arb_poly_get_unique_fmpz_poly :: Ptr CFmpzPoly -> Ptr CArbPoly -> IO CInt

-- Bounds ----------------------------------------------------------------------

-- | /_arb_poly_majorant/ /res/ /poly/ /len/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_majorant"
  _arb_poly_majorant :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /arb_poly_majorant/ /res/ /poly/ /prec/ 
--
-- Sets /res/ to an exact real polynomial whose coefficients are upper
-- bounds for the absolute values of the coefficients in /poly/, rounded to
-- /prec/ bits.
foreign import ccall "arb_poly.h arb_poly_majorant"
  arb_poly_majorant :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> IO ()

-- Arithmetic ------------------------------------------------------------------

-- | /_arb_poly_add/ /C/ /A/ /lenA/ /B/ /lenB/ /prec/ 
--
-- Sets /{C, max(lenA, lenB)}/ to the sum of /{A, lenA}/ and /{B, lenB}/.
-- Allows aliasing of the input and output operands.
foreign import ccall "arb_poly.h _arb_poly_add"
  _arb_poly_add :: Ptr CArb -> Ptr CArb -> CLong -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /arb_poly_add/ /C/ /A/ /B/ /prec/ 
--
foreign import ccall "arb_poly.h arb_poly_add"
  arb_poly_add :: Ptr CArbPoly -> Ptr CArbPoly -> Ptr CArbPoly -> CLong -> IO ()

-- | /arb_poly_add_si/ /C/ /A/ /B/ /prec/ 
--
-- Sets /C/ to the sum of /A/ and /B/.
foreign import ccall "arb_poly.h arb_poly_add_si"
  arb_poly_add_si :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_poly_sub/ /C/ /A/ /lenA/ /B/ /lenB/ /prec/ 
--
-- Sets /{C, max(lenA, lenB)}/ to the difference of /{A, lenA}/ and /{B,
-- lenB}/. Allows aliasing of the input and output operands.
foreign import ccall "arb_poly.h _arb_poly_sub"
  _arb_poly_sub :: Ptr CArb -> Ptr CArb -> CLong -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /arb_poly_sub/ /C/ /A/ /B/ /prec/ 
--
-- Sets /C/ to the difference of /A/ and /B/.
foreign import ccall "arb_poly.h arb_poly_sub"
  arb_poly_sub :: Ptr CArbPoly -> Ptr CArbPoly -> Ptr CArbPoly -> CLong -> IO ()

-- | /arb_poly_add_series/ /C/ /A/ /B/ /len/ /prec/ 
--
-- Sets /C/ to the sum of /A/ and /B/, truncated to length /len/.
foreign import ccall "arb_poly.h arb_poly_add_series"
  arb_poly_add_series :: Ptr CArbPoly -> Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /arb_poly_sub_series/ /C/ /A/ /B/ /len/ /prec/ 
--
-- Sets /C/ to the difference of /A/ and /B/, truncated to length /len/.
foreign import ccall "arb_poly.h arb_poly_sub_series"
  arb_poly_sub_series :: Ptr CArbPoly -> Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /arb_poly_neg/ /C/ /A/ 
--
-- Sets /C/ to the negation of /A/.
foreign import ccall "arb_poly.h arb_poly_neg"
  arb_poly_neg :: Ptr CArbPoly -> Ptr CArbPoly -> IO ()

-- | /arb_poly_scalar_mul_2exp_si/ /C/ /A/ /c/ 
--
-- Sets /C/ to /A/ multiplied by \(2^c\).
foreign import ccall "arb_poly.h arb_poly_scalar_mul_2exp_si"
  arb_poly_scalar_mul_2exp_si :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> IO ()

-- | /arb_poly_scalar_mul/ /C/ /A/ /c/ /prec/ 
--
-- Sets /C/ to /A/ multiplied by /c/.
foreign import ccall "arb_poly.h arb_poly_scalar_mul"
  arb_poly_scalar_mul :: Ptr CArbPoly -> Ptr CArbPoly -> Ptr CArb -> CLong -> IO ()

-- | /arb_poly_scalar_div/ /C/ /A/ /c/ /prec/ 
--
-- Sets /C/ to /A/ divided by /c/.
foreign import ccall "arb_poly.h arb_poly_scalar_div"
  arb_poly_scalar_div :: Ptr CArbPoly -> Ptr CArbPoly -> Ptr CArb -> CLong -> IO ()

-- | /_arb_poly_mullow_classical/ /C/ /A/ /lenA/ /B/ /lenB/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_mullow_classical"
  _arb_poly_mullow_classical :: Ptr CArb -> Ptr CArb -> CLong -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /_arb_poly_mullow_block/ /C/ /A/ /lenA/ /B/ /lenB/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_mullow_block"
  _arb_poly_mullow_block :: Ptr CArb -> Ptr CArb -> CLong -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /_arb_poly_mullow/ /C/ /A/ /lenA/ /B/ /lenB/ /n/ /prec/ 
--
-- Sets /{C, n}/ to the product of /{A, lenA}/ and /{B, lenB}/, truncated
-- to length /n/. The output is not allowed to be aliased with either of
-- the inputs. We require \(\mathrm{lenA} \ge \mathrm{lenB} > 0\),
-- \(n > 0\), \(\mathrm{lenA} + \mathrm{lenB} - 1 \ge n\).
-- 
-- The /classical/ version uses a plain loop. This has good numerical
-- stability but gets slow for large /n/.
-- 
-- The /block/ version decomposes the product into several subproducts
-- which are computed exactly over the integers.
-- 
-- It first attempts to find an integer \(c\) such that \(A(2^c x)\) and
-- \(B(2^c x)\) have slowly varying coefficients, to reduce the number of
-- blocks.
-- 
-- The scaling factor \(c\) is chosen in a quick, heuristic way by picking
-- the first and last nonzero terms in each polynomial. If the indices in
-- \(A\) are \(a_2, a_1\) and the log-2 magnitudes are \(e_2, e_1\), and
-- the indices in \(B\) are \(b_2, b_1\) with corresponding magnitudes
-- \(f_2, f_1\), then we compute \(c\) as the weighted arithmetic mean of
-- the slopes, rounded to the nearest integer:
-- 
-- \[`\]
-- \[c = \left\lfloor
--     \frac{(e_2 - e_1) + (f_2 + f_1)}{(a_2 - a_1) + (b_2 - b_1)}
--     + \frac{1}{2}
--     \right \rfloor.\]
-- 
-- This strategy is used because it is simple. It is not optimal in all
-- cases, but will typically give good performance when multiplying two
-- power series with a similar decay rate.
-- 
-- The default algorithm chooses the /classical/ algorithm for short
-- polynomials and the /block/ algorithm for long polynomials.
-- 
-- If the input pointers are identical (and the lengths are the same), they
-- are assumed to represent the same polynomial, and its square is
-- computed.
foreign import ccall "arb_poly.h _arb_poly_mullow"
  _arb_poly_mullow :: Ptr CArb -> Ptr CArb -> CLong -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_poly_mullow_classical/ /C/ /A/ /B/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h arb_poly_mullow_classical"
  arb_poly_mullow_classical :: Ptr CArbPoly -> Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- -- | /arb_poly_mullow_ztrunc/ /C/ /A/ /B/ /n/ /prec/ 
-- --
-- foreign import ccall "arb_poly.h arb_poly_mullow_ztrunc"
--   arb_poly_mullow_ztrunc :: Ptr CArbPoly -> Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /arb_poly_mullow_block/ /C/ /A/ /B/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h arb_poly_mullow_block"
  arb_poly_mullow_block :: Ptr CArbPoly -> Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /arb_poly_mullow/ /C/ /A/ /B/ /n/ /prec/ 
--
-- Sets /C/ to the product of /A/ and /B/, truncated to length /n/. If the
-- same variable is passed for /A/ and /B/, sets /C/ to the square of /A/
-- truncated to length /n/.
foreign import ccall "arb_poly.h arb_poly_mullow"
  arb_poly_mullow :: Ptr CArbPoly -> Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_poly_mul/ /C/ /A/ /lenA/ /B/ /lenB/ /prec/ 
--
-- Sets /{C, lenA + lenB - 1}/ to the product of /{A, lenA}/ and /{B,
-- lenB}/. The output is not allowed to be aliased with either of the
-- inputs. We require \(\mathrm{lenA} \ge \mathrm{lenB} > 0\). This
-- function is implemented as a simple wrapper for @_arb_poly_mullow@.
-- 
-- If the input pointers are identical (and the lengths are the same), they
-- are assumed to represent the same polynomial, and its square is
-- computed.
foreign import ccall "arb_poly.h _arb_poly_mul"
  _arb_poly_mul :: Ptr CArb -> Ptr CArb -> CLong -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /arb_poly_mul/ /C/ /A/ /B/ /prec/ 
--
-- Sets /C/ to the product of /A/ and /B/. If the same variable is passed
-- for /A/ and /B/, sets /C/ to the square of /A/.
foreign import ccall "arb_poly.h arb_poly_mul"
  arb_poly_mul :: Ptr CArbPoly -> Ptr CArbPoly -> Ptr CArbPoly -> CLong -> IO ()

-- | /_arb_poly_inv_series/ /Q/ /A/ /Alen/ /len/ /prec/ 
--
-- Sets /{Q, len}/ to the power series inverse of /{A, Alen}/. Uses Newton
-- iteration.
foreign import ccall "arb_poly.h _arb_poly_inv_series"
  _arb_poly_inv_series :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_poly_inv_series/ /Q/ /A/ /n/ /prec/ 
--
-- Sets /Q/ to the power series inverse of /A/, truncated to length /n/.
foreign import ccall "arb_poly.h arb_poly_inv_series"
  arb_poly_inv_series :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_poly_div_series/ /Q/ /A/ /Alen/ /B/ /Blen/ /n/ /prec/ 
--
-- Sets /{Q, n}/ to the power series quotient of /{A, Alen}/ by /{B,
-- Blen}/. Uses Newton iteration followed by multiplication.
foreign import ccall "arb_poly.h _arb_poly_div_series"
  _arb_poly_div_series :: Ptr CArb -> Ptr CArb -> CLong -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_poly_div_series/ /Q/ /A/ /B/ /n/ /prec/ 
--
-- Sets /Q/ to the power series quotient /A/ divided by /B/, truncated to
-- length /n/.
foreign import ccall "arb_poly.h arb_poly_div_series"
  arb_poly_div_series :: Ptr CArbPoly -> Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_poly_div/ /Q/ /A/ /lenA/ /B/ /lenB/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_div"
  _arb_poly_div :: Ptr CArb -> Ptr CArb -> CLong -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /_arb_poly_rem/ /R/ /A/ /lenA/ /B/ /lenB/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_rem"
  _arb_poly_rem :: Ptr CArb -> Ptr CArb -> CLong -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /_arb_poly_divrem/ /Q/ /R/ /A/ /lenA/ /B/ /lenB/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_divrem"
  _arb_poly_divrem :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /arb_poly_divrem/ /Q/ /R/ /A/ /B/ /prec/ 
--
-- Performs polynomial division with remainder, computing a quotient \(Q\)
-- and a remainder \(R\) such that \(A = BQ + R\). The implementation
-- reverses the inputs and performs power series division.
-- 
-- If the leading coefficient of \(B\) contains zero (or if \(B\) is
-- identically zero), returns 0 indicating failure without modifying the
-- outputs. Otherwise returns nonzero.
foreign import ccall "arb_poly.h arb_poly_divrem"
  arb_poly_divrem :: Ptr CArbPoly -> Ptr CArbPoly -> Ptr CArbPoly -> Ptr CArbPoly -> CLong -> IO CInt

-- | /_arb_poly_div_root/ /Q/ /R/ /A/ /len/ /c/ /prec/ 
--
-- Divides \(A\) by the polynomial \(x - c\), computing the quotient \(Q\)
-- as well as the remainder \(R = f(c)\).
foreign import ccall "arb_poly.h _arb_poly_div_root"
  _arb_poly_div_root :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> Ptr CArb -> CLong -> IO ()

-- Composition -----------------------------------------------------------------

-- | /_arb_poly_taylor_shift/ /g/ /c/ /n/ /prec/ 
foreign import ccall "arb_poly.h _arb_poly_taylor_shift"
  _arb_poly_taylor_shift :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> IO ()
-- | /arb_poly_taylor_shift/ /g/ /f/ /c/ /prec/ 
--
-- Sets /g/ to the Taylor shift \(f(x+c)\). The underscore methods act
-- in-place on /g/ = /f/ which has length /n/.
foreign import ccall "arb_poly.h arb_poly_taylor_shift"
  arb_poly_taylor_shift :: Ptr CArbPoly -> Ptr CArbPoly -> Ptr CArb -> CLong -> IO ()

-- | /_arb_poly_compose/ /res/ /poly1/ /len1/ /poly2/ /len2/ /prec/ 
foreign import ccall "arb_poly.h _arb_poly_compose"
  _arb_poly_compose :: Ptr CArb -> Ptr CArb -> CLong -> Ptr CArb -> CLong -> CLong -> IO ()
-- | /arb_poly_compose/ /res/ /poly1/ /poly2/ /prec/ 
--
-- Sets /res/ to the composition \(h(x) = f(g(x))\) where \(f\) is given by
-- /poly1/ and \(g\) is given by /poly2/. The underscore method does not
-- support aliasing of the output with either input polynomial.
foreign import ccall "arb_poly.h arb_poly_compose"
  arb_poly_compose :: Ptr CArbPoly -> Ptr CArbPoly -> Ptr CArbPoly -> CLong -> IO ()

-- | /_arb_poly_compose_series/ /res/ /poly1/ /len1/ /poly2/ /len2/ /n/ /prec/ 
foreign import ccall "arb_poly.h _arb_poly_compose_series"
  _arb_poly_compose_series :: Ptr CArb -> Ptr CArb -> CLong -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()
-- | /arb_poly_compose_series/ /res/ /poly1/ /poly2/ /n/ /prec/ 
--
-- Sets /res/ to the power series composition \(h(x) = f(g(x))\) truncated
-- to order \(O(x^n)\) where \(f\) is given by /poly1/ and \(g\) is given
-- by /poly2/. Wraps @_gr_poly_compose_series@ which chooses automatically
-- between various algorithms.
-- 
-- We require that the constant term in \(g(x)\) is exactly zero. The
-- underscore method does not support aliasing of the output with either
-- input polynomial.
foreign import ccall "arb_poly.h arb_poly_compose_series"
  arb_poly_compose_series :: Ptr CArbPoly -> Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_poly_revert_series_lagrange/ /h/ /f/ /flen/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_revert_series_lagrange"
  _arb_poly_revert_series_lagrange :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_poly_revert_series_lagrange/ /h/ /f/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h arb_poly_revert_series_lagrange"
  arb_poly_revert_series_lagrange :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_poly_revert_series_newton/ /h/ /f/ /flen/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_revert_series_newton"
  _arb_poly_revert_series_newton :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_poly_revert_series_newton/ /h/ /f/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h arb_poly_revert_series_newton"
  arb_poly_revert_series_newton :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_poly_revert_series_lagrange_fast/ /h/ /f/ /flen/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_revert_series_lagrange_fast"
  _arb_poly_revert_series_lagrange_fast :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_poly_revert_series_lagrange_fast/ /h/ /f/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h arb_poly_revert_series_lagrange_fast"
  arb_poly_revert_series_lagrange_fast :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_poly_revert_series/ /h/ /f/ /flen/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_revert_series"
  _arb_poly_revert_series :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_poly_revert_series/ /h/ /f/ /n/ /prec/ 
--
-- Sets \(h\) to the power series reversion of \(f\), i.e. the expansion of
-- the compositional inverse function \(f^{-1}(x)\), truncated to order
-- \(O(x^n)\), using respectively Lagrange inversion, Newton iteration,
-- fast Lagrange inversion, and a default algorithm choice.
-- 
-- We require that the constant term in \(f\) is exactly zero and that the
-- linear term is nonzero. The underscore methods assume that /flen/ is at
-- least 2, and do not support aliasing.
foreign import ccall "arb_poly.h arb_poly_revert_series"
  arb_poly_revert_series :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- Evaluation ------------------------------------------------------------------

-- | /_arb_poly_evaluate_horner/ /y/ /f/ /len/ /x/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_evaluate_horner"
  _arb_poly_evaluate_horner :: Ptr CArb -> Ptr CArb -> CLong -> Ptr CArb -> CLong -> IO ()

-- | /arb_poly_evaluate_horner/ /y/ /f/ /x/ /prec/ 
--
foreign import ccall "arb_poly.h arb_poly_evaluate_horner"
  arb_poly_evaluate_horner :: Ptr CArb -> Ptr CArbPoly -> Ptr CArb -> CLong -> IO ()

-- | /_arb_poly_evaluate_rectangular/ /y/ /f/ /len/ /x/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_evaluate_rectangular"
  _arb_poly_evaluate_rectangular :: Ptr CArb -> Ptr CArb -> CLong -> Ptr CArb -> CLong -> IO ()

-- | /arb_poly_evaluate_rectangular/ /y/ /f/ /x/ /prec/ 
--
foreign import ccall "arb_poly.h arb_poly_evaluate_rectangular"
  arb_poly_evaluate_rectangular :: Ptr CArb -> Ptr CArbPoly -> Ptr CArb -> CLong -> IO ()

-- | /_arb_poly_evaluate/ /y/ /f/ /len/ /x/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_evaluate"
  _arb_poly_evaluate :: Ptr CArb -> Ptr CArb -> CLong -> Ptr CArb -> CLong -> IO ()

-- | /arb_poly_evaluate/ /y/ /f/ /x/ /prec/ 
--
-- Sets \(y = f(x)\), evaluated respectively using Horner\'s rule,
-- rectangular splitting, and an automatic algorithm choice.
foreign import ccall "arb_poly.h arb_poly_evaluate"
  arb_poly_evaluate :: Ptr CArb -> Ptr CArbPoly -> Ptr CArb -> CLong -> IO ()

-- | /_arb_poly_evaluate_acb_horner/ /y/ /f/ /len/ /x/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_evaluate_acb_horner"
  _arb_poly_evaluate_acb_horner :: Ptr CAcb -> Ptr CArb -> CLong -> Ptr CAcb -> CLong -> IO ()

-- | /arb_poly_evaluate_acb_horner/ /y/ /f/ /x/ /prec/ 
--
foreign import ccall "arb_poly.h arb_poly_evaluate_acb_horner"
  arb_poly_evaluate_acb_horner :: Ptr CAcb -> Ptr CArbPoly -> Ptr CAcb -> CLong -> IO ()

-- | /_arb_poly_evaluate_acb_rectangular/ /y/ /f/ /len/ /x/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_evaluate_acb_rectangular"
  _arb_poly_evaluate_acb_rectangular :: Ptr CAcb -> Ptr CArb -> CLong -> Ptr CAcb -> CLong -> IO ()

-- | /arb_poly_evaluate_acb_rectangular/ /y/ /f/ /x/ /prec/ 
--
foreign import ccall "arb_poly.h arb_poly_evaluate_acb_rectangular"
  arb_poly_evaluate_acb_rectangular :: Ptr CAcb -> Ptr CArbPoly -> Ptr CAcb -> CLong -> IO ()

-- | /_arb_poly_evaluate_acb/ /y/ /f/ /len/ /x/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_evaluate_acb"
  _arb_poly_evaluate_acb :: Ptr CAcb -> Ptr CArb -> CLong -> Ptr CAcb -> CLong -> IO ()

-- | /arb_poly_evaluate_acb/ /y/ /f/ /x/ /prec/ 
--
-- Sets \(y = f(x)\) where \(x\) is a complex number, evaluating the
-- polynomial respectively using Horner\'s rule, rectangular splitting, and
-- an automatic algorithm choice.
foreign import ccall "arb_poly.h arb_poly_evaluate_acb"
  arb_poly_evaluate_acb :: Ptr CAcb -> Ptr CArbPoly -> Ptr CAcb -> CLong -> IO ()

-- | /_arb_poly_evaluate2_horner/ /y/ /z/ /f/ /len/ /x/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_evaluate2_horner"
  _arb_poly_evaluate2_horner :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> Ptr CArb -> CLong -> IO ()

-- | /arb_poly_evaluate2_horner/ /y/ /z/ /f/ /x/ /prec/ 
--
foreign import ccall "arb_poly.h arb_poly_evaluate2_horner"
  arb_poly_evaluate2_horner :: Ptr CArb -> Ptr CArb -> Ptr CArbPoly -> Ptr CArb -> CLong -> IO ()

-- | /_arb_poly_evaluate2_rectangular/ /y/ /z/ /f/ /len/ /x/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_evaluate2_rectangular"
  _arb_poly_evaluate2_rectangular :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> Ptr CArb -> CLong -> IO ()

-- | /arb_poly_evaluate2_rectangular/ /y/ /z/ /f/ /x/ /prec/ 
--
foreign import ccall "arb_poly.h arb_poly_evaluate2_rectangular"
  arb_poly_evaluate2_rectangular :: Ptr CArb -> Ptr CArb -> Ptr CArbPoly -> Ptr CArb -> CLong -> IO ()

-- | /_arb_poly_evaluate2/ /y/ /z/ /f/ /len/ /x/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_evaluate2"
  _arb_poly_evaluate2 :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> Ptr CArb -> CLong -> IO ()

-- | /arb_poly_evaluate2/ /y/ /z/ /f/ /x/ /prec/ 
--
-- Sets \(y = f(x), z = f'(x)\), evaluated respectively using Horner\'s
-- rule, rectangular splitting, and an automatic algorithm choice.
-- 
-- When Horner\'s rule is used, the only advantage of evaluating the
-- function and its derivative simultaneously is that one does not have to
-- generate the derivative polynomial explicitly. With the rectangular
-- splitting algorithm, the powers can be reused, making simultaneous
-- evaluation slightly faster.
foreign import ccall "arb_poly.h arb_poly_evaluate2"
  arb_poly_evaluate2 :: Ptr CArb -> Ptr CArb -> Ptr CArbPoly -> Ptr CArb -> CLong -> IO ()

-- | /_arb_poly_evaluate2_acb_horner/ /y/ /z/ /f/ /len/ /x/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_evaluate2_acb_horner"
  _arb_poly_evaluate2_acb_horner :: Ptr CAcb -> Ptr CAcb -> Ptr CArb -> CLong -> Ptr CAcb -> CLong -> IO ()

-- | /arb_poly_evaluate2_acb_horner/ /y/ /z/ /f/ /x/ /prec/ 
--
foreign import ccall "arb_poly.h arb_poly_evaluate2_acb_horner"
  arb_poly_evaluate2_acb_horner :: Ptr CAcb -> Ptr CAcb -> Ptr CArbPoly -> Ptr CAcb -> CLong -> IO ()

-- | /_arb_poly_evaluate2_acb_rectangular/ /y/ /z/ /f/ /len/ /x/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_evaluate2_acb_rectangular"
  _arb_poly_evaluate2_acb_rectangular :: Ptr CAcb -> Ptr CAcb -> Ptr CArb -> CLong -> Ptr CAcb -> CLong -> IO ()

-- | /arb_poly_evaluate2_acb_rectangular/ /y/ /z/ /f/ /x/ /prec/ 
--
foreign import ccall "arb_poly.h arb_poly_evaluate2_acb_rectangular"
  arb_poly_evaluate2_acb_rectangular :: Ptr CAcb -> Ptr CAcb -> Ptr CArbPoly -> Ptr CAcb -> CLong -> IO ()

-- | /_arb_poly_evaluate2_acb/ /y/ /z/ /f/ /len/ /x/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_evaluate2_acb"
  _arb_poly_evaluate2_acb :: Ptr CAcb -> Ptr CAcb -> Ptr CArb -> CLong -> Ptr CAcb -> CLong -> IO ()

-- | /arb_poly_evaluate2_acb/ /y/ /z/ /f/ /x/ /prec/ 
--
-- Sets \(y = f(x), z = f'(x)\), evaluated respectively using Horner\'s
-- rule, rectangular splitting, and an automatic algorithm choice.
foreign import ccall "arb_poly.h arb_poly_evaluate2_acb"
  arb_poly_evaluate2_acb :: Ptr CAcb -> Ptr CAcb -> Ptr CArbPoly -> Ptr CAcb -> CLong -> IO ()

-- Product trees ---------------------------------------------------------------

-- | /_arb_poly_product_roots/ /poly/ /xs/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_product_roots"
  _arb_poly_product_roots :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /arb_poly_product_roots/ /poly/ /xs/ /n/ /prec/ 
--
-- Generates the polynomial \((x-x_0)(x-x_1)\cdots(x-x_{n-1})\).
foreign import ccall "arb_poly.h arb_poly_product_roots"
  arb_poly_product_roots :: Ptr CArbPoly -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /_arb_poly_product_roots_complex/ /poly/ /r/ /rn/ /c/ /cn/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_product_roots_complex"
  _arb_poly_product_roots_complex :: Ptr CArb -> Ptr CArb -> CLong -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /arb_poly_product_roots_complex/ /poly/ /r/ /rn/ /c/ /cn/ /prec/ 
--
-- Generates the polynomial
-- 
-- \[`\]
-- \[\left(\prod_{i=0}^{rn-1} (x-r_i)\right) \left(\prod_{i=0}^{cn-1} (x-c_i)(x-\bar{c_i})\right)\]
-- 
-- having /rn/ real roots given by the array /r/ and having \(2cn\) complex
-- roots in conjugate pairs given by the length-/cn/ array /c/. Either /rn/
-- or /cn/ or both may be zero.
-- 
-- Note that only one representative from each complex conjugate pair is
-- supplied (unless a pair is supposed to be repeated with higher
-- multiplicity). To construct a polynomial from complex roots where the
-- conjugate pairs have not been distinguished, use
-- @acb_poly_product_roots@ instead.
foreign import ccall "arb_poly.h arb_poly_product_roots_complex"
  arb_poly_product_roots_complex :: Ptr CArbPoly -> Ptr CArb -> CLong -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /_arb_poly_tree_alloc/ /len/ 
--
-- Returns an initialized data structured capable of representing a
-- remainder tree (product tree) of /len/ roots.
foreign import ccall "arb_poly.h _arb_poly_tree_alloc"
  _arb_poly_tree_alloc :: CLong -> IO (Ptr (Ptr CArb))

-- | /_arb_poly_tree_free/ /tree/ /len/ 
--
-- Deallocates a tree structure as allocated using /_arb_poly_tree_alloc/.
foreign import ccall "arb_poly.h _arb_poly_tree_free"
  _arb_poly_tree_free :: Ptr (Ptr CArb) -> CLong -> IO ()

-- | /_arb_poly_tree_build/ /tree/ /roots/ /len/ /prec/ 
--
-- Constructs a product tree from a given array of /len/ roots. The tree
-- structure must be pre-allocated to the specified length using
-- @_arb_poly_tree_alloc@.
foreign import ccall "arb_poly.h _arb_poly_tree_build"
  _arb_poly_tree_build :: Ptr (Ptr CArb) -> Ptr CArb -> CLong -> CLong -> IO ()

-- Multipoint evaluation -------------------------------------------------------

-- | /_arb_poly_evaluate_vec_iter/ /ys/ /poly/ /plen/ /xs/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_evaluate_vec_iter"
  _arb_poly_evaluate_vec_iter :: Ptr CArb -> Ptr CArb -> CLong -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /arb_poly_evaluate_vec_iter/ /ys/ /poly/ /xs/ /n/ /prec/ 
--
-- Evaluates the polynomial simultaneously at /n/ given points, calling
-- @_arb_poly_evaluate@ repeatedly.
foreign import ccall "arb_poly.h arb_poly_evaluate_vec_iter"
  arb_poly_evaluate_vec_iter :: Ptr CArb -> Ptr CArbPoly -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /_arb_poly_evaluate_vec_fast_precomp/ /vs/ /poly/ /plen/ /tree/ /len/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_evaluate_vec_fast_precomp"
  _arb_poly_evaluate_vec_fast_precomp :: Ptr CArb -> Ptr CArb -> CLong -> Ptr (Ptr CArb) -> CLong -> CLong -> IO ()

-- | /_arb_poly_evaluate_vec_fast/ /ys/ /poly/ /plen/ /xs/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_evaluate_vec_fast"
  _arb_poly_evaluate_vec_fast :: Ptr CArb -> Ptr CArb -> CLong -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /arb_poly_evaluate_vec_fast/ /ys/ /poly/ /xs/ /n/ /prec/ 
--
-- Evaluates the polynomial simultaneously at /n/ given points, using fast
-- multipoint evaluation.
foreign import ccall "arb_poly.h arb_poly_evaluate_vec_fast"
  arb_poly_evaluate_vec_fast :: Ptr CArb -> Ptr CArbPoly -> Ptr CArb -> CLong -> CLong -> IO ()

-- Interpolation ---------------------------------------------------------------

-- | /_arb_poly_interpolate_newton/ /poly/ /xs/ /ys/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_interpolate_newton"
  _arb_poly_interpolate_newton :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /arb_poly_interpolate_newton/ /poly/ /xs/ /ys/ /n/ /prec/ 
--
-- Recovers the unique polynomial of length at most /n/ that interpolates
-- the given /x/ and /y/ values. This implementation first interpolates in
-- the Newton basis and then converts back to the monomial basis.
foreign import ccall "arb_poly.h arb_poly_interpolate_newton"
  arb_poly_interpolate_newton :: Ptr CArbPoly -> Ptr CArb -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /_arb_poly_interpolate_barycentric/ /poly/ /xs/ /ys/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_interpolate_barycentric"
  _arb_poly_interpolate_barycentric :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /arb_poly_interpolate_barycentric/ /poly/ /xs/ /ys/ /n/ /prec/ 
--
-- Recovers the unique polynomial of length at most /n/ that interpolates
-- the given /x/ and /y/ values. This implementation uses the barycentric
-- form of Lagrange interpolation.
foreign import ccall "arb_poly.h arb_poly_interpolate_barycentric"
  arb_poly_interpolate_barycentric :: Ptr CArbPoly -> Ptr CArb -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /_arb_poly_interpolation_weights/ /w/ /tree/ /len/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_interpolation_weights"
  _arb_poly_interpolation_weights :: Ptr CArb -> Ptr (Ptr CArb) -> CLong -> CLong -> IO ()

-- | /_arb_poly_interpolate_fast_precomp/ /poly/ /ys/ /tree/ /weights/ /len/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_interpolate_fast_precomp"
  _arb_poly_interpolate_fast_precomp :: Ptr CArb -> Ptr CArb -> Ptr (Ptr CArb) -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /_arb_poly_interpolate_fast/ /poly/ /xs/ /ys/ /len/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_interpolate_fast"
  _arb_poly_interpolate_fast :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /arb_poly_interpolate_fast/ /poly/ /xs/ /ys/ /n/ /prec/ 
--
-- Recovers the unique polynomial of length at most /n/ that interpolates
-- the given /x/ and /y/ values, using fast Lagrange interpolation. The
-- precomp function takes a precomputed product tree over the /x/ values
-- and a vector of interpolation weights as additional inputs.
foreign import ccall "arb_poly.h arb_poly_interpolate_fast"
  arb_poly_interpolate_fast :: Ptr CArbPoly -> Ptr CArb -> Ptr CArb -> CLong -> CLong -> IO ()

-- Differentiation -------------------------------------------------------------

-- | /_arb_poly_derivative/ /res/ /poly/ /len/ /prec/ 
--
-- Sets /{res, len - 1}/ to the derivative of /{poly, len}/. Allows
-- aliasing of the input and output.
foreign import ccall "arb_poly.h _arb_poly_derivative"
  _arb_poly_derivative :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /arb_poly_derivative/ /res/ /poly/ /prec/ 
--
-- Sets /res/ to the derivative of /poly/.
foreign import ccall "arb_poly.h arb_poly_derivative"
  arb_poly_derivative :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> IO ()

-- | /_arb_poly_nth_derivative/ /res/ /poly/ /n/ /len/ /prec/ 
--
-- Sets /{res, len - n}/ to the nth derivative of /{poly, len}/. Does
-- nothing if /len \<= n/. Allows aliasing of the input and output.
foreign import ccall "arb_poly.h _arb_poly_nth_derivative"
  _arb_poly_nth_derivative :: Ptr CArb -> Ptr CArb -> CULong -> CLong -> CLong -> IO ()

-- | /arb_poly_nth_derivative/ /res/ /poly/ /prec/ 
--
-- Sets /res/ to the nth derivative of /poly/.
foreign import ccall "arb_poly.h arb_poly_nth_derivative"
  arb_poly_nth_derivative :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> IO ()

-- | /_arb_poly_integral/ /res/ /poly/ /len/ /prec/ 
--
-- Sets /{res, len}/ to the integral of /{poly, len - 1}/. Allows aliasing
-- of the input and output.
foreign import ccall "arb_poly.h _arb_poly_integral"
  _arb_poly_integral :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /arb_poly_integral/ /res/ /poly/ /prec/ 
--
-- Sets /res/ to the integral of /poly/.
foreign import ccall "arb_poly.h arb_poly_integral"
  arb_poly_integral :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> IO ()

-- Transforms ------------------------------------------------------------------

-- | /_arb_poly_borel_transform/ /res/ /poly/ /len/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_borel_transform"
  _arb_poly_borel_transform :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /arb_poly_borel_transform/ /res/ /poly/ /prec/ 
--
-- Computes the Borel transform of the input polynomial, mapping
-- \(\sum_k a_k x^k\) to \(\sum_k (a_k / k!) x^k\). The underscore method
-- allows aliasing.
foreign import ccall "arb_poly.h arb_poly_borel_transform"
  arb_poly_borel_transform :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> IO ()

-- | /_arb_poly_inv_borel_transform/ /res/ /poly/ /len/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_inv_borel_transform"
  _arb_poly_inv_borel_transform :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /arb_poly_inv_borel_transform/ /res/ /poly/ /prec/ 
--
-- Computes the inverse Borel transform of the input polynomial, mapping
-- \(\sum_k a_k x^k\) to \(\sum_k a_k k! x^k\). The underscore method
-- allows aliasing.
foreign import ccall "arb_poly.h arb_poly_inv_borel_transform"
  arb_poly_inv_borel_transform :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> IO ()

-- | /_arb_poly_binomial_transform_basecase/ /b/ /a/ /alen/ /len/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_binomial_transform_basecase"
  _arb_poly_binomial_transform_basecase :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_poly_binomial_transform_basecase/ /b/ /a/ /len/ /prec/ 
--
foreign import ccall "arb_poly.h arb_poly_binomial_transform_basecase"
  arb_poly_binomial_transform_basecase :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_poly_binomial_transform_convolution/ /b/ /a/ /alen/ /len/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_binomial_transform_convolution"
  _arb_poly_binomial_transform_convolution :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_poly_binomial_transform_convolution/ /b/ /a/ /len/ /prec/ 
--
foreign import ccall "arb_poly.h arb_poly_binomial_transform_convolution"
  arb_poly_binomial_transform_convolution :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_poly_binomial_transform/ /b/ /a/ /alen/ /len/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_binomial_transform"
  _arb_poly_binomial_transform :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_poly_binomial_transform/ /b/ /a/ /len/ /prec/ 
--
-- Computes the binomial transform of the input polynomial, truncating the
-- output to length /len/. The binomial transform maps the coefficients
-- \(a_k\) in the input polynomial to the coefficients \(b_k\) in the
-- output polynomial via \(b_n = \sum_{k=0}^n (-1)^k {n \choose k} a_k\).
-- The binomial transform is equivalent to the power series composition
-- \(f(x) \to (1-x)^{-1} f(x/(x-1))\), and is its own inverse.
-- 
-- The /basecase/ version evaluates coefficients one by one from the
-- definition, generating the binomial coefficients by a recurrence
-- relation.
-- 
-- The /convolution/ version uses the identity
-- \(T(f(x)) = B^{-1}(e^x B(f(-x)))\) where \(T\) denotes the binomial
-- transform operator and \(B\) denotes the Borel transform operator. This
-- only costs a single polynomial multiplication, plus some scalar
-- operations.
-- 
-- The default version automatically chooses an algorithm.
-- 
-- The underscore methods do not support aliasing, and assume that the
-- lengths are nonzero.
foreign import ccall "arb_poly.h arb_poly_binomial_transform"
  arb_poly_binomial_transform :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_poly_graeffe_transform/ /b/ /a/ /len/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_graeffe_transform"
  _arb_poly_graeffe_transform :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /arb_poly_graeffe_transform/ /b/ /a/ /prec/ 
--
-- Computes the Graeffe transform of input polynomial.
-- 
-- The Graeffe transform \(G\) of a polynomial \(P\) is defined through the
-- equation \(G(x^2) = \pm P(x)P(-x)\). The sign is given by \((-1)^d\),
-- where \(d = deg(P)\). The Graeffe transform has the property that its
-- roots are exactly the squares of the roots of P.
-- 
-- The underscore method assumes that /a/ and /b/ are initialized, /a/ is
-- of length /len/, and /b/ is of length at least /len/. Both methods allow
-- aliasing.
foreign import ccall "arb_poly.h arb_poly_graeffe_transform"
  arb_poly_graeffe_transform :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> IO ()

-- Powers and elementary functions ---------------------------------------------

-- | /_arb_poly_pow_ui_trunc_binexp/ /res/ /f/ /flen/ /exp/ /len/ /prec/ 
--
-- Sets /{res, len}/ to /{f, flen}/ raised to the power /exp/, truncated to
-- length /len/. Requires that /len/ is no longer than the length of the
-- power as computed without truncation (i.e. no zero-padding is
-- performed). Does not support aliasing of the input and output, and
-- requires that /flen/ and /len/ are positive. Uses binary exponentiation.
foreign import ccall "arb_poly.h _arb_poly_pow_ui_trunc_binexp"
  _arb_poly_pow_ui_trunc_binexp :: Ptr CArb -> Ptr CArb -> CLong -> CULong -> CLong -> CLong -> IO ()

-- | /arb_poly_pow_ui_trunc_binexp/ /res/ /poly/ /exp/ /len/ /prec/ 
--
-- Sets /res/ to /poly/ raised to the power /exp/, truncated to length
-- /len/. Uses binary exponentiation.
foreign import ccall "arb_poly.h arb_poly_pow_ui_trunc_binexp"
  arb_poly_pow_ui_trunc_binexp :: Ptr CArbPoly -> Ptr CArbPoly -> CULong -> CLong -> CLong -> IO ()

-- | /_arb_poly_pow_ui/ /res/ /f/ /flen/ /exp/ /prec/ 
--
-- Sets /res/ to /{f, flen}/ raised to the power /exp/. Does not support
-- aliasing of the input and output, and requires that /flen/ is positive.
foreign import ccall "arb_poly.h _arb_poly_pow_ui"
  _arb_poly_pow_ui :: Ptr CArb -> Ptr CArb -> CLong -> CULong -> CLong -> IO ()

-- | /arb_poly_pow_ui/ /res/ /poly/ /exp/ /prec/ 
--
-- Sets /res/ to /poly/ raised to the power /exp/.
foreign import ccall "arb_poly.h arb_poly_pow_ui"
  arb_poly_pow_ui :: Ptr CArbPoly -> Ptr CArbPoly -> CULong -> CLong -> IO ()

-- | /_arb_poly_pow_series/ /h/ /f/ /flen/ /g/ /glen/ /len/ /prec/ 
--
-- Sets /{h, len}/ to the power series
-- \(f(x)^{g(x)} = \exp(g(x) \log f(x))\) truncated to length /len/. This
-- function detects special cases such as /g/ being an exact small integer
-- or \(\pm 1/2\), and computes such powers more efficiently. This function
-- does not support aliasing of the output with either of the input
-- operands. It requires that all lengths are positive, and assumes that
-- /flen/ and /glen/ do not exceed /len/.
foreign import ccall "arb_poly.h _arb_poly_pow_series"
  _arb_poly_pow_series :: Ptr CArb -> Ptr CArb -> CLong -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_poly_pow_series/ /h/ /f/ /g/ /len/ /prec/ 
--
-- Sets /h/ to the power series \(f(x)^{g(x)} = \exp(g(x) \log f(x))\)
-- truncated to length /len/. This function detects special cases such as
-- /g/ being an exact small integer or \(\pm 1/2\), and computes such
-- powers more efficiently.
foreign import ccall "arb_poly.h arb_poly_pow_series"
  arb_poly_pow_series :: Ptr CArbPoly -> Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_poly_pow_arb_series/ /h/ /f/ /flen/ /g/ /len/ /prec/ 
--
-- Sets /{h, len}/ to the power series \(f(x)^g = \exp(g \log f(x))\)
-- truncated to length /len/. This function detects special cases such as
-- /g/ being an exact small integer or \(\pm 1/2\), and computes such
-- powers more efficiently. This function does not support aliasing of the
-- output with either of the input operands. It requires that all lengths
-- are positive, and assumes that /flen/ does not exceed /len/.
foreign import ccall "arb_poly.h _arb_poly_pow_arb_series"
  _arb_poly_pow_arb_series :: Ptr CArb -> Ptr CArb -> CLong -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /arb_poly_pow_arb_series/ /h/ /f/ /g/ /len/ /prec/ 
--
-- Sets /h/ to the power series \(f(x)^g = \exp(g \log f(x))\) truncated to
-- length /len/.
foreign import ccall "arb_poly.h arb_poly_pow_arb_series"
  arb_poly_pow_arb_series :: Ptr CArbPoly -> Ptr CArbPoly -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /_arb_poly_sqrt_series/ /g/ /h/ /hlen/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_sqrt_series"
  _arb_poly_sqrt_series :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_poly_sqrt_series/ /g/ /h/ /n/ /prec/ 
--
-- Sets /g/ to the power series square root of /h/, truncated to length
-- /n/. Uses division-free Newton iteration for the reciprocal square root,
-- followed by a multiplication.
-- 
-- The underscore method does not support aliasing of the input and output
-- arrays. It requires that /hlen/ and /n/ are greater than zero.
foreign import ccall "arb_poly.h arb_poly_sqrt_series"
  arb_poly_sqrt_series :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_poly_rsqrt_series/ /g/ /h/ /hlen/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_rsqrt_series"
  _arb_poly_rsqrt_series :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_poly_rsqrt_series/ /g/ /h/ /n/ /prec/ 
--
-- Sets /g/ to the reciprocal power series square root of /h/, truncated to
-- length /n/. Uses division-free Newton iteration.
-- 
-- The underscore method does not support aliasing of the input and output
-- arrays. It requires that /hlen/ and /n/ are greater than zero.
foreign import ccall "arb_poly.h arb_poly_rsqrt_series"
  arb_poly_rsqrt_series :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_poly_log_series/ /res/ /f/ /flen/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_log_series"
  _arb_poly_log_series :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_poly_log_series/ /res/ /f/ /n/ /prec/ 
--
-- Sets /res/ to the power series logarithm of /f/, truncated to length
-- /n/. Uses the formula \(\log(f(x)) = \int f'(x) / f(x) dx\), adding the
-- logarithm of the constant term in /f/ as the constant of integration.
-- 
-- The underscore method supports aliasing of the input and output arrays.
-- It requires that /flen/ and /n/ are greater than zero.
foreign import ccall "arb_poly.h arb_poly_log_series"
  arb_poly_log_series :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_poly_log1p_series/ /res/ /f/ /flen/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_log1p_series"
  _arb_poly_log1p_series :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_poly_log1p_series/ /res/ /f/ /n/ /prec/ 
--
-- Computes the power series \(\log(1+f)\), with better accuracy when the
-- constant term of /f/ is small.
foreign import ccall "arb_poly.h arb_poly_log1p_series"
  arb_poly_log1p_series :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_poly_atan_series/ /res/ /f/ /flen/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_atan_series"
  _arb_poly_atan_series :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_poly_atan_series/ /res/ /f/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h arb_poly_atan_series"
  arb_poly_atan_series :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_poly_asin_series/ /res/ /f/ /flen/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_asin_series"
  _arb_poly_asin_series :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_poly_asin_series/ /res/ /f/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h arb_poly_asin_series"
  arb_poly_asin_series :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_poly_acos_series/ /res/ /f/ /flen/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_acos_series"
  _arb_poly_acos_series :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_poly_acos_series/ /res/ /f/ /n/ /prec/ 
--
-- Sets /res/ respectively to the power series inverse tangent, inverse
-- sine and inverse cosine of /f/, truncated to length /n/.
-- 
-- Uses the formulas
-- 
-- \[`\]
-- \[\tan^{-1}(f(x)) = \int f'(x) / (1+f(x)^2) dx,\]
-- \[\sin^{-1}(f(x)) = \int f'(x) / (1-f(x)^2)^{1/2} dx,\]
-- \[\cos^{-1}(f(x)) = -\int f'(x) / (1-f(x)^2)^{1/2} dx,\]
-- 
-- adding the inverse function of the constant term in /f/ as the constant
-- of integration.
-- 
-- The underscore methods supports aliasing of the input and output arrays.
-- They require that /flen/ and /n/ are greater than zero.
foreign import ccall "arb_poly.h arb_poly_acos_series"
  arb_poly_acos_series :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_poly_exp_series_basecase/ /f/ /h/ /hlen/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_exp_series_basecase"
  _arb_poly_exp_series_basecase :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_poly_exp_series_basecase/ /f/ /h/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h arb_poly_exp_series_basecase"
  arb_poly_exp_series_basecase :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_poly_exp_series/ /f/ /h/ /hlen/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_exp_series"
  _arb_poly_exp_series :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_poly_exp_series/ /f/ /h/ /n/ /prec/ 
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
foreign import ccall "arb_poly.h arb_poly_exp_series"
  arb_poly_exp_series :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_poly_sin_cos_series/ /s/ /c/ /h/ /hlen/ /n/ /prec/ 
foreign import ccall "arb_poly.h _arb_poly_sin_cos_series"
  _arb_poly_sin_cos_series :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()
-- | /arb_poly_sin_cos_series/ /s/ /c/ /h/ /n/ /prec/ 
--
-- Sets /s/ and /c/ to the power series sine and cosine of /h/, computed
-- simultaneously. The underscore method supports aliasing and requires the
-- lengths to be nonzero.
foreign import ccall "arb_poly.h arb_poly_sin_cos_series"
  arb_poly_sin_cos_series :: Ptr CArbPoly -> Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_poly_sin_series/ /s/ /h/ /hlen/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_sin_series"
  _arb_poly_sin_series :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_poly_sin_series/ /s/ /h/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h arb_poly_sin_series"
  arb_poly_sin_series :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_poly_cos_series/ /c/ /h/ /hlen/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_cos_series"
  _arb_poly_cos_series :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_poly_cos_series/ /c/ /h/ /n/ /prec/ 
--
-- Respectively evaluates the power series sine or cosine. These functions
-- simply wrap @_arb_poly_sin_cos_series@. The underscore methods support
-- aliasing and require the lengths to be nonzero.
foreign import ccall "arb_poly.h arb_poly_cos_series"
  arb_poly_cos_series :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_poly_tan_series/ /g/ /h/ /hlen/ /len/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_tan_series"
  _arb_poly_tan_series :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_poly_tan_series/ /g/ /h/ /n/ /prec/ 
--
-- Sets /g/ to the power series tangent of /h/.
-- 
-- For small /n/ takes the quotient of the sine and cosine as computed
-- using the basecase algorithm. For large /n/, uses Newton iteration to
-- invert the inverse tangent series. The complexity is \(O(M(n))\).
-- 
-- The underscore version does not support aliasing, and requires the
-- lengths to be nonzero.
foreign import ccall "arb_poly.h arb_poly_tan_series"
  arb_poly_tan_series :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_poly_sin_cos_pi_series/ /s/ /c/ /h/ /hlen/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_sin_cos_pi_series"
  _arb_poly_sin_cos_pi_series :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_poly_sin_cos_pi_series/ /s/ /c/ /h/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h arb_poly_sin_cos_pi_series"
  arb_poly_sin_cos_pi_series :: Ptr CArbPoly -> Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_poly_sin_pi_series/ /s/ /h/ /hlen/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_sin_pi_series"
  _arb_poly_sin_pi_series :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_poly_sin_pi_series/ /s/ /h/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h arb_poly_sin_pi_series"
  arb_poly_sin_pi_series :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_poly_cos_pi_series/ /c/ /h/ /hlen/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_cos_pi_series"
  _arb_poly_cos_pi_series :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_poly_cos_pi_series/ /c/ /h/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h arb_poly_cos_pi_series"
  arb_poly_cos_pi_series :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_poly_cot_pi_series/ /c/ /h/ /hlen/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_cot_pi_series"
  _arb_poly_cot_pi_series :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_poly_cot_pi_series/ /c/ /h/ /n/ /prec/ 
--
-- Compute the respective trigonometric functions of the input multiplied
-- by \(\pi\).
foreign import ccall "arb_poly.h arb_poly_cot_pi_series"
  arb_poly_cot_pi_series :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_poly_sinh_cosh_series_basecase/ /s/ /c/ /h/ /hlen/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_sinh_cosh_series_basecase"
  _arb_poly_sinh_cosh_series_basecase :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_poly_sinh_cosh_series_basecase/ /s/ /c/ /h/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h arb_poly_sinh_cosh_series_basecase"
  arb_poly_sinh_cosh_series_basecase :: Ptr CArbPoly -> Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_poly_sinh_cosh_series_exponential/ /s/ /c/ /h/ /hlen/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_sinh_cosh_series_exponential"
  _arb_poly_sinh_cosh_series_exponential :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_poly_sinh_cosh_series_exponential/ /s/ /c/ /h/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h arb_poly_sinh_cosh_series_exponential"
  arb_poly_sinh_cosh_series_exponential :: Ptr CArbPoly -> Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_poly_sinh_cosh_series/ /s/ /c/ /h/ /hlen/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_sinh_cosh_series"
  _arb_poly_sinh_cosh_series :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_poly_sinh_cosh_series/ /s/ /c/ /h/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h arb_poly_sinh_cosh_series"
  arb_poly_sinh_cosh_series :: Ptr CArbPoly -> Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_poly_sinh_series/ /s/ /h/ /hlen/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_sinh_series"
  _arb_poly_sinh_series :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_poly_sinh_series/ /s/ /h/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h arb_poly_sinh_series"
  arb_poly_sinh_series :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_poly_cosh_series/ /c/ /h/ /hlen/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_cosh_series"
  _arb_poly_cosh_series :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_poly_cosh_series/ /c/ /h/ /n/ /prec/ 
--
-- Sets /s/ and /c/ respectively to the hyperbolic sine and cosine of the
-- power series /h/, truncated to length /n/.
-- 
-- The implementations mirror those for sine and cosine, except that the
-- /exponential/ version computes both functions using the exponential
-- function instead of the hyperbolic tangent.
foreign import ccall "arb_poly.h arb_poly_cosh_series"
  arb_poly_cosh_series :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_poly_sinc_series/ /s/ /h/ /hlen/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_sinc_series"
  _arb_poly_sinc_series :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_poly_sinc_series/ /s/ /h/ /n/ /prec/ 
--
-- Sets /c/ to the sinc function of the power series /h/, truncated to
-- length /n/.
foreign import ccall "arb_poly.h arb_poly_sinc_series"
  arb_poly_sinc_series :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_poly_sinc_pi_series/ /s/ /h/ /hlen/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_sinc_pi_series"
  _arb_poly_sinc_pi_series :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_poly_sinc_pi_series/ /s/ /h/ /n/ /prec/ 
--
-- Compute the sinc function of the input multiplied by \(\pi\).
foreign import ccall "arb_poly.h arb_poly_sinc_pi_series"
  arb_poly_sinc_pi_series :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- Lambert W function ----------------------------------------------------------

-- | /_arb_poly_lambertw_series/ /res/ /z/ /zlen/ /flags/ /len/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_lambertw_series"
  _arb_poly_lambertw_series :: Ptr CArb -> Ptr CArb -> CLong -> CInt -> CLong -> CLong -> IO ()

-- | /arb_poly_lambertw_series/ /res/ /z/ /flags/ /len/ /prec/ 
--
-- Sets /res/ to the Lambert W function of the power series /z/. If /flags/
-- is 0, the principal branch is computed; if /flags/ is 1, the second real
-- branch \(W_{-1}(z)\) is computed. The underscore method allows aliasing,
-- but assumes that the lengths are nonzero.
foreign import ccall "arb_poly.h arb_poly_lambertw_series"
  arb_poly_lambertw_series :: Ptr CArbPoly -> Ptr CArbPoly -> CInt -> CLong -> CLong -> IO ()

-- Gamma function and factorials -----------------------------------------------

-- | /_arb_poly_gamma_series/ /res/ /h/ /hlen/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_gamma_series"
  _arb_poly_gamma_series :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_poly_gamma_series/ /res/ /h/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h arb_poly_gamma_series"
  arb_poly_gamma_series :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_poly_rgamma_series/ /res/ /h/ /hlen/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_rgamma_series"
  _arb_poly_rgamma_series :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_poly_rgamma_series/ /res/ /h/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h arb_poly_rgamma_series"
  arb_poly_rgamma_series :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_poly_lgamma_series/ /res/ /h/ /hlen/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_lgamma_series"
  _arb_poly_lgamma_series :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_poly_lgamma_series/ /res/ /h/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h arb_poly_lgamma_series"
  arb_poly_lgamma_series :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_poly_digamma_series/ /res/ /h/ /hlen/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_digamma_series"
  _arb_poly_digamma_series :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_poly_digamma_series/ /res/ /h/ /n/ /prec/ 
--
-- Sets /res/ to the series expansion of \(\Gamma(h(x))\),
-- \(1/\Gamma(h(x))\), or \(\log \Gamma(h(x))\), \(\psi(h(x))\), truncated
-- to length /n/.
-- 
-- These functions first generate the Taylor series at the constant term of
-- /h/, and then call @_arb_poly_compose_series@. The Taylor coefficients
-- are generated using the Riemann zeta function if the constant term of
-- /h/ is a small integer, and with Stirling\'s series otherwise.
-- 
-- The underscore methods support aliasing of the input and output arrays,
-- and require that /hlen/ and /n/ are greater than zero.
foreign import ccall "arb_poly.h arb_poly_digamma_series"
  arb_poly_digamma_series :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_poly_rising_ui_series/ /res/ /f/ /flen/ /r/ /trunc/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_rising_ui_series"
  _arb_poly_rising_ui_series :: Ptr CArb -> Ptr CArb -> CLong -> CULong -> CLong -> CLong -> IO ()

-- | /arb_poly_rising_ui_series/ /res/ /f/ /r/ /trunc/ /prec/ 
--
-- Sets /res/ to the rising factorial \((f) (f+1) (f+2) \cdots (f+r-1)\),
-- truncated to length /trunc/. The underscore method assumes that /flen/,
-- /r/ and /trunc/ are at least 1, and does not support aliasing. Uses
-- binary splitting.
foreign import ccall "arb_poly.h arb_poly_rising_ui_series"
  arb_poly_rising_ui_series :: Ptr CArbPoly -> Ptr CArbPoly -> CULong -> CLong -> CLong -> IO ()

-- Zeta function ---------------------------------------------------------------

-- | /arb_poly_zeta_series/ /res/ /s/ /a/ /deflate/ /n/ /prec/ 
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
-- \[\sum_{k=0}^{n-1} \frac{(-1)^k}{k!} \gamma_k(a) x^k.\]
-- 
-- If \(a = 1\), this implementation uses the reflection formula if the
-- midpoint of the constant term of \(s\) is negative.
foreign import ccall "arb_poly.h arb_poly_zeta_series"
  arb_poly_zeta_series :: Ptr CArbPoly -> Ptr CArbPoly -> Ptr CArb -> CInt -> CLong -> CLong -> IO ()

-- | /_arb_poly_riemann_siegel_theta_series/ /res/ /h/ /hlen/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_riemann_siegel_theta_series"
  _arb_poly_riemann_siegel_theta_series :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_poly_riemann_siegel_theta_series/ /res/ /h/ /n/ /prec/ 
--
-- Sets /res/ to the series expansion of the Riemann-Siegel theta function
-- 
-- \[`\]
-- \[\theta(h) = \arg \left(\Gamma\left(\frac{2ih+1}{4}\right)\right) - \frac{\log \pi}{2} h\]
-- 
-- where the argument of the gamma function is chosen continuously as the
-- imaginary part of the log gamma function.
-- 
-- The underscore method does not support aliasing of the input and output
-- arrays, and requires that the lengths are greater than zero.
foreign import ccall "arb_poly.h arb_poly_riemann_siegel_theta_series"
  arb_poly_riemann_siegel_theta_series :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_poly_riemann_siegel_z_series/ /res/ /h/ /hlen/ /n/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_riemann_siegel_z_series"
  _arb_poly_riemann_siegel_z_series :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_poly_riemann_siegel_z_series/ /res/ /h/ /n/ /prec/ 
--
-- Sets /res/ to the series expansion of the Riemann-Siegel Z-function
-- 
-- \[`\]
-- \[Z(h) = e^{i\theta(h)} \zeta(1/2+ih).\]
-- 
-- The zeros of the Z-function on the real line precisely correspond to the
-- imaginary parts of the zeros of the Riemann zeta function on the
-- critical line.
-- 
-- The underscore method supports aliasing of the input and output arrays,
-- and requires that the lengths are greater than zero.
foreign import ccall "arb_poly.h arb_poly_riemann_siegel_z_series"
  arb_poly_riemann_siegel_z_series :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- Root-finding ----------------------------------------------------------------

-- | /_arb_poly_root_bound_fujiwara/ /bound/ /poly/ /len/ 
--
foreign import ccall "arb_poly.h _arb_poly_root_bound_fujiwara"
  _arb_poly_root_bound_fujiwara :: Ptr CMag -> Ptr CArb -> CLong -> IO ()

-- | /arb_poly_root_bound_fujiwara/ /bound/ /poly/ 
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
foreign import ccall "arb_poly.h arb_poly_root_bound_fujiwara"
  arb_poly_root_bound_fujiwara :: Ptr CMag -> Ptr CArbPoly -> IO ()

-- | /_arb_poly_newton_convergence_factor/ /convergence_factor/ /poly/ /len/ /convergence_interval/ /prec/ 
--
-- Given an interval \(I\) specified by /convergence_interval/, evaluates a
-- bound for \(C = \sup_{t,u \in I} \frac{1}{2} |f''(t)| / |f'(u)|\), where
-- \(f\) is the polynomial defined by the coefficients /{poly, len}/. The
-- bound is obtained by evaluating \(f'(I)\) and \(f''(I)\) directly. If
-- \(f\) has large coefficients, \(I\) must be extremely precise in order
-- to get a finite factor.
foreign import ccall "arb_poly.h _arb_poly_newton_convergence_factor"
  _arb_poly_newton_convergence_factor :: Ptr CArf -> Ptr CArb -> CLong -> Ptr CArb -> CLong -> IO ()

-- | /_arb_poly_newton_step/ /xnew/ /poly/ /len/ /x/ /convergence_interval/ /convergence_factor/ /prec/ 
--
-- Performs a single step with Newton\'s method.
-- 
-- The input consists of the polynomial \(f\) specified by the coefficients
-- /{poly, len}/, an interval \(x = [m-r, m+r]\) known to contain a single
-- root of \(f\), an interval \(I\) (/convergence_interval/) containing
-- \(x\) with an associated bound (/convergence_factor/) for
-- \(C = \sup_{t,u \in I} \frac{1}{2} |f''(t)| / |f'(u)|\), and a working
-- precision /prec/.
-- 
-- The Newton update consists of setting \(x' = [m'-r', m'+r']\) where
-- \(m' = m - f(m) / f'(m)\) and \(r' = C r^2\). The expression
-- \(m - f(m) / f'(m)\) is evaluated using ball arithmetic at a working
-- precision of /prec/ bits, and the rounding error during this evaluation
-- is accounted for in the output. We now check that \(x' \in I\) and
-- \(m' < m\). If both conditions are satisfied, we set /xnew/ to \(x'\)
-- and return nonzero. If either condition fails, we set /xnew/ to \(x\)
-- and return zero, indicating that no progress was made.
foreign import ccall "arb_poly.h _arb_poly_newton_step"
  _arb_poly_newton_step :: Ptr CArb -> Ptr CArb -> CLong -> Ptr CArb -> Ptr CArb -> Ptr CArf -> CLong -> IO CInt

-- | /_arb_poly_newton_refine_root/ /r/ /poly/ /len/ /start/ /convergence_interval/ /convergence_factor/ /eval_extra_prec/ /prec/ 
--
-- Refines a precise estimate of a polynomial root to high precision by
-- performing several Newton steps, using nearly optimally chosen doubling
-- precision steps.
-- 
-- The inputs are defined as for /_arb_poly_newton_step/, except for the
-- precision parameters: /prec/ is the target accuracy and
-- /eval_extra_prec/ is the estimated number of guard bits that need to be
-- added to evaluate the polynomial accurately close to the root
-- (typically, if the polynomial has large coefficients of alternating
-- signs, this needs to be approximately the bit size of the coefficients).
foreign import ccall "arb_poly.h _arb_poly_newton_refine_root"
  _arb_poly_newton_refine_root :: Ptr CArb -> Ptr CArb -> CLong -> Ptr CArb -> Ptr CArb -> Ptr CArf -> CLong -> CLong -> IO ()

-- Other special polynomials ---------------------------------------------------

-- | /_arb_poly_swinnerton_dyer_ui/ /poly/ /n/ /trunc/ /prec/ 
--
foreign import ccall "arb_poly.h _arb_poly_swinnerton_dyer_ui"
  _arb_poly_swinnerton_dyer_ui :: Ptr CArb -> CULong -> CLong -> CLong -> IO ()

-- | /arb_poly_swinnerton_dyer_ui/ /poly/ /n/ /prec/ 
--
-- Computes the Swinnerton-Dyer polynomial \(S_n\), which has degree
-- \(2^n\) and is the rational minimal polynomial of the sum of the square
-- roots of the first /n/ prime numbers.
-- 
-- If /prec/ is set to zero, a precision is chosen automatically such that
-- @arb_poly_get_unique_fmpz_poly@ should be successful. Otherwise a
-- working precision of /prec/ bits is used.
-- 
-- The underscore version accepts an additional /trunc/ parameter. Even
-- when computing a truncated polynomial, the array /poly/ must have room
-- for \(2^n + 1\) coefficients, used as temporary space.
foreign import ccall "arb_poly.h arb_poly_swinnerton_dyer_ui"
  arb_poly_swinnerton_dyer_ui :: Ptr CArbPoly -> CULong -> CLong -> IO ()

