
module Data.Number.Flint.NMod.Poly.FFI (
  -- * Univariate polynomials over integers mod n (word-size n)
  -- * Types
    NModPoly (..)
  , CNModPoly (..)
  , newNModPoly
  , withNModPoly
  , withNewNModPoly
  -- * Helper functions
  , signed_mpn_sub_n
  -- * Memory management
  , nmod_poly_init
  , nmod_poly_init_preinv
  , nmod_poly_init_mod
  , nmod_poly_init2
  , nmod_poly_init2_preinv
  , nmod_poly_realloc
  , nmod_poly_clear
  , nmod_poly_fit_length
  , _nmod_poly_normalise
  -- * Polynomial properties
  , nmod_poly_length
  , nmod_poly_degree
  , nmod_poly_modulus
  , nmod_poly_max_bits
  -- * Assignment and basic manipulation
  , nmod_poly_set
  , nmod_poly_swap
  , nmod_poly_zero
  , nmod_poly_truncate
  , nmod_poly_set_trunc
  , _nmod_poly_reverse
  , nmod_poly_reverse
  -- * Randomization
  , nmod_poly_randtest
  , nmod_poly_randtest_irreducible
  , nmod_poly_randtest_monic
  , nmod_poly_randtest_monic_irreducible
  , nmod_poly_randtest_monic_primitive
  , nmod_poly_randtest_trinomial
  , nmod_poly_randtest_trinomial_irreducible
  , nmod_poly_randtest_pentomial
  , nmod_poly_randtest_pentomial_irreducible
  , nmod_poly_randtest_sparse_irreducible
  -- * Getting and setting coefficients
  , nmod_poly_get_coeff_ui
  , nmod_poly_set_coeff_ui
  -- * Input and output
  , nmod_poly_get_str
  , nmod_poly_get_str_pretty
  , nmod_poly_set_str
  , nmod_poly_print
  , nmod_poly_print_pretty
  , nmod_poly_fread
  , nmod_poly_fprint
  , nmod_poly_fprint_pretty
  , nmod_poly_read
  -- * Comparison
  , nmod_poly_equal
  , nmod_poly_equal_trunc
  , nmod_poly_is_zero
  , nmod_poly_is_one
  -- * Shifting
  , _nmod_poly_shift_left
  , nmod_poly_shift_left
  , _nmod_poly_shift_right
  , nmod_poly_shift_right
  -- * Addition and subtraction
  , _nmod_poly_add
  , nmod_poly_add
  , nmod_poly_add_series
  , _nmod_poly_sub
  , nmod_poly_sub
  , nmod_poly_sub_series
  , nmod_poly_neg
  -- * Scalar multiplication and division
  , nmod_poly_scalar_mul_nmod
  , _nmod_poly_make_monic
  , nmod_poly_make_monic
  -- * Bit packing and unpacking
  , _nmod_poly_bit_pack
  , _nmod_poly_bit_unpack
  , nmod_poly_bit_pack
  , nmod_poly_bit_unpack
  , _nmod_poly_KS2_pack1
  , _nmod_poly_KS2_pack
  , _nmod_poly_KS2_unpack1
  , _nmod_poly_KS2_unpack2
  , _nmod_poly_KS2_unpack3
  , _nmod_poly_KS2_unpack
  -- * KS2\/KS4 Reduction
  , _nmod_poly_KS2_reduce
  , _nmod_poly_KS2_recover_reduce1
  , _nmod_poly_KS2_recover_reduce2
  , _nmod_poly_KS2_recover_reduce2b
  , _nmod_poly_KS2_recover_reduce3
  , _nmod_poly_KS2_recover_reduce
  -- * Multiplication
  , _nmod_poly_mul_classical
  , nmod_poly_mul_classical
  , _nmod_poly_mullow_classical
  , nmod_poly_mullow_classical
  , _nmod_poly_mulhigh_classical
  , nmod_poly_mulhigh_classical
  , _nmod_poly_mul_KS
  , nmod_poly_mul_KS
  , _nmod_poly_mul_KS2
  , nmod_poly_mul_KS2
  , _nmod_poly_mul_KS4
  , nmod_poly_mul_KS4
  , _nmod_poly_mullow_KS
  , nmod_poly_mullow_KS
  , _nmod_poly_mul
  , nmod_poly_mul
  , _nmod_poly_mullow
  , nmod_poly_mullow
  , _nmod_poly_mulhigh
  , nmod_poly_mulhigh
  , _nmod_poly_mulmod
  , nmod_poly_mulmod
  , _nmod_poly_mulmod_preinv
  , nmod_poly_mulmod_preinv
  -- * Powering
  , _nmod_poly_pow_binexp
  , nmod_poly_pow_binexp
  , _nmod_poly_pow
  , nmod_poly_pow
  , _nmod_poly_pow_trunc_binexp
  , nmod_poly_pow_trunc_binexp
  , _nmod_poly_pow_trunc
  , nmod_poly_pow_trunc
  , _nmod_poly_powmod_ui_binexp
  , nmod_poly_powmod_ui_binexp
  , _nmod_poly_powmod_mpz_binexp
  , nmod_poly_powmod_mpz_binexp
  , _nmod_poly_powmod_fmpz_binexp
  , nmod_poly_powmod_fmpz_binexp
  , _nmod_poly_powmod_ui_binexp_preinv
  , nmod_poly_powmod_ui_binexp_preinv
  , _nmod_poly_powmod_mpz_binexp_preinv
  , nmod_poly_powmod_mpz_binexp_preinv
  , _nmod_poly_powmod_fmpz_binexp_preinv
  , nmod_poly_powmod_fmpz_binexp_preinv
  , _nmod_poly_powmod_x_ui_preinv
  , nmod_poly_powmod_x_ui_preinv
  , _nmod_poly_powmod_x_fmpz_preinv
  , nmod_poly_powmod_x_fmpz_preinv
  , _nmod_poly_powers_mod_preinv_naive
  , nmod_poly_powers_mod_naive
  , _nmod_poly_powers_mod_preinv_threaded_pool
  , _nmod_poly_powers_mod_preinv_threaded
  , nmod_poly_powers_mod_bsgs
  -- * Division
  , _nmod_poly_divrem_basecase
  , nmod_poly_divrem_basecase
  , _nmod_poly_divrem
  , nmod_poly_divrem
  , _nmod_poly_div
  , nmod_poly_div
  , _nmod_poly_rem_q1
  , _nmod_poly_rem
  , nmod_poly_rem
  , _nmod_poly_inv_series_basecase
  , nmod_poly_inv_series_basecase
  , _nmod_poly_inv_series_newton
  , nmod_poly_inv_series_newton
  , _nmod_poly_inv_series
  , nmod_poly_inv_series
  , _nmod_poly_div_series_basecase
  , nmod_poly_div_series_basecase
  , _nmod_poly_div_series
  , nmod_poly_div_series
  , _nmod_poly_div_newton_n_preinv
  , nmod_poly_div_newton_n_preinv
  , _nmod_poly_divrem_newton_n_preinv
  , nmod_poly_divrem_newton_n_preinv
  , _nmod_poly_div_root
  , nmod_poly_div_root
  -- * Divisibility testing
  , _nmod_poly_divides_classical
  , nmod_poly_divides_classical
  , _nmod_poly_divides
  , nmod_poly_divides
  -- * Derivative and integral
  , _nmod_poly_derivative
  , nmod_poly_derivative
  , _nmod_poly_integral
  , nmod_poly_integral
  -- * Evaluation
  , _nmod_poly_evaluate_nmod
  , nmod_poly_evaluate_nmod
  , nmod_poly_evaluate_mat_horner
  , nmod_poly_evaluate_mat_paterson_stockmeyer
  , nmod_poly_evaluate_mat
  -- * Multipoint evaluation
  , _nmod_poly_evaluate_nmod_vec_iter
  , nmod_poly_evaluate_nmod_vec_iter
  , _nmod_poly_evaluate_nmod_vec_fast_precomp
  , _nmod_poly_evaluate_nmod_vec_fast
  , nmod_poly_evaluate_nmod_vec_fast
  , _nmod_poly_evaluate_nmod_vec
  , nmod_poly_evaluate_nmod_vec
  -- * Interpolation
  , _nmod_poly_interpolate_nmod_vec
  , nmod_poly_interpolate_nmod_vec
  , _nmod_poly_interpolation_weights
  , _nmod_poly_interpolate_nmod_vec_fast_precomp
  , _nmod_poly_interpolate_nmod_vec_fast
  , nmod_poly_interpolate_nmod_vec_fast
  , _nmod_poly_interpolate_nmod_vec_newton
  , nmod_poly_interpolate_nmod_vec_newton
  , _nmod_poly_interpolate_nmod_vec_barycentric
  , nmod_poly_interpolate_nmod_vec_barycentric
  -- * Composition
  , _nmod_poly_compose_horner
  , nmod_poly_compose_horner
  --, _nmod_poly_compose_divconquer
  --, nmod_poly_compose_divconquer
  , _nmod_poly_compose
  , nmod_poly_compose
  -- * Taylor shift
  , _nmod_poly_taylor_shift_horner
  , nmod_poly_taylor_shift_horner
  , _nmod_poly_taylor_shift_convolution
  , nmod_poly_taylor_shift_convolution
  , _nmod_poly_taylor_shift
  , nmod_poly_taylor_shift
  -- * Modular composition
  , _nmod_poly_compose_mod_horner
  , nmod_poly_compose_mod_horner
  , _nmod_poly_compose_mod_brent_kung
  , nmod_poly_compose_mod_brent_kung
  , _nmod_poly_compose_mod_brent_kung_preinv
  , nmod_poly_compose_mod_brent_kung_preinv
  , _nmod_poly_reduce_matrix_mod_poly
  , _nmod_poly_precompute_matrix_worker
  , _nmod_poly_precompute_matrix
  , nmod_poly_precompute_matrix
  , _nmod_poly_compose_mod_brent_kung_precomp_preinv_worker
  , _nmod_poly_compose_mod_brent_kung_precomp_preinv
  , nmod_poly_compose_mod_brent_kung_precomp_preinv
  , _nmod_poly_compose_mod_brent_kung_vec_preinv
  , nmod_poly_compose_mod_brent_kung_vec_preinv
  , _nmod_poly_compose_mod_brent_kung_vec_preinv_threaded_pool
  , nmod_poly_compose_mod_brent_kung_vec_preinv_threaded_pool
  , nmod_poly_compose_mod_brent_kung_vec_preinv_threaded
  , _nmod_poly_compose_mod
  , nmod_poly_compose_mod
  -- * Greatest common divisor
  , _nmod_poly_gcd_euclidean
  , nmod_poly_gcd_euclidean
  , _nmod_poly_hgcd
  , _nmod_poly_gcd_hgcd
  , nmod_poly_gcd_hgcd
  , _nmod_poly_gcd
  , nmod_poly_gcd
  , _nmod_poly_xgcd_euclidean
  , nmod_poly_xgcd_euclidean
  , _nmod_poly_xgcd_hgcd
  , nmod_poly_xgcd_hgcd
  , _nmod_poly_xgcd
  , nmod_poly_xgcd
  , _nmod_poly_resultant_euclidean
  , nmod_poly_resultant_euclidean
  , _nmod_poly_resultant_hgcd
  , nmod_poly_resultant_hgcd
  , _nmod_poly_resultant
  , nmod_poly_resultant
  , _nmod_poly_gcdinv
  , nmod_poly_gcdinv
  , _nmod_poly_invmod
  , nmod_poly_invmod
  -- * Power series composition
  , _nmod_poly_discriminant
  , nmod_poly_discriminant
  -- * Power series composition
  , _nmod_poly_compose_series
  , nmod_poly_compose_series
  -- * Power series reversion
  , _nmod_poly_revert_series_lagrange
  , nmod_poly_revert_series_lagrange
  , _nmod_poly_revert_series_lagrange_fast
  , nmod_poly_revert_series_lagrange_fast
  , _nmod_poly_revert_series_newton
  , nmod_poly_revert_series_newton
  , _nmod_poly_revert_series
  , nmod_poly_revert_series
  -- * Square roots
  , _nmod_poly_invsqrt_series
  , nmod_poly_invsqrt_series
  , _nmod_poly_sqrt_series
  , nmod_poly_sqrt_series
  , _nmod_poly_sqrt
  , nmod_poly_sqrt
  -- * Power sums
  , _nmod_poly_power_sums_naive
  , nmod_poly_power_sums_naive
  , _nmod_poly_power_sums_schoenhage
  , nmod_poly_power_sums_schoenhage
  , _nmod_poly_power_sums
  , nmod_poly_power_sums
  , _nmod_poly_power_sums_to_poly_naive
  , nmod_poly_power_sums_to_poly_naive
  , _nmod_poly_power_sums_to_poly_schoenhage
  , nmod_poly_power_sums_to_poly_schoenhage
  , _nmod_poly_power_sums_to_poly
  , nmod_poly_power_sums_to_poly
  -- * Transcendental functions
  , _nmod_poly_log_series
  , nmod_poly_log_series
  , _nmod_poly_exp_series
  , _nmod_poly_exp_expinv_series
  , nmod_poly_exp_series
  , _nmod_poly_atan_series
  , nmod_poly_atan_series
  , _nmod_poly_atanh_series
  , nmod_poly_atanh_series
  , _nmod_poly_asin_series
  , nmod_poly_asin_series
  , _nmod_poly_asinh_series
  , nmod_poly_asinh_series
  , _nmod_poly_sin_series
  , nmod_poly_sin_series
  , _nmod_poly_cos_series
  , nmod_poly_cos_series
  , _nmod_poly_tan_series
  , nmod_poly_tan_series
  , _nmod_poly_sinh_series
  , nmod_poly_sinh_series
  , _nmod_poly_cosh_series
  , nmod_poly_cosh_series
  , _nmod_poly_tanh_series
  , nmod_poly_tanh_series
  -- * Products
  , _nmod_poly_product_roots_nmod_vec
  , nmod_poly_product_roots_nmod_vec
  , nmod_poly_find_distinct_nonzero_roots
  -- * Subproduct trees
  , _nmod_poly_tree_alloc
  , _nmod_poly_tree_free
  , _nmod_poly_tree_build
  -- * Inflation and deflation
  , nmod_poly_inflate
  , nmod_poly_deflate
  , nmod_poly_deflation
  -- * Chinese Remaindering
  , nmod_poly_multi_crt_init
  , nmod_poly_multi_crt_precompute
  , nmod_poly_multi_crt_precomp
  , nmod_poly_multi_crt
  , nmod_poly_multi_crt_clear
  , _nmod_poly_multi_crt_local_size
  , _nmod_poly_multi_crt_run
  -- * Berlekamp-Massey Algorithm
  , nmod_berlekamp_massey_init
  , nmod_berlekamp_massey_clear
  , nmod_berlekamp_massey_start_over
  , nmod_berlekamp_massey_set_prime
  , nmod_berlekamp_massey_add_points
  , nmod_berlekamp_massey_reduce
  , nmod_berlekamp_massey_point_count
  , nmod_berlekamp_massey_points
  , nmod_berlekamp_massey_V_poly
  , nmod_berlekamp_massey_R_poly
) where 

-- Univariate polynomials over integers mod n (word-sizen) ---------------------

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr )
import Foreign.Storable
import Foreign.Marshal ( free )

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.NMod
import Data.Number.Flint.NMod.Types
import Data.Number.Flint.ThreadPool

#include <flint/nmod_poly.h>

-- Types -----------------------------------------------------------------------

newNModPoly n = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> nmod_poly_init x n
  addForeignPtrFinalizer p_nmod_poly_clear x
  return $ NModPoly x

{-# INLINE withNModPoly #-}
withNModPoly (NModPoly x) f = do
  withForeignPtr x $ \px -> f px >>= return . (NModPoly x,)

{-# INLINE withNewNModPoly #-}
withNewNModPoly n f = do
  x <- newNModPoly n
  withNModPoly x $ \x -> f x

-- nmod_poly_crt_t -------------------------------------------------------------

data NModPolyMultiCRT = NModPolyCRT {-# UNPACK #-} !(ForeignPtr CNModPolyMultiCRT)
type CNModPolyMultiCRT = CFlint NModPolyMultiCRT

instance Storable CNModPolyMultiCRT where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size nmod_poly_multi_crt_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment nmod_poly_multi_crt_t}
  peek = undefined
  poke = undefined

-- nmod_berlekamp_massey_t -----------------------------------------------------

data NModBerlekampMassey = NModBerlekampMassey {-# UNPACK #-} !(ForeignPtr CNModBerlekampMassey)
type CNModBerlekampMassey = CFlint NModBerlekampMassey

instance Storable CNModBerlekampMassey where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size nmod_berlekamp_massey_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment nmod_berlekamp_massey_t}
  peek = undefined
  poke = undefined

newNModBerlekampMassey n = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> nmod_berlekamp_massey_init x n
  addForeignPtrFinalizer p_nmod_berlekamp_massey_clear x
  return $ NModBerlekampMassey x

{-# INLINE withNModBerlekampMassey #-}
withNModBerlekampMassey (NModBerlekampMassey x) f = do
  withForeignPtr x $ \px -> f px >>= return . (NModBerlekampMassey x,)
 
-- Helper functions ------------------------------------------------------------

-- | /signed_mpn_sub_n/ /res/ /op1/ /op2/ /n/ 
-- 
-- If @op1 >= op2@ return 0 and set @res@ to @op1 - op2@ else return 1 and
-- set @res@ to @op2 - op1@.
foreign import ccall "nmod_poly.h signed_mpn_sub_n"
  signed_mpn_sub_n :: Ptr CMp -> Ptr CMp -> Ptr CMp -> CLong -> IO CInt

-- Memory management -----------------------------------------------------------

-- | /nmod_poly_init/ /poly/ /n/ 
-- 
-- Initialises @poly@. It will have coefficients modulo~\`n\`.
foreign import ccall "nmod_poly.h nmod_poly_init"
  nmod_poly_init :: Ptr CNModPoly -> CMpLimb -> IO ()

-- | /nmod_poly_init_preinv/ /poly/ /n/ /ninv/ 
-- 
-- Initialises @poly@. It will have coefficients modulo~\`n\`. The caller
-- supplies a precomputed inverse limb generated by @n_preinvert_limb@.
foreign import ccall "nmod_poly.h nmod_poly_init_preinv"
  nmod_poly_init_preinv :: Ptr CNModPoly -> CMpLimb -> CMpLimb -> IO ()

-- | /nmod_poly_init_mod/ /poly/ /mod/ 
-- 
-- Initialises @poly@ using an already initialised modulus @mod@.
foreign import ccall "nmod_poly.h nmod_poly_init_mod"
  nmod_poly_init_mod :: Ptr CNModPoly -> Ptr CNMod -> IO ()

-- | /nmod_poly_init2/ /poly/ /n/ /alloc/ 
-- 
-- Initialises @poly@. It will have coefficients modulo~\`n\`. Up to
-- @alloc@ coefficients may be stored in @poly@.
foreign import ccall "nmod_poly.h nmod_poly_init2"
  nmod_poly_init2 :: Ptr CNModPoly -> CMpLimb -> CLong -> IO ()

-- | /nmod_poly_init2_preinv/ /poly/ /n/ /ninv/ /alloc/ 
-- 
-- Initialises @poly@. It will have coefficients modulo~\`n\`. The caller
-- supplies a precomputed inverse limb generated by @n_preinvert_limb@. Up
-- to @alloc@ coefficients may be stored in @poly@.
foreign import ccall "nmod_poly.h nmod_poly_init2_preinv"
  nmod_poly_init2_preinv :: Ptr CNModPoly -> CMpLimb -> CMpLimb -> CLong -> IO ()

-- | /nmod_poly_realloc/ /poly/ /alloc/ 
-- 
-- Reallocates @poly@ to the given length. If the current length is less
-- than @alloc@, the polynomial is truncated and normalised. If @alloc@ is
-- zero, the polynomial is cleared.
foreign import ccall "nmod_poly.h nmod_poly_realloc"
  nmod_poly_realloc :: Ptr CNModPoly -> CLong -> IO ()

-- | /nmod_poly_clear/ /poly/ 
-- 
-- Clears the polynomial and releases any memory it used. The polynomial
-- cannot be used again until it is initialised.
foreign import ccall "nmod_poly.h nmod_poly_clear"
  nmod_poly_clear :: Ptr CNModPoly -> IO ()

foreign import ccall "nmod_poly.h &nmod_poly_clear"
  p_nmod_poly_clear :: FunPtr (Ptr CNModPoly -> IO ())

-- | /nmod_poly_fit_length/ /poly/ /alloc/ 
-- 
-- Ensures @poly@ has space for at least @alloc@ coefficients. This
-- function only ever grows the allocated space, so no data loss can occur.
foreign import ccall "nmod_poly.h nmod_poly_fit_length"
  nmod_poly_fit_length :: Ptr CNModPoly -> CLong -> IO ()

-- | /_nmod_poly_normalise/ /poly/ 
-- 
-- Internal function for normalising a polynomial so that the top
-- coefficient, if there is one at all, is not zero.
foreign import ccall "nmod_poly.h _nmod_poly_normalise"
  _nmod_poly_normalise :: Ptr CNModPoly -> IO ()

-- Polynomial properties -------------------------------------------------------

-- | /nmod_poly_length/ /poly/ 
-- 
-- Returns the length of the polynomial @poly@. The zero polynomial has
-- length zero.
foreign import ccall "nmod_poly.h nmod_poly_length"
  nmod_poly_length :: Ptr CNModPoly -> IO CLong

-- | /nmod_poly_degree/ /poly/ 
-- 
-- Returns the degree of the polynomial @poly@. The zero polynomial is
-- deemed to have degree~\`-1\`.
foreign import ccall "nmod_poly.h nmod_poly_degree"
  nmod_poly_degree :: Ptr CNModPoly -> IO CLong

-- | /nmod_poly_modulus/ /poly/ 
-- 
-- Returns the modulus of the polynomial @poly@. This will be a positive
-- integer.
foreign import ccall "nmod_poly.h nmod_poly_modulus"
  nmod_poly_modulus :: Ptr CNModPoly -> IO CMpLimb

-- | /nmod_poly_max_bits/ /poly/ 
-- 
-- Returns the maximum number of bits of any coefficient of @poly@.
foreign import ccall "nmod_poly.h nmod_poly_max_bits"
  nmod_poly_max_bits :: Ptr CNModPoly -> IO CFBitCnt

-- Assignment and basic manipulation -------------------------------------------

-- | /nmod_poly_set/ /a/ /b/ 
-- 
-- Sets @a@ to a copy of @b@.
foreign import ccall "nmod_poly.h nmod_poly_set"
  nmod_poly_set :: Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- | /nmod_poly_swap/ /poly1/ /poly2/ 
-- 
-- Efficiently swaps @poly1@ and @poly2@ by swapping pointers internally.
foreign import ccall "nmod_poly.h nmod_poly_swap"
  nmod_poly_swap :: Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- | /nmod_poly_zero/ /res/ 
-- 
-- Sets @res@ to the zero polynomial.
foreign import ccall "nmod_poly.h nmod_poly_zero"
  nmod_poly_zero :: Ptr CNModPoly -> IO ()

-- | /nmod_poly_truncate/ /poly/ /len/ 
-- 
-- Truncates @poly@ to the given length and normalises it. If @len@ is
-- greater than the current length of @poly@, then nothing happens.
foreign import ccall "nmod_poly.h nmod_poly_truncate"
  nmod_poly_truncate :: Ptr CNModPoly -> CLong -> IO ()

-- | /nmod_poly_set_trunc/ /res/ /poly/ /n/ 
-- 
-- Notionally truncate @poly@ to length \(n\) and set @res@ to the result.
-- The result is normalised.
foreign import ccall "nmod_poly.h nmod_poly_set_trunc"
  nmod_poly_set_trunc :: Ptr CNModPoly -> Ptr CNModPoly -> CLong -> IO ()

-- | /_nmod_poly_reverse/ /output/ /input/ /len/ /m/ 
-- 
-- Sets @output@ to the reverse of @input@, which is of length @len@, but
-- thinking of it as a polynomial of length~@m@, notionally zero-padded if
-- necessary. The length~@m@ must be non-negative, but there are no other
-- restrictions. The polynomial @output@ must have space for @m@
-- coefficients. Supports aliasing of @output@ and @input@, but the
-- behaviour is undefined in case of partial overlap.
foreign import ccall "nmod_poly.h _nmod_poly_reverse"
  _nmod_poly_reverse :: Ptr CMp -> Ptr CMp -> CLong -> CLong -> IO ()

-- | /nmod_poly_reverse/ /output/ /input/ /m/ 
-- 
-- Sets @output@ to the reverse of @input@, thinking of it as a polynomial
-- of length~@m@, notionally zero-padded if necessary). The length~@m@ must
-- be non-negative, but there are no other restrictions. The output
-- polynomial will be set to length~@m@ and then normalised.
foreign import ccall "nmod_poly.h nmod_poly_reverse"
  nmod_poly_reverse :: Ptr CNModPoly -> Ptr CNModPoly -> CLong -> IO ()

-- Randomization ---------------------------------------------------------------

-- | /nmod_poly_randtest/ /poly/ /state/ /len/ 
-- 
-- Generates a random polynomial with length up to @len@.
foreign import ccall "nmod_poly.h nmod_poly_randtest"
  nmod_poly_randtest :: Ptr CNModPoly -> Ptr CFRandState -> CLong -> IO ()

-- | /nmod_poly_randtest_irreducible/ /poly/ /state/ /len/ 
-- 
-- Generates a random irreducible polynomial with length up to @len@.
foreign import ccall "nmod_poly.h nmod_poly_randtest_irreducible"
  nmod_poly_randtest_irreducible :: Ptr CNModPoly -> Ptr CFRandState -> CLong -> IO ()

-- | /nmod_poly_randtest_monic/ /poly/ /state/ /len/ 
-- 
-- Generates a random monic polynomial with length @len@.
foreign import ccall "nmod_poly.h nmod_poly_randtest_monic"
  nmod_poly_randtest_monic :: Ptr CNModPoly -> Ptr CFRandState -> CLong -> IO ()

-- | /nmod_poly_randtest_monic_irreducible/ /poly/ /state/ /len/ 
-- 
-- Generates a random monic irreducible polynomial with length @len@.
foreign import ccall "nmod_poly.h nmod_poly_randtest_monic_irreducible"
  nmod_poly_randtest_monic_irreducible :: Ptr CNModPoly -> Ptr CFRandState -> CLong -> IO ()

-- | /nmod_poly_randtest_monic_primitive/ /poly/ /state/ /len/ 
-- 
-- Generates a random monic irreducible primitive polynomial with length
-- @len@.
foreign import ccall "nmod_poly.h nmod_poly_randtest_monic_primitive"
  nmod_poly_randtest_monic_primitive :: Ptr CNModPoly -> Ptr CFRandState -> CLong -> IO ()

-- | /nmod_poly_randtest_trinomial/ /poly/ /state/ /len/ 
-- 
-- Generates a random monic trinomial of length @len@.
foreign import ccall "nmod_poly.h nmod_poly_randtest_trinomial"
  nmod_poly_randtest_trinomial :: Ptr CNModPoly -> Ptr CFRandState -> CLong -> IO ()

-- | /nmod_poly_randtest_trinomial_irreducible/ /poly/ /state/ /len/ /max_attempts/ 
-- 
-- Attempts to set @poly@ to a monic irreducible trinomial of length @len@.
-- It will generate up to @max_attempts@ trinomials in attempt to find an
-- irreducible one. If @max_attempts@ is @0@, then it will keep generating
-- trinomials until an irreducible one is found. Returns \(1\) if one is
-- found and \(0\) otherwise.
foreign import ccall "nmod_poly.h nmod_poly_randtest_trinomial_irreducible"
  nmod_poly_randtest_trinomial_irreducible :: Ptr CNModPoly -> Ptr CFRandState -> CLong -> CLong -> IO CInt

-- | /nmod_poly_randtest_pentomial/ /poly/ /state/ /len/ 
-- 
-- Generates a random monic pentomial of length @len@.
foreign import ccall "nmod_poly.h nmod_poly_randtest_pentomial"
  nmod_poly_randtest_pentomial :: Ptr CNModPoly -> Ptr CFRandState -> CLong -> IO ()

-- | /nmod_poly_randtest_pentomial_irreducible/ /poly/ /state/ /len/ /max_attempts/ 
-- 
-- Attempts to set @poly@ to a monic irreducible pentomial of length @len@.
-- It will generate up to @max_attempts@ pentomials in attempt to find an
-- irreducible one. If @max_attempts@ is @0@, then it will keep generating
-- pentomials until an irreducible one is found. Returns \(1\) if one is
-- found and \(0\) otherwise.
foreign import ccall "nmod_poly.h nmod_poly_randtest_pentomial_irreducible"
  nmod_poly_randtest_pentomial_irreducible :: Ptr CNModPoly -> Ptr CFRandState -> CLong -> CLong -> IO CInt

-- | /nmod_poly_randtest_sparse_irreducible/ /poly/ /state/ /len/ 
-- 
-- Attempts to set @poly@ to a sparse, monic irreducible polynomial with
-- length @len@. It attempts to find an irreducible trinomial. If that does
-- not succeed, it attempts to find a irreducible pentomial. If that fails,
-- then @poly@ is just set to a random monic irreducible polynomial.
foreign import ccall "nmod_poly.h nmod_poly_randtest_sparse_irreducible"
  nmod_poly_randtest_sparse_irreducible :: Ptr CNModPoly -> Ptr CFRandState -> CLong -> IO ()

-- Getting and setting coefficients --------------------------------------------

-- | /nmod_poly_get_coeff_ui/ /poly/ /j/ 
-- 
-- Returns the coefficient of @poly@ at index~@j@, where coefficients are
-- numbered with zero being the constant coefficient, and returns it as an
-- @ulong@. If @j@ refers to a coefficient beyond the end of @poly@, zero
-- is returned.
foreign import ccall "nmod_poly.h nmod_poly_get_coeff_ui"
  nmod_poly_get_coeff_ui :: Ptr CNModPoly -> CLong -> IO CULong

-- | /nmod_poly_set_coeff_ui/ /poly/ /j/ /c/ 
-- 
-- Sets the coefficient of @poly@ at index @j@, where coefficients are
-- numbered with zero being the constant coefficient, to the value @c@
-- reduced modulo the modulus of @poly@. If @j@ refers to a coefficient
-- beyond the current end of @poly@, the polynomial is first resized, with
-- intervening coefficients being set to zero.
foreign import ccall "nmod_poly.h nmod_poly_set_coeff_ui"
  nmod_poly_set_coeff_ui :: Ptr CNModPoly -> CLong -> CULong -> IO ()

-- Input and output ------------------------------------------------------------

-- | /nmod_poly_get_str/ /poly/ 
-- 
-- Writes @poly@ to a string representation. The format is as described for
-- @nmod_poly_print@. The string must be freed by the user when finished.
-- For this it is sufficient to call @flint_free@.
foreign import ccall "nmod_poly.h nmod_poly_get_str"
  nmod_poly_get_str :: Ptr CNModPoly -> IO CString

-- | /nmod_poly_get_str_pretty/ /poly/ /x/ 
-- 
-- Writes @poly@ to a pretty string representation. The format is as
-- described for @nmod_poly_print_pretty@. The string must be freed by the
-- user when finished. For this it is sufficient to call @flint_free@.
-- 
-- It is assumed that the top coefficient is non-zero.
foreign import ccall "nmod_poly.h nmod_poly_get_str_pretty"
  nmod_poly_get_str_pretty :: Ptr CNModPoly -> CString -> IO CString

-- | /nmod_poly_set_str/ /poly/ /s/ 
-- 
-- Reads @poly@ from a string @s@. The format is as described for
-- @nmod_poly_print@. If a polynomial in the correct format is read, a
-- positive value is returned, otherwise a non-positive value is returned.
foreign import ccall "nmod_poly.h nmod_poly_set_str"
  nmod_poly_set_str :: Ptr CNModPoly -> CString -> IO CInt

-- | /nmod_poly_print/ /a/ 
-- 
-- Prints the polynomial to @stdout@. The length is printed, followed by a
-- space, then the modulus. If the length is zero this is all that is
-- printed, otherwise two spaces followed by a space separated list of
-- coefficients is printed, beginning with the constant coefficient.
-- 
-- In case of success, returns a positive value. In case of failure,
-- returns a non-positive value.
nmod_poly_print :: Ptr CNModPoly -> IO CInt
nmod_poly_print a = printCStr nmod_poly_get_str a

-- | /nmod_poly_print_pretty/ /a/ /x/ 
-- 
-- Prints the polynomial to @stdout@ using the string @x@ to represent the
-- indeterminate.
-- 
-- It is assumed that the top coefficient is non-zero.
-- 
-- In case of success, returns a positive value. In case of failure,
-- returns a non-positive value.
nmod_poly_print_pretty :: Ptr CNModPoly -> CString -> IO CInt
nmod_poly_print_pretty a x = printCStr (flip nmod_poly_get_str_pretty x) a
  
-- | /nmod_poly_fread/ /f/ /poly/ 
-- 
-- Reads @poly@ from the file stream @f@. If this is a file that has just
-- been written, the file should be closed then opened again. The format is
-- as described for @nmod_poly_print@. If a polynomial in the correct
-- format is read, a positive value is returned, otherwise a non-positive
-- value is returned.
foreign import ccall "nmod_poly.h nmod_poly_fread"
  nmod_poly_fread :: Ptr CFile -> Ptr CNModPoly -> IO CInt

-- | /nmod_poly_fprint/ /f/ /poly/ 
-- 
-- Writes a polynomial to the file stream @f@. If this is a file then the
-- file should be closed and reopened before being read. The format is as
-- described for @nmod_poly_print@. If the polynomial is written correctly,
-- a positive value is returned, otherwise a non-positive value is
-- returned.
-- 
-- In case of success, returns a positive value. In case of failure,
-- returns a non-positive value.
foreign import ccall "nmod_poly.h nmod_poly_fprint"
  nmod_poly_fprint :: Ptr CFile -> Ptr CNModPoly -> IO CInt

-- | /nmod_poly_fprint_pretty/ /f/ /poly/ /x/ 
-- 
-- Writes a polynomial to the file stream @f@. If this is a file then the
-- file should be closed and reopened before being read. The format is as
-- described for @nmod_poly_print_pretty@. If the polynomial is written
-- correctly, a positive value is returned, otherwise a non-positive value
-- is returned.
-- 
-- It is assumed that the top coefficient is non-zero.
-- 
-- In case of success, returns a positive value. In case of failure,
-- returns a non-positive value.
foreign import ccall "nmod_poly.h nmod_poly_fprint_pretty"
  nmod_poly_fprint_pretty :: Ptr CFile -> Ptr CNModPoly -> CString -> IO CInt

-- | /nmod_poly_read/ /poly/ 
-- 
-- Read @poly@ from @stdin@. The format is as described for
-- @nmod_poly_print@. If a polynomial in the correct format is read, a
-- positive value is returned, otherwise a non-positive value is returned.
foreign import ccall "nmod_poly.h nmod_poly_read"
  nmod_poly_read :: Ptr CNModPoly -> IO CInt

-- Comparison ------------------------------------------------------------------

-- | /nmod_poly_equal/ /a/ /b/ 
-- 
-- Returns~\`1\` if the polynomials are equal, otherwise~\`0\`.
foreign import ccall "nmod_poly.h nmod_poly_equal"
  nmod_poly_equal :: Ptr CNModPoly -> Ptr CNModPoly -> IO CInt

-- | /nmod_poly_equal_trunc/ /poly1/ /poly2/ /n/ 
-- 
-- Notionally truncate @poly1@ and @poly2@ to length \(n\) and return \(1\)
-- if the truncations are equal, otherwise return \(0\).
foreign import ccall "nmod_poly.h nmod_poly_equal_trunc"
  nmod_poly_equal_trunc :: Ptr CNModPoly -> Ptr CNModPoly -> CLong -> IO CInt

-- | /nmod_poly_is_zero/ /poly/ 
-- 
-- Returns~\`1\` if the polynomial @poly@ is the zero polynomial, otherwise
-- returns~\`0\`.
foreign import ccall "nmod_poly.h nmod_poly_is_zero"
  nmod_poly_is_zero :: Ptr CNModPoly -> IO CInt

-- | /nmod_poly_is_one/ /poly/ 
-- 
-- Returns~\`1\` if the polynomial @poly@ is the constant polynomial 1,
-- otherwise returns~\`0\`.
foreign import ccall "nmod_poly.h nmod_poly_is_one"
  nmod_poly_is_one :: Ptr CNModPoly -> IO CInt

-- Shifting --------------------------------------------------------------------

-- | /_nmod_poly_shift_left/ /res/ /poly/ /len/ /k/ 
-- 
-- Sets @(res, len + k)@ to @(poly, len)@ shifted left by @k@ coefficients.
-- Assumes that @res@ has space for @len + k@ coefficients.
foreign import ccall "nmod_poly.h _nmod_poly_shift_left"
  _nmod_poly_shift_left :: Ptr CMp -> Ptr CMp -> CLong -> CLong -> IO ()

-- | /nmod_poly_shift_left/ /res/ /poly/ /k/ 
-- 
-- Sets @res@ to @poly@ shifted left by @k@ coefficients, i.e.multiplied by
-- \(x^k\).
foreign import ccall "nmod_poly.h nmod_poly_shift_left"
  nmod_poly_shift_left :: Ptr CNModPoly -> Ptr CNModPoly -> CLong -> IO ()

-- | /_nmod_poly_shift_right/ /res/ /poly/ /len/ /k/ 
-- 
-- Sets @(res, len - k)@ to @(poly, len)@ shifted left by @k@ coefficients.
-- It is assumed that @k \<= len@ and that @res@ has space for at least
-- @len - k@ coefficients.
foreign import ccall "nmod_poly.h _nmod_poly_shift_right"
  _nmod_poly_shift_right :: Ptr CMp -> Ptr CMp -> CLong -> CLong -> IO ()

-- | /nmod_poly_shift_right/ /res/ /poly/ /k/ 
-- 
-- Sets @res@ to @poly@ shifted right by @k@ coefficients, i.e.divide by
-- \(x^k\) and throws away the remainder. If @k@ is greater than or equal
-- to the length of @poly@, the result is the zero polynomial.
foreign import ccall "nmod_poly.h nmod_poly_shift_right"
  nmod_poly_shift_right :: Ptr CNModPoly -> Ptr CNModPoly -> CLong -> IO ()

-- Addition and subtraction ----------------------------------------------------

-- | /_nmod_poly_add/ /res/ /poly1/ /len1/ /poly2/ /len2/ /mod/ 
-- 
-- Sets @res@ to the sum of @(poly1, len1)@ and @(poly2, len2)@. There are
-- no restrictions on the lengths.
foreign import ccall "nmod_poly.h _nmod_poly_add"
  _nmod_poly_add :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_add/ /res/ /poly1/ /poly2/ 
-- 
-- Sets @res@ to the sum of @poly1@ and @poly2@.
foreign import ccall "nmod_poly.h nmod_poly_add"
  nmod_poly_add :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- | /nmod_poly_add_series/ /res/ /poly1/ /poly2/ /n/ 
-- 
-- Notionally truncate @poly1@ and @poly2@ to length \(n\) and set @res@ to
-- the sum.
foreign import ccall "nmod_poly.h nmod_poly_add_series"
  nmod_poly_add_series :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> CLong -> IO ()

-- | /_nmod_poly_sub/ /res/ /poly1/ /len1/ /poly2/ /len2/ /mod/ 
-- 
-- Sets @res@ to the difference of @(poly1, len1)@ and @(poly2, len2)@.
-- There are no restrictions on the lengths.
foreign import ccall "nmod_poly.h _nmod_poly_sub"
  _nmod_poly_sub :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_sub/ /res/ /poly1/ /poly2/ 
-- 
-- Sets @res@ to the difference of @poly1@ and @poly2@.
foreign import ccall "nmod_poly.h nmod_poly_sub"
  nmod_poly_sub :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- | /nmod_poly_sub_series/ /res/ /poly1/ /poly2/ /n/ 
-- 
-- Notionally truncate @poly1@ and @poly2@ to length \(n\) and set @res@ to
-- the difference.
foreign import ccall "nmod_poly.h nmod_poly_sub_series"
  nmod_poly_sub_series :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> CLong -> IO ()

-- | /nmod_poly_neg/ /res/ /poly/ 
-- 
-- Sets @res@ to the negation of @poly@.
foreign import ccall "nmod_poly.h nmod_poly_neg"
  nmod_poly_neg :: Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- Scalar multiplication and division ------------------------------------------

-- | /nmod_poly_scalar_mul_nmod/ /res/ /poly/ /c/ 
-- 
-- Sets @res@ to @(poly, len)@ multiplied by~\`c\`, where~\`c\` is reduced
-- modulo the modulus of @poly@.
foreign import ccall "nmod_poly.h nmod_poly_scalar_mul_nmod"
  nmod_poly_scalar_mul_nmod :: Ptr CNModPoly -> Ptr CNModPoly -> CULong -> IO ()

-- | /_nmod_poly_make_monic/ /output/ /input/ /len/ /mod/ 
-- 
-- Sets @output@ to be the scalar multiple of @input@ of length @len > 0@
-- that has leading coefficient one, if such a polynomial exists. If the
-- leading coefficient of @input@ is not invertible, @output@ is set to the
-- multiple of @input@ whose leading coefficient is the greatest common
-- divisor of the leading coefficient and the modulus of @input@.
foreign import ccall "nmod_poly.h _nmod_poly_make_monic"
  _nmod_poly_make_monic :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_make_monic/ /output/ /input/ 
-- 
-- Sets @output@ to be the scalar multiple of @input@ with leading
-- coefficient one, if such a polynomial exists. If @input@ is zero an
-- exception is raised. If the leading coefficient of @input@ is not
-- invertible, @output@ is set to the multiple of @input@ whose leading
-- coefficient is the greatest common divisor of the leading coefficient
-- and the modulus of @input@.
foreign import ccall "nmod_poly.h nmod_poly_make_monic"
  nmod_poly_make_monic :: Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- Bit packing and unpacking ---------------------------------------------------

-- | /_nmod_poly_bit_pack/ /res/ /poly/ /len/ /bits/ 
-- 
-- Packs @len@ coefficients of @poly@ into fields of the given number of
-- bits in the large integer @res@, i.e.evaluates @poly@ at @2^bits@ and
-- store the result in @res@. Assumes @len > 0@ and @bits > 0@. Also
-- assumes that no coefficient of @poly@ is bigger than @bits\/2@ bits. We
-- also assume @bits \< 3 * FLINT_BITS@.
foreign import ccall "nmod_poly.h _nmod_poly_bit_pack"
  _nmod_poly_bit_pack :: Ptr CMp -> Ptr CMp -> CLong -> CFBitCnt -> IO ()

-- | /_nmod_poly_bit_unpack/ /res/ /len/ /mpn/ /bits/ /mod/ 
-- 
-- Unpacks @len@ coefficients stored in the big integer @mpn@ in bit fields
-- of the given number of bits, reduces them modulo the given modulus, then
-- stores them in the polynomial @res@. We assume @len > 0@ and
-- @3 * FLINT_BITS > bits > 0@. There are no restrictions on the size of
-- the actual coefficients as stored within the bitfields.
foreign import ccall "nmod_poly.h _nmod_poly_bit_unpack"
  _nmod_poly_bit_unpack :: Ptr CMp -> CLong -> Ptr CMp -> CULong -> Ptr CNMod -> IO ()

-- | /nmod_poly_bit_pack/ /f/ /poly/ /bit_size/ 
-- 
-- Packs @poly@ into bitfields of size @bit_size@, writing the result to
-- @f@.
foreign import ccall "nmod_poly.h nmod_poly_bit_pack"
  nmod_poly_bit_pack :: Ptr CFmpz -> Ptr CNModPoly -> CFBitCnt -> IO ()

-- | /nmod_poly_bit_unpack/ /poly/ /f/ /bit_size/ 
-- 
-- Unpacks the polynomial from fields of size @bit_size@ as represented by
-- the integer @f@.
foreign import ccall "nmod_poly.h nmod_poly_bit_unpack"
  nmod_poly_bit_unpack :: Ptr CNModPoly -> Ptr CFmpz -> CFBitCnt -> IO ()

-- | /_nmod_poly_KS2_pack1/ /res/ /op/ /n/ /s/ /b/ /k/ /r/ 
-- 
-- Same as @_nmod_poly_KS2_pack@, but requires @b \<= FLINT_BITS@.
foreign import ccall "nmod_poly.h _nmod_poly_KS2_pack1"
  _nmod_poly_KS2_pack1 :: Ptr CMp -> Ptr CMp -> CLong -> CLong -> CULong -> CULong -> CLong -> IO ()

-- | /_nmod_poly_KS2_pack/ /res/ /op/ /n/ /s/ /b/ /k/ /r/ 
-- 
-- Bit packing routine used by KS2 and KS4 multiplication.
foreign import ccall "nmod_poly.h _nmod_poly_KS2_pack"
  _nmod_poly_KS2_pack :: Ptr CMp -> Ptr CMp -> CLong -> CLong -> CULong -> CULong -> CLong -> IO ()

-- | /_nmod_poly_KS2_unpack1/ /res/ /op/ /n/ /b/ /k/ 
-- 
-- Same as @_nmod_poly_KS2_unpack@, but requires @b \<= FLINT_BITS@ (i.e.
-- writes one word per coefficient).
foreign import ccall "nmod_poly.h _nmod_poly_KS2_unpack1"
  _nmod_poly_KS2_unpack1 :: Ptr CMp -> Ptr CMp -> CLong -> CULong -> CULong -> IO ()

-- | /_nmod_poly_KS2_unpack2/ /res/ /op/ /n/ /b/ /k/ 
-- 
-- Same as @_nmod_poly_KS2_unpack@, but requires
-- @FLINT_BITS \< b \<= 2 * FLINT_BITS@ (i.e. writes two words per
-- coefficient).
foreign import ccall "nmod_poly.h _nmod_poly_KS2_unpack2"
  _nmod_poly_KS2_unpack2 :: Ptr CMp -> Ptr CMp -> CLong -> CULong -> CULong -> IO ()

-- | /_nmod_poly_KS2_unpack3/ /res/ /op/ /n/ /b/ /k/ 
-- 
-- Same as @_nmod_poly_KS2_unpack@, but requires
-- @2 * FLINT_BITS \< b \< 3 * FLINT_BITS@ (i.e. writes three words per
-- coefficient).
foreign import ccall "nmod_poly.h _nmod_poly_KS2_unpack3"
  _nmod_poly_KS2_unpack3 :: Ptr CMp -> Ptr CMp -> CLong -> CULong -> CULong -> IO ()

-- | /_nmod_poly_KS2_unpack/ /res/ /op/ /n/ /b/ /k/ 
-- 
-- Bit unpacking code used by KS2 and KS4 multiplication.
foreign import ccall "nmod_poly.h _nmod_poly_KS2_unpack"
  _nmod_poly_KS2_unpack :: Ptr CMp -> Ptr CMp -> CLong -> CULong -> CULong -> IO ()

-- KS2\/KS4 Reduction ----------------------------------------------------------

-- | /_nmod_poly_KS2_reduce/ /res/ /s/ /op/ /n/ /w/ /mod/ 
-- 
-- Reduction code used by KS2 and KS4 multiplication.
foreign import ccall "nmod_poly.h _nmod_poly_KS2_reduce"
  _nmod_poly_KS2_reduce :: Ptr CMp -> CLong -> Ptr CMp -> CLong -> CULong -> Ptr CNMod -> IO ()

-- | /_nmod_poly_KS2_recover_reduce1/ /res/ /s/ /op1/ /op2/ /n/ /b/ /mod/ 
-- 
-- Same as @_nmod_poly_KS2_recover_reduce@, but requires
-- @0 \< 2 * b \<= FLINT_BITS@.
foreign import ccall "nmod_poly.h _nmod_poly_KS2_recover_reduce1"
  _nmod_poly_KS2_recover_reduce1 :: Ptr CMp -> CLong -> Ptr CMp -> Ptr CMp -> CLong -> CULong -> Ptr CNMod -> IO ()

-- | /_nmod_poly_KS2_recover_reduce2/ /res/ /s/ /op1/ /op2/ /n/ /b/ /mod/ 
-- 
-- Same as @_nmod_poly_KS2_recover_reduce@, but requires
-- @FLINT_BITS \< 2 * b \< 2*FLINT_BITS@.
foreign import ccall "nmod_poly.h _nmod_poly_KS2_recover_reduce2"
  _nmod_poly_KS2_recover_reduce2 :: Ptr CMp -> CLong -> Ptr CMp -> Ptr CMp -> CLong -> CULong -> Ptr CNMod -> IO ()

-- | /_nmod_poly_KS2_recover_reduce2b/ /res/ /s/ /op1/ /op2/ /n/ /b/ /mod/ 
-- 
-- Same as @_nmod_poly_KS2_recover_reduce@, but requires @b == FLINT_BITS@.
foreign import ccall "nmod_poly.h _nmod_poly_KS2_recover_reduce2b"
  _nmod_poly_KS2_recover_reduce2b :: Ptr CMp -> CLong -> Ptr CMp -> Ptr CMp -> CLong -> CULong -> Ptr CNMod -> IO ()

-- | /_nmod_poly_KS2_recover_reduce3/ /res/ /s/ /op1/ /op2/ /n/ /b/ /mod/ 
-- 
-- Same as @_nmod_poly_KS2_recover_reduce@, but requires
-- @2 * FLINT_BITS \< 2 * b \<= 3 * FLINT_BITS@.
foreign import ccall "nmod_poly.h _nmod_poly_KS2_recover_reduce3"
  _nmod_poly_KS2_recover_reduce3 :: Ptr CMp -> CLong -> Ptr CMp -> Ptr CMp -> CLong -> CULong -> Ptr CNMod -> IO ()

-- | /_nmod_poly_KS2_recover_reduce/ /res/ /s/ /op1/ /op2/ /n/ /b/ /mod/ 
-- 
-- Reduction code used by KS4 multiplication.
foreign import ccall "nmod_poly.h _nmod_poly_KS2_recover_reduce"
  _nmod_poly_KS2_recover_reduce :: Ptr CMp -> CLong -> Ptr CMp -> Ptr CMp -> CLong -> CULong -> Ptr CNMod -> IO ()

-- Multiplication --------------------------------------------------------------

-- | /_nmod_poly_mul_classical/ /res/ /poly1/ /len1/ /poly2/ /len2/ /mod/ 
-- 
-- Sets @(res, len1 + len2 - 1)@ to the product of @(poly1, len1)@ and
-- @(poly2, len2)@. Assumes @len1 >= len2 > 0@. Aliasing of inputs and
-- output is not permitted.
foreign import ccall "nmod_poly.h _nmod_poly_mul_classical"
  _nmod_poly_mul_classical :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_mul_classical/ /res/ /poly1/ /poly2/ 
-- 
-- Sets @res@ to the product of @poly1@ and @poly2@.
foreign import ccall "nmod_poly.h nmod_poly_mul_classical"
  nmod_poly_mul_classical :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- | /_nmod_poly_mullow_classical/ /res/ /poly1/ /len1/ /poly2/ /len2/ /trunc/ /mod/ 
-- 
-- Sets @res@ to the lower @trunc@ coefficients of the product of
-- @(poly1, len1)@ and @(poly2, len2)@. Assumes that @len1 >= len2 > 0@ and
-- @trunc > 0@. Aliasing of inputs and output is not permitted.
foreign import ccall "nmod_poly.h _nmod_poly_mullow_classical"
  _nmod_poly_mullow_classical :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_mullow_classical/ /res/ /poly1/ /poly2/ /trunc/ 
-- 
-- Sets @res@ to the lower @trunc@ coefficients of the product of @poly1@
-- and @poly2@.
foreign import ccall "nmod_poly.h nmod_poly_mullow_classical"
  nmod_poly_mullow_classical :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> CLong -> IO ()

-- | /_nmod_poly_mulhigh_classical/ /res/ /poly1/ /len1/ /poly2/ /len2/ /start/ /mod/ 
-- 
-- Computes the product of @(poly1, len1)@ and @(poly2, len2)@ and writes
-- the coefficients from @start@ onwards into the high coefficients of
-- @res@, the remaining coefficients being arbitrary but reduced. Assumes
-- that @len1 >= len2 > 0@. Aliasing of inputs and output is not permitted.
foreign import ccall "nmod_poly.h _nmod_poly_mulhigh_classical"
  _nmod_poly_mulhigh_classical :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_mulhigh_classical/ /res/ /poly1/ /poly2/ /start/ 
-- 
-- Computes the product of @poly1@ and @poly2@ and writes the coefficients
-- from @start@ onwards into the high coefficients of @res@, the remaining
-- coefficients being arbitrary but reduced.
foreign import ccall "nmod_poly.h nmod_poly_mulhigh_classical"
  nmod_poly_mulhigh_classical :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> CLong -> IO ()

-- | /_nmod_poly_mul_KS/ /out/ /in1/ /len1/ /in2/ /len2/ /bits/ /mod/ 
-- 
-- Sets @res@ to the product of @in1@ and @in2@ assuming the output
-- coefficients are at most the given number of bits wide. If @bits@ is set
-- to \(0\) an appropriate value is computed automatically. Assumes that
-- @len1 >= len2 > 0@.
foreign import ccall "nmod_poly.h _nmod_poly_mul_KS"
  _nmod_poly_mul_KS :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> CFBitCnt -> Ptr CNMod -> IO ()

-- | /nmod_poly_mul_KS/ /res/ /poly1/ /poly2/ /bits/ 
-- 
-- Sets @res@ to the product of @poly1@ and @poly2@ assuming the output
-- coefficients are at most the given number of bits wide. If @bits@ is set
-- to \(0\) an appropriate value is computed automatically.
foreign import ccall "nmod_poly.h nmod_poly_mul_KS"
  nmod_poly_mul_KS :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> CFBitCnt -> IO ()

-- | /_nmod_poly_mul_KS2/ /res/ /op1/ /n1/ /op2/ /n2/ /mod/ 
-- 
-- Sets @res@ to the product of @op1@ and @op2@. Assumes that
-- @len1 >= len2 > 0@.
foreign import ccall "nmod_poly.h _nmod_poly_mul_KS2"
  _nmod_poly_mul_KS2 :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_mul_KS2/ /res/ /poly1/ /poly2/ 
-- 
-- Sets @res@ to the product of @poly1@ and @poly2@.
foreign import ccall "nmod_poly.h nmod_poly_mul_KS2"
  nmod_poly_mul_KS2 :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- | /_nmod_poly_mul_KS4/ /res/ /op1/ /n1/ /op2/ /n2/ /mod/ 
-- 
-- Sets @res@ to the product of @op1@ and @op2@. Assumes that
-- @len1 >= len2 > 0@.
foreign import ccall "nmod_poly.h _nmod_poly_mul_KS4"
  _nmod_poly_mul_KS4 :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_mul_KS4/ /res/ /poly1/ /poly2/ 
-- 
-- Sets @res@ to the product of @poly1@ and @poly2@.
foreign import ccall "nmod_poly.h nmod_poly_mul_KS4"
  nmod_poly_mul_KS4 :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- | /_nmod_poly_mullow_KS/ /out/ /in1/ /len1/ /in2/ /len2/ /bits/ /n/ /mod/ 
-- 
-- Sets @out@ to the low \(n\) coefficients of @in1@ of length @len1@ times
-- @in2@ of length @len2@. The output must have space for @n@ coefficients.
-- We assume that @len1 >= len2 > 0@ and that @0 \< n \<= len1 + len2 - 1@.
foreign import ccall "nmod_poly.h _nmod_poly_mullow_KS"
  _nmod_poly_mullow_KS :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> CFBitCnt -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_mullow_KS/ /res/ /poly1/ /poly2/ /bits/ /n/ 
-- 
-- Set @res@ to the low \(n\) coefficients of @in1@ of length @len1@ times
-- @in2@ of length @len2@.
foreign import ccall "nmod_poly.h nmod_poly_mullow_KS"
  nmod_poly_mullow_KS :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> CFBitCnt -> CLong -> IO ()

-- | /_nmod_poly_mul/ /res/ /poly1/ /len1/ /poly2/ /len2/ /mod/ 
-- 
-- Sets @res@ to the product of @poly1@ of length @len1@ and @poly2@ of
-- length @len2@. Assumes @len1 >= len2 > 0@. No aliasing is permitted
-- between the inputs and the output.
foreign import ccall "nmod_poly.h _nmod_poly_mul"
  _nmod_poly_mul :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_mul/ /res/ /poly/ /poly2/ 
-- 
-- Sets @res@ to the product of @poly1@ and @poly2@.
foreign import ccall "nmod_poly.h nmod_poly_mul"
  nmod_poly_mul :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- | /_nmod_poly_mullow/ /res/ /poly1/ /len1/ /poly2/ /len2/ /n/ /mod/ 
-- 
-- Sets @res@ to the first @n@ coefficients of the product of @poly1@ of
-- length @len1@ and @poly2@ of length @len2@. It is assumed that
-- @0 \< n \<= len1 + len2 - 1@ and that @len1 >= len2 > 0@. No aliasing of
-- inputs and output is permitted.
foreign import ccall "nmod_poly.h _nmod_poly_mullow"
  _nmod_poly_mullow :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_mullow/ /res/ /poly1/ /poly2/ /trunc/ 
-- 
-- Sets @res@ to the first @trunc@ coefficients of the product of @poly1@
-- and @poly2@.
foreign import ccall "nmod_poly.h nmod_poly_mullow"
  nmod_poly_mullow :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> CLong -> IO ()

-- | /_nmod_poly_mulhigh/ /res/ /poly1/ /len1/ /poly2/ /len2/ /n/ /mod/ 
-- 
-- Sets all but the low \(n\) coefficients of @res@ to the corresponding
-- coefficients of the product of @poly1@ of length @len1@ and @poly2@ of
-- length @len2@, the other coefficients being arbitrary. It is assumed
-- that @len1 >= len2 > 0@ and that @0 \< n \<= len1 + len2 - 1@. Aliasing
-- of inputs and output is not permitted.
foreign import ccall "nmod_poly.h _nmod_poly_mulhigh"
  _nmod_poly_mulhigh :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_mulhigh/ /res/ /poly1/ /poly2/ /n/ 
-- 
-- Sets all but the low \(n\) coefficients of @res@ to the corresponding
-- coefficients of the product of @poly1@ and @poly2@, the remaining
-- coefficients being arbitrary.
foreign import ccall "nmod_poly.h nmod_poly_mulhigh"
  nmod_poly_mulhigh :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> CLong -> IO ()

-- | /_nmod_poly_mulmod/ /res/ /poly1/ /len1/ /poly2/ /len2/ /f/ /lenf/ /mod/ 
-- 
-- Sets @res@ to the remainder of the product of @poly1@ and @poly2@ upon
-- polynomial division by @f@.
-- 
-- It is required that @len1 + len2 - lenf > 0@, which is equivalent to
-- requiring that the result will actually be reduced. Otherwise, simply
-- use @_nmod_poly_mul@ instead.
-- 
-- Aliasing of @f@ and @res@ is not permitted.
foreign import ccall "nmod_poly.h _nmod_poly_mulmod"
  _nmod_poly_mulmod :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_mulmod/ /res/ /poly1/ /poly2/ /f/ 
-- 
-- Sets @res@ to the remainder of the product of @poly1@ and @poly2@ upon
-- polynomial division by @f@.
foreign import ccall "nmod_poly.h nmod_poly_mulmod"
  nmod_poly_mulmod :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- | /_nmod_poly_mulmod_preinv/ /res/ /poly1/ /len1/ /poly2/ /len2/ /f/ /lenf/ /finv/ /lenfinv/ /mod/ 
-- 
-- Sets @res@ to the remainder of the product of @poly1@ and @poly2@ upon
-- polynomial division by @f@.
-- 
-- It is required that @finv@ is the inverse of the reverse of @f@ mod
-- @x^lenf@. It is required that @len1 + len2 - lenf > 0@, which is
-- equivalent to requiring that the result will actually be reduced. It is
-- required that @len1 \< lenf@ and @len2 \< lenf@. Otherwise, simply use
-- @_nmod_poly_mul@ instead.
-- 
-- Aliasing of @\`res@ with any of the inputs is not permitted.
foreign import ccall "nmod_poly.h _nmod_poly_mulmod_preinv"
  _nmod_poly_mulmod_preinv :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_mulmod_preinv/ /res/ /poly1/ /poly2/ /f/ /finv/ 
-- 
-- Sets @res@ to the remainder of the product of @poly1@ and @poly2@ upon
-- polynomial division by @f@. @finv@ is the inverse of the reverse of @f@.
-- It is required that @poly1@ and @poly2@ are reduced modulo @f@.
foreign import ccall "nmod_poly.h nmod_poly_mulmod_preinv"
  nmod_poly_mulmod_preinv :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- Powering --------------------------------------------------------------------

-- | /_nmod_poly_pow_binexp/ /res/ /poly/ /len/ /e/ /mod/ 
-- 
-- Raises @poly@ of length @len@ to the power @e@ and sets @res@ to the
-- result. We require that @res@ has enough space for @(len - 1)*e + 1@
-- coefficients. Assumes that @len > 0@, @e > 1@. Aliasing is not
-- permitted. Uses the binary exponentiation method.
foreign import ccall "nmod_poly.h _nmod_poly_pow_binexp"
  _nmod_poly_pow_binexp :: Ptr CMp -> Ptr CMp -> CLong -> CULong -> Ptr CNMod -> IO ()

-- | /nmod_poly_pow_binexp/ /res/ /poly/ /e/ 
-- 
-- Raises @poly@ to the power @e@ and sets @res@ to the result. Uses the
-- binary exponentiation method.
foreign import ccall "nmod_poly.h nmod_poly_pow_binexp"
  nmod_poly_pow_binexp :: Ptr CNModPoly -> Ptr CNModPoly -> CULong -> IO ()

-- | /_nmod_poly_pow/ /res/ /poly/ /len/ /e/ /mod/ 
-- 
-- Raises @poly@ of length @len@ to the power @e@ and sets @res@ to the
-- result. We require that @res@ has enough space for @(len - 1)*e + 1@
-- coefficients. Assumes that @len > 0@, @e > 1@. Aliasing is not
-- permitted.
foreign import ccall "nmod_poly.h _nmod_poly_pow"
  _nmod_poly_pow :: Ptr CMp -> Ptr CMp -> CLong -> CULong -> Ptr CNMod -> IO ()

-- | /nmod_poly_pow/ /res/ /poly/ /e/ 
-- 
-- Raises @poly@ to the power @e@ and sets @res@ to the result.
foreign import ccall "nmod_poly.h nmod_poly_pow"
  nmod_poly_pow :: Ptr CNModPoly -> Ptr CNModPoly -> CULong -> IO ()

-- | /_nmod_poly_pow_trunc_binexp/ /res/ /poly/ /e/ /trunc/ /mod/ 
-- 
-- Sets @res@ to the low @trunc@ coefficients of @poly@ (assumed to be zero
-- padded if necessary to length @trunc@) to the power @e@. This is
-- equivalent to doing a powering followed by a truncation. We require that
-- @res@ has enough space for @trunc@ coefficients, that @trunc > 0@ and
-- that @e > 1@. Aliasing is not permitted. Uses the binary exponentiation
-- method.
foreign import ccall "nmod_poly.h _nmod_poly_pow_trunc_binexp"
  _nmod_poly_pow_trunc_binexp :: Ptr CMp -> Ptr CMp -> CULong -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_pow_trunc_binexp/ /res/ /poly/ /e/ /trunc/ 
-- 
-- Sets @res@ to the low @trunc@ coefficients of @poly@ to the power @e@.
-- This is equivalent to doing a powering followed by a truncation. Uses
-- the binary exponentiation method.
foreign import ccall "nmod_poly.h nmod_poly_pow_trunc_binexp"
  nmod_poly_pow_trunc_binexp :: Ptr CNModPoly -> Ptr CNModPoly -> CULong -> CLong -> IO ()

-- | /_nmod_poly_pow_trunc/ /res/ /poly/ /e/ /trunc/ /mod/ 
-- 
-- Sets @res@ to the low @trunc@ coefficients of @poly@ (assumed to be zero
-- padded if necessary to length @trunc@) to the power @e@. This is
-- equivalent to doing a powering followed by a truncation. We require that
-- @res@ has enough space for @trunc@ coefficients, that @trunc > 0@ and
-- that @e > 1@. Aliasing is not permitted.
foreign import ccall "nmod_poly.h _nmod_poly_pow_trunc"
  _nmod_poly_pow_trunc :: Ptr CMp -> Ptr CMp -> CULong -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_pow_trunc/ /res/ /poly/ /e/ /trunc/ 
-- 
-- Sets @res@ to the low @trunc@ coefficients of @poly@ to the power @e@.
-- This is equivalent to doing a powering followed by a truncation.
foreign import ccall "nmod_poly.h nmod_poly_pow_trunc"
  nmod_poly_pow_trunc :: Ptr CNModPoly -> Ptr CNModPoly -> CULong -> CLong -> IO ()

-- | /_nmod_poly_powmod_ui_binexp/ /res/ /poly/ /e/ /f/ /lenf/ /mod/ 
-- 
-- Sets @res@ to @poly@ raised to the power @e@ modulo @f@, using binary
-- exponentiation. We require @e > 0@.
-- 
-- We require @lenf > 1@. It is assumed that @poly@ is already reduced
-- modulo @f@ and zero-padded as necessary to have length exactly
-- @lenf - 1@. The output @res@ must have room for @lenf - 1@ coefficients.
foreign import ccall "nmod_poly.h _nmod_poly_powmod_ui_binexp"
  _nmod_poly_powmod_ui_binexp :: Ptr CMp -> Ptr CMp -> CULong -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_powmod_ui_binexp/ /res/ /poly/ /e/ /f/ 
-- 
-- Sets @res@ to @poly@ raised to the power @e@ modulo @f@, using binary
-- exponentiation. We require @e >= 0@.
foreign import ccall "nmod_poly.h nmod_poly_powmod_ui_binexp"
  nmod_poly_powmod_ui_binexp :: Ptr CNModPoly -> Ptr CNModPoly -> CULong -> Ptr CNModPoly -> IO ()

-- | /_nmod_poly_powmod_mpz_binexp/ /res/ /poly/ /e/ /f/ /lenf/ /mod/ 
-- 
-- Sets @res@ to @poly@ raised to the power @e@ modulo @f@, using binary
-- exponentiation. We require @e > 0@.
-- 
-- We require @lenf > 1@. It is assumed that @poly@ is already reduced
-- modulo @f@ and zero-padded as necessary to have length exactly
-- @lenf - 1@. The output @res@ must have room for @lenf - 1@ coefficients.
foreign import ccall "nmod_poly.h _nmod_poly_powmod_mpz_binexp"
  _nmod_poly_powmod_mpz_binexp :: Ptr CMp -> Ptr CMp -> Ptr CMpz -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_powmod_mpz_binexp/ /res/ /poly/ /e/ /f/ 
-- 
-- Sets @res@ to @poly@ raised to the power @e@ modulo @f@, using binary
-- exponentiation. We require @e >= 0@.
foreign import ccall "nmod_poly.h nmod_poly_powmod_mpz_binexp"
  nmod_poly_powmod_mpz_binexp :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CMpz -> Ptr CNModPoly -> IO ()

-- | /_nmod_poly_powmod_fmpz_binexp/ /res/ /poly/ /e/ /f/ /lenf/ /mod/ 
-- 
-- Sets @res@ to @poly@ raised to the power @e@ modulo @f@, using binary
-- exponentiation. We require @e > 0@.
-- 
-- We require @lenf > 1@. It is assumed that @poly@ is already reduced
-- modulo @f@ and zero-padded as necessary to have length exactly
-- @lenf - 1@. The output @res@ must have room for @lenf - 1@ coefficients.
foreign import ccall "nmod_poly.h _nmod_poly_powmod_fmpz_binexp"
  _nmod_poly_powmod_fmpz_binexp :: Ptr CMp -> Ptr CMp -> Ptr CFmpz -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_powmod_fmpz_binexp/ /res/ /poly/ /e/ /f/ 
-- 
-- Sets @res@ to @poly@ raised to the power @e@ modulo @f@, using binary
-- exponentiation. We require @e >= 0@.
foreign import ccall "nmod_poly.h nmod_poly_powmod_fmpz_binexp"
  nmod_poly_powmod_fmpz_binexp :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CFmpz -> Ptr CNModPoly -> IO ()

-- | /_nmod_poly_powmod_ui_binexp_preinv/ /res/ /poly/ /e/ /f/ /lenf/ /finv/ /lenfinv/ /mod/ 
-- 
-- Sets @res@ to @poly@ raised to the power @e@ modulo @f@, using binary
-- exponentiation. We require @e > 0@. We require @finv@ to be the inverse
-- of the reverse of @f@.
-- 
-- We require @lenf > 1@. It is assumed that @poly@ is already reduced
-- modulo @f@ and zero-padded as necessary to have length exactly
-- @lenf - 1@. The output @res@ must have room for @lenf - 1@ coefficients.
foreign import ccall "nmod_poly.h _nmod_poly_powmod_ui_binexp_preinv"
  _nmod_poly_powmod_ui_binexp_preinv :: Ptr CMp -> Ptr CMp -> CULong -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_powmod_ui_binexp_preinv/ /res/ /poly/ /e/ /f/ /finv/ 
-- 
-- Sets @res@ to @poly@ raised to the power @e@ modulo @f@, using binary
-- exponentiation. We require @e >= 0@. We require @finv@ to be the inverse
-- of the reverse of @f@.
foreign import ccall "nmod_poly.h nmod_poly_powmod_ui_binexp_preinv"
  nmod_poly_powmod_ui_binexp_preinv :: Ptr CNModPoly -> Ptr CNModPoly -> CULong -> Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- | /_nmod_poly_powmod_mpz_binexp_preinv/ /res/ /poly/ /e/ /f/ /lenf/ /finv/ /lenfinv/ /mod/ 
-- 
-- Sets @res@ to @poly@ raised to the power @e@ modulo @f@, using binary
-- exponentiation. We require @e > 0@. We require @finv@ to be the inverse
-- of the reverse of @f@. We require @lenf > 1@. It is assumed that @poly@
-- is already reduced modulo @f@ and zero-padded as necessary to have
-- length exactly @lenf - 1@. The output @res@ must have room for
-- @lenf - 1@ coefficients.
foreign import ccall "nmod_poly.h _nmod_poly_powmod_mpz_binexp_preinv"
  _nmod_poly_powmod_mpz_binexp_preinv :: Ptr CMp -> Ptr CMp -> Ptr CMpz -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_powmod_mpz_binexp_preinv/ /res/ /poly/ /e/ /f/ /finv/ 
-- 
-- Sets @res@ to @poly@ raised to the power @e@ modulo @f@, using binary
-- exponentiation. We require @e >= 0@. We require @finv@ to be the inverse
-- of the reverse of @f@.
foreign import ccall "nmod_poly.h nmod_poly_powmod_mpz_binexp_preinv"
  nmod_poly_powmod_mpz_binexp_preinv :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CMpz -> Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- | /_nmod_poly_powmod_fmpz_binexp_preinv/ /res/ /poly/ /e/ /f/ /lenf/ /finv/ /lenfinv/ /mod/ 
-- 
-- Sets @res@ to @poly@ raised to the power @e@ modulo @f@, using binary
-- exponentiation. We require @e > 0@. We require @finv@ to be the inverse
-- of the reverse of @f@.
-- 
-- We require @lenf > 1@. It is assumed that @poly@ is already reduced
-- modulo @f@ and zero-padded as necessary to have length exactly
-- @lenf - 1@. The output @res@ must have room for @lenf - 1@ coefficients.
foreign import ccall "nmod_poly.h _nmod_poly_powmod_fmpz_binexp_preinv"
  _nmod_poly_powmod_fmpz_binexp_preinv :: Ptr CMp -> Ptr CMp -> Ptr CFmpz -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_powmod_fmpz_binexp_preinv/ /res/ /poly/ /e/ /f/ /finv/ 
-- 
-- Sets @res@ to @poly@ raised to the power @e@ modulo @f@, using binary
-- exponentiation. We require @e >= 0@. We require @finv@ to be the inverse
-- of the reverse of @f@.
foreign import ccall "nmod_poly.h nmod_poly_powmod_fmpz_binexp_preinv"
  nmod_poly_powmod_fmpz_binexp_preinv :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CFmpz -> Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- | /_nmod_poly_powmod_x_ui_preinv/ /res/ /e/ /f/ /lenf/ /finv/ /lenfinv/ /mod/ 
-- 
-- Sets @res@ to @x@ raised to the power @e@ modulo @f@, using sliding
-- window exponentiation. We require @e > 0@. We require @finv@ to be the
-- inverse of the reverse of @f@.
-- 
-- We require @lenf > 2@. The output @res@ must have room for @lenf - 1@
-- coefficients.
foreign import ccall "nmod_poly.h _nmod_poly_powmod_x_ui_preinv"
  _nmod_poly_powmod_x_ui_preinv :: Ptr CMp -> CULong -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_powmod_x_ui_preinv/ /res/ /e/ /f/ /finv/ 
-- 
-- Sets @res@ to @x@ raised to the power @e@ modulo @f@, using sliding
-- window exponentiation. We require @e >= 0@. We require @finv@ to be the
-- inverse of the reverse of @f@.
foreign import ccall "nmod_poly.h nmod_poly_powmod_x_ui_preinv"
  nmod_poly_powmod_x_ui_preinv :: Ptr CNModPoly -> CULong -> Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- | /_nmod_poly_powmod_x_fmpz_preinv/ /res/ /e/ /f/ /lenf/ /finv/ /lenfinv/ /mod/ 
-- 
-- Sets @res@ to @x@ raised to the power @e@ modulo @f@, using sliding
-- window exponentiation. We require @e > 0@. We require @finv@ to be the
-- inverse of the reverse of @f@.
-- 
-- We require @lenf > 2@. The output @res@ must have room for @lenf - 1@
-- coefficients.
foreign import ccall "nmod_poly.h _nmod_poly_powmod_x_fmpz_preinv"
  _nmod_poly_powmod_x_fmpz_preinv :: Ptr CMp -> Ptr CFmpz -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_powmod_x_fmpz_preinv/ /res/ /e/ /f/ /finv/ 
-- 
-- Sets @res@ to @x@ raised to the power @e@ modulo @f@, using sliding
-- window exponentiation. We require @e >= 0@. We require @finv@ to be the
-- inverse of the reverse of @f@.
foreign import ccall "nmod_poly.h nmod_poly_powmod_x_fmpz_preinv"
  nmod_poly_powmod_x_fmpz_preinv :: Ptr CNModPoly -> Ptr CFmpz -> Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- | /_nmod_poly_powers_mod_preinv_naive/ /res/ /f/ /flen/ /n/ /g/ /glen/ /ginv/ /ginvlen/ /mod/ 
-- 
-- Compute @f^0, f^1, ..., f^(n-1) mod g@, where @g@ has length @glen@ and
-- @f@ is reduced mod @g@ and has length @flen@ (possibly zero spaced).
-- Assumes @res@ is an array of @n@ arrays each with space for at least
-- @glen - 1@ coefficients and that @flen > 0@. We require that @ginv@ of
-- length @ginvlen@ is set to the power series inverse of the reverse of
-- @g@.
foreign import ccall "nmod_poly.h _nmod_poly_powers_mod_preinv_naive"
  _nmod_poly_powers_mod_preinv_naive :: Ptr (Ptr CMp) -> Ptr CMp -> CLong -> CLong -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_powers_mod_naive/ /res/ /f/ /n/ /g/ 
-- 
-- Set the entries of the array @res@ to @f^0, f^1, ..., f^(n-1) mod g@. No
-- aliasing is permitted between the entries of @res@ and either of the
-- inputs.
foreign import ccall "nmod_poly.h nmod_poly_powers_mod_naive"
  nmod_poly_powers_mod_naive :: Ptr (Ptr CNModPoly) -> Ptr CNModPoly -> CLong -> Ptr CNModPoly -> IO ()

-- | /_nmod_poly_powers_mod_preinv_threaded_pool/ /res/ /f/ /flen/ /n/ /g/ /glen/ /ginv/ /ginvlen/ /mod/ /threads/ /num_threads/ 
-- 
-- Compute @f^0, f^1, ..., f^(n-1) mod g@, where @g@ has length @glen@ and
-- @f@ is reduced mod @g@ and has length @flen@ (possibly zero spaced).
-- Assumes @res@ is an array of @n@ arrays each with space for at least
-- @glen - 1@ coefficients and that @flen > 0@. We require that @ginv@ of
-- length @ginvlen@ is set to the power series inverse of the reverse of
-- @g@.
foreign import ccall "nmod_poly.h _nmod_poly_powers_mod_preinv_threaded_pool"
  _nmod_poly_powers_mod_preinv_threaded_pool :: Ptr (Ptr CMp) -> Ptr CMp -> CLong -> CLong -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> Ptr CThreadPoolHandle -> CLong -> IO ()

-- | /_nmod_poly_powers_mod_preinv_threaded/ /res/ /f/ /flen/ /n/ /g/ /glen/ /ginv/ /ginvlen/ /mod/ 
-- 
-- Compute @f^0, f^1, ..., f^(n-1) mod g@, where @g@ has length @glen@ and
-- @f@ is reduced mod @g@ and has length @flen@ (possibly zero spaced).
-- Assumes @res@ is an array of @n@ arrays each with space for at least
-- @glen - 1@ coefficients and that @flen > 0@. We require that @ginv@ of
-- length @ginvlen@ is set to the power series inverse of the reverse of
-- @g@.
foreign import ccall "nmod_poly.h _nmod_poly_powers_mod_preinv_threaded"
  _nmod_poly_powers_mod_preinv_threaded :: Ptr (Ptr CMp) -> Ptr CMp -> CLong -> CLong -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_powers_mod_bsgs/ /res/ /f/ /n/ /g/ 
-- 
-- Set the entries of the array @res@ to @f^0, f^1, ..., f^(n-1) mod g@. No
-- aliasing is permitted between the entries of @res@ and either of the
-- inputs.
foreign import ccall "nmod_poly.h nmod_poly_powers_mod_bsgs"
  nmod_poly_powers_mod_bsgs :: Ptr (Ptr CNModPoly) -> Ptr CNModPoly -> CLong -> Ptr CNModPoly -> IO ()

-- Division --------------------------------------------------------------------

-- | /_nmod_poly_divrem_basecase/ /Q/ /R/ /W/ /A/ /A_len/ /B/ /B_len/ /mod/ 
-- 
-- Finds \(Q\) and \(R\) such that \(A = B Q + R\) with
-- \(\operatorname{len}(R) < \operatorname{len}(B)\). If
-- \(\operatorname{len}(B) = 0\) an exception is raised. We require that
-- @W@ is temporary space of @NMOD_DIVREM_BC_ITCH(A_len, B_len, mod)@
-- coefficients.
foreign import ccall "nmod_poly.h _nmod_poly_divrem_basecase"
  _nmod_poly_divrem_basecase :: Ptr CMp -> Ptr CMp -> Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_divrem_basecase/ /Q/ /R/ /A/ /B/ 
-- 
-- Finds \(Q\) and \(R\) such that \(A = B Q + R\) with
-- \(\operatorname{len}(R) < \operatorname{len}(B)\). If
-- \(\operatorname{len}(B) = 0\) an exception is raised.
foreign import ccall "nmod_poly.h nmod_poly_divrem_basecase"
  nmod_poly_divrem_basecase :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- | /_nmod_poly_divrem/ /Q/ /R/ /A/ /lenA/ /B/ /lenB/ /mod/ 
-- 
-- Computes \(Q\) and \(R\) such that \(A = BQ + R\) with
-- \(\operatorname{len}(R)\) less than @lenB@, where @A@ is of length
-- @lenA@ and @B@ is of length @lenB@. We require that @Q@ have space for
-- @lenA - lenB + 1@ coefficients.
foreign import ccall "nmod_poly.h _nmod_poly_divrem"
  _nmod_poly_divrem :: Ptr CMp -> Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_divrem/ /Q/ /R/ /A/ /B/ 
-- 
-- Computes \(Q\) and \(R\) such that \(A = BQ + R\) with
-- \(\operatorname{len}(R) < \operatorname{len}(B)\).
foreign import ccall "nmod_poly.h nmod_poly_divrem"
  nmod_poly_divrem :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- | /_nmod_poly_div/ /Q/ /A/ /lenA/ /B/ /lenB/ /mod/ 
-- 
-- Notionally computes polynomials \(Q\) and \(R\) such that \(A = BQ + R\)
-- with \(\operatorname{len}(R)\) less than @lenB@, where @A@ is of length
-- @lenA@ and @B@ is of length @lenB@, but returns only @Q@. We require
-- that @Q@ have space for @lenA - lenB + 1@ coefficients.
foreign import ccall "nmod_poly.h _nmod_poly_div"
  _nmod_poly_div :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_div/ /Q/ /A/ /B/ 
-- 
-- Computes the quotient \(Q\) on polynomial division of \(A\) and \(B\).
foreign import ccall "nmod_poly.h nmod_poly_div"
  nmod_poly_div :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> IO ()

foreign import ccall "nmod_poly.h _nmod_poly_rem_q1"
  _nmod_poly_rem_q1 :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /_nmod_poly_rem/ /R/ /A/ /lenA/ /B/ /lenB/ /mod/ 
-- 
-- Computes the remainder \(R\) on polynomial division of \(A\) by \(B\).
foreign import ccall "nmod_poly.h _nmod_poly_rem"
  _nmod_poly_rem :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_rem/ /R/ /A/ /B/ 
-- 
-- Computes the remainder \(R\) on polynomial division of \(A\) by \(B\).
foreign import ccall "nmod_poly.h nmod_poly_rem"
  nmod_poly_rem :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- | /_nmod_poly_inv_series_basecase/ /Qinv/ /Q/ /Qlen/ /n/ /mod/ 
-- 
-- Given @Q@ of length @Qlen@ whose leading coefficient is invertible
-- modulo the given modulus, finds a polynomial @Qinv@ of length @n@ such
-- that the top @n@ coefficients of the product @Q * Qinv@ is
-- \(x^{n - 1}\). Requires that @n > 0@. This function can be viewed as
-- inverting a power series.
foreign import ccall "nmod_poly.h _nmod_poly_inv_series_basecase"
  _nmod_poly_inv_series_basecase :: Ptr CMp -> Ptr CMp -> CLong -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_inv_series_basecase/ /Qinv/ /Q/ /n/ 
-- 
-- Given @Q@ of length at least @n@ find @Qinv@ of length @n@ such that the
-- top @n@ coefficients of the product @Q * Qinv@ is \(x^{n - 1}\). An
-- exception is raised if @n = 0@ or if the length of @Q@ is less than @n@.
-- The leading coefficient of @Q@ must be invertible modulo the modulus of
-- @Q@. This function can be viewed as inverting a power series.
foreign import ccall "nmod_poly.h nmod_poly_inv_series_basecase"
  nmod_poly_inv_series_basecase :: Ptr CNModPoly -> Ptr CNModPoly -> CLong -> IO ()

-- | /_nmod_poly_inv_series_newton/ /Qinv/ /Q/ /Qlen/ /n/ /mod/ 
-- 
-- Given @Q@ of length @Qlen@ whose constant coefficient is invertible
-- modulo the given modulus, find a polynomial @Qinv@ of length @n@ such
-- that @Q * Qinv@ is @1@ modulo \(x^n\). Requires @n > 0@. This function
-- can be viewed as inverting a power series via Newton iteration.
foreign import ccall "nmod_poly.h _nmod_poly_inv_series_newton"
  _nmod_poly_inv_series_newton :: Ptr CMp -> Ptr CMp -> CLong -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_inv_series_newton/ /Qinv/ /Q/ /n/ 
-- 
-- Given @Q@ find @Qinv@ such that @Q * Qinv@ is @1@ modulo \(x^n\). The
-- constant coefficient of @Q@ must be invertible modulo the modulus of
-- @Q@. An exception is raised if this is not the case or if @n = 0@. This
-- function can be viewed as inverting a power series via Newton iteration.
foreign import ccall "nmod_poly.h nmod_poly_inv_series_newton"
  nmod_poly_inv_series_newton :: Ptr CNModPoly -> Ptr CNModPoly -> CLong -> IO ()

-- | /_nmod_poly_inv_series/ /Qinv/ /Q/ /Qlen/ /n/ /mod/ 
-- 
-- Given @Q@ of length @Qlenn@ whose constant coefficient is invertible
-- modulo the given modulus, find a polynomial @Qinv@ of length @n@ such
-- that @Q * Qinv@ is @1@ modulo \(x^n\). Requires @n > 0@. This function
-- can be viewed as inverting a power series.
foreign import ccall "nmod_poly.h _nmod_poly_inv_series"
  _nmod_poly_inv_series :: Ptr CMp -> Ptr CMp -> CLong -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_inv_series/ /Qinv/ /Q/ /n/ 
-- 
-- Given @Q@ find @Qinv@ such that @Q * Qinv@ is @1@ modulo \(x^n\). The
-- constant coefficient of @Q@ must be invertible modulo the modulus of
-- @Q@. An exception is raised if this is not the case or if @n = 0@. This
-- function can be viewed as inverting a power series.
foreign import ccall "nmod_poly.h nmod_poly_inv_series"
  nmod_poly_inv_series :: Ptr CNModPoly -> Ptr CNModPoly -> CLong -> IO ()

-- | /_nmod_poly_div_series_basecase/ /Q/ /A/ /Alen/ /B/ /Blen/ /n/ /mod/ 
-- 
-- Given polynomials @A@ and @B@ of length @Alen@ and @Blen@, finds the
-- polynomial @Q@ of length @n@ such that @Q * B = A@ modulo \(x^n\). We
-- assume @n > 0@ and that the constant coefficient of @B@ is invertible
-- modulo the given modulus. The polynomial @Q@ must have space for @n@
-- coefficients.
foreign import ccall "nmod_poly.h _nmod_poly_div_series_basecase"
  _nmod_poly_div_series_basecase :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_div_series_basecase/ /Q/ /A/ /B/ /n/ 
-- 
-- Given polynomials @A@ and @B@ considered modulo @n@, finds the
-- polynomial @Q@ of length at most @n@ such that @Q * B = A@ modulo
-- \(x^n\). We assume @n > 0@ and that the constant coefficient of @B@ is
-- invertible modulo the modulus. An exception is raised if @n == 0@ or the
-- constant coefficient of @B@ is zero.
foreign import ccall "nmod_poly.h nmod_poly_div_series_basecase"
  nmod_poly_div_series_basecase :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> CLong -> IO ()

-- | /_nmod_poly_div_series/ /Q/ /A/ /Alen/ /B/ /Blen/ /n/ /mod/ 
-- 
-- Given polynomials @A@ and @B@ of length @Alen@ and @Blen@, finds the
-- polynomial @Q@ of length @n@ such that @Q * B = A@ modulo \(x^n\). We
-- assume @n > 0@ and that the constant coefficient of @B@ is invertible
-- modulo the given modulus. The polynomial @Q@ must have space for @n@
-- coefficients.
foreign import ccall "nmod_poly.h _nmod_poly_div_series"
  _nmod_poly_div_series :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_div_series/ /Q/ /A/ /B/ /n/ 
-- 
-- Given polynomials @A@ and @B@ considered modulo @n@, finds the
-- polynomial @Q@ of length at most @n@ such that @Q * B = A@ modulo
-- \(x^n\). We assume @n > 0@ and that the constant coefficient of @B@ is
-- invertible modulo the modulus. An exception is raised if @n == 0@ or the
-- constant coefficient of @B@ is zero.
foreign import ccall "nmod_poly.h nmod_poly_div_series"
  nmod_poly_div_series :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> CLong -> IO ()

-- | /_nmod_poly_div_newton_n_preinv/ /Q/ /A/ /lenA/ /B/ /lenB/ /Binv/ /lenBinv/ /mod/ 
-- 
-- Notionally computes polynomials \(Q\) and \(R\) such that \(A = BQ + R\)
-- with \(\operatorname{len}(R)\) less than @lenB@, where @A@ is of length
-- @lenA@ and @B@ is of length @lenB@, but return only \(Q\).
-- 
-- We require that \(Q\) have space for @lenA - lenB + 1@ coefficients and
-- assume that the leading coefficient of \(B\) is a unit. Furthermore, we
-- assume that \(Binv\) is the inverse of the reverse of \(B\) mod
-- \(x^{\operatorname{len}(B)}\).
-- 
-- The algorithm used is to reverse the polynomials and divide the
-- resulting power series, then reverse the result.
foreign import ccall "nmod_poly.h _nmod_poly_div_newton_n_preinv"
  _nmod_poly_div_newton_n_preinv :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_div_newton_n_preinv/ /Q/ /A/ /B/ /Binv/ 
-- 
-- Notionally computes \(Q\) and \(R\) such that \(A = BQ + R\) with
-- \(\operatorname{len}(R) < \operatorname{len}(B)\), but returns only
-- \(Q\).
-- 
-- We assume that the leading coefficient of \(B\) is a unit and that
-- \(Binv\) is the inverse of the reverse of \(B\) mod
-- \(x^{\operatorname{len}(B)}\).
-- 
-- It is required that the length of \(A\) is less than or equal to 2*the
-- length of \(B\) - 2.
-- 
-- The algorithm used is to reverse the polynomials and divide the
-- resulting power series, then reverse the result.
foreign import ccall "nmod_poly.h nmod_poly_div_newton_n_preinv"
  nmod_poly_div_newton_n_preinv :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- | /_nmod_poly_divrem_newton_n_preinv/ /Q/ /R/ /A/ /lenA/ /B/ /lenB/ /Binv/ /lenBinv/ /mod/ 
-- 
-- Computes \(Q\) and \(R\) such that \(A = BQ + R\) with
-- \(\operatorname{len}(R)\) less than @lenB@, where \(A\) is of length
-- @lenA@ and \(B\) is of length @lenB@. We require that \(Q\) have space
-- for @lenA - lenB + 1@ coefficients. Furthermore, we assume that \(Binv\)
-- is the inverse of the reverse of \(B\) mod
-- \(x^{\operatorname{len}(B)}\). The algorithm used is to call
-- @div_newton_n_preinv@ and then multiply out and compute the remainder.
foreign import ccall "nmod_poly.h _nmod_poly_divrem_newton_n_preinv"
  _nmod_poly_divrem_newton_n_preinv :: Ptr CMp -> Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_divrem_newton_n_preinv/ /Q/ /R/ /A/ /B/ /Binv/ 
-- 
-- Computes \(Q\) and \(R\) such that \(A = BQ + R\) with
-- \(\operatorname{len}(R) < \operatorname{len}(B)\). We assume \(Binv\) is
-- the inverse of the reverse of \(B\) mod \(x^{\operatorname{len}(B)}\).
-- 
-- It is required that the length of \(A\) is less than or equal to 2*the
-- length of \(B\) - 2.
-- 
-- The algorithm used is to call @div_newton_n@ and then multiply out and
-- compute the remainder.
foreign import ccall "nmod_poly.h nmod_poly_divrem_newton_n_preinv"
  nmod_poly_divrem_newton_n_preinv :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- | /_nmod_poly_div_root/ /Q/ /A/ /len/ /c/ /mod/ 
-- 
-- Sets @(Q, len-1)@ to the quotient of @(A, len)@ on division by
-- \((x - c)\), and returns the remainder, equal to the value of \(A\)
-- evaluated at \(c\). \(A\) and \(Q\) are allowed to be the same, but may
-- not overlap partially in any other way.
foreign import ccall "nmod_poly.h _nmod_poly_div_root"
  _nmod_poly_div_root :: Ptr CMp -> Ptr CMp -> CLong -> CMpLimb -> Ptr CNMod -> IO CMpLimb

-- | /nmod_poly_div_root/ /Q/ /A/ /c/ 
-- 
-- Sets \(Q\) to the quotient of \(A\) on division by \((x - c)\), and
-- returns the remainder, equal to the value of \(A\) evaluated at \(c\).
foreign import ccall "nmod_poly.h nmod_poly_div_root"
  nmod_poly_div_root :: Ptr CNModPoly -> Ptr CNModPoly -> CMpLimb -> IO CMpLimb

-- Divisibility testing --------------------------------------------------------

-- | /_nmod_poly_divides_classical/ /Q/ /A/ /lenA/ /B/ /lenB/ /mod/ 
-- 
-- Returns \(1\) if \((B, lenB)\) divides \((A, lenA)\) and sets
-- \((Q, lenA - lenB + 1)\) to the quotient. Otherwise, returns \(0\) and
-- sets \((Q, lenA - lenB + 1)\) to zero. We require that
-- \(lenA >= lenB > 0\).
foreign import ccall "nmod_poly.h _nmod_poly_divides_classical"
  _nmod_poly_divides_classical :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO CInt

-- | /nmod_poly_divides_classical/ /Q/ /A/ /B/ 
-- 
-- Returns \(1\) if \(B\) divides \(A\) and sets \(Q\) to the quotient.
-- Otherwise returns \(0\) and sets \(Q\) to zero.
foreign import ccall "nmod_poly.h nmod_poly_divides_classical"
  nmod_poly_divides_classical :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> IO CInt

-- | /_nmod_poly_divides/ /Q/ /A/ /lenA/ /B/ /lenB/ /mod/ 
-- 
-- Returns \(1\) if \((B, lenB)\) divides \((A, lenA)\) and sets
-- \((Q, lenA - lenB + 1)\) to the quotient. Otherwise, returns \(0\) and
-- sets \((Q, lenA - lenB + 1)\) to zero. We require that
-- \(lenA >= lenB > 0\).
foreign import ccall "nmod_poly.h _nmod_poly_divides"
  _nmod_poly_divides :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO CInt

-- | /nmod_poly_divides/ /Q/ /A/ /B/ 
-- 
-- Returns \(1\) if \(B\) divides \(A\) and sets \(Q\) to the quotient.
-- Otherwise returns \(0\) and sets \(Q\) to zero.
foreign import ccall "nmod_poly.h nmod_poly_divides"
  nmod_poly_divides :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> IO CInt

-- Derivative and integral -----------------------------------------------------

-- | /_nmod_poly_derivative/ /x_prime/ /x/ /len/ /mod/ 
-- 
-- Sets the first @len - 1@ coefficients of @x_prime@ to the derivative of
-- @x@ which is assumed to be of length @len@. It is assumed that
-- @len > 0@.
foreign import ccall "nmod_poly.h _nmod_poly_derivative"
  _nmod_poly_derivative :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_derivative/ /x_prime/ /x/ 
-- 
-- Sets @x_prime@ to the derivative of @x@.
foreign import ccall "nmod_poly.h nmod_poly_derivative"
  nmod_poly_derivative :: Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- | /_nmod_poly_integral/ /x_int/ /x/ /len/ /mod/ 
-- 
-- Set the first @len@ coefficients of @x_int@ to the integral of @x@ which
-- is assumed to be of length @len - 1@. The constant term of @x_int@ is
-- set to zero. It is assumed that @len > 0@. The result is only
-- well-defined if the modulus is a prime number strictly larger than the
-- degree of @x@. Supports aliasing between the two polynomials.
foreign import ccall "nmod_poly.h _nmod_poly_integral"
  _nmod_poly_integral :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_integral/ /x_int/ /x/ 
-- 
-- Set @x_int@ to the indefinite integral of @x@ with constant term zero.
-- The result is only well-defined if the modulus is a prime number
-- strictly larger than the degree of @x@.
foreign import ccall "nmod_poly.h nmod_poly_integral"
  nmod_poly_integral :: Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- Evaluation ------------------------------------------------------------------

-- | /_nmod_poly_evaluate_nmod/ /poly/ /len/ /c/ /mod/ 
-- 
-- Evaluates @poly@ at the value~@c@ and reduces modulo the given modulus
-- of @poly@. The value~@c@ should be reduced modulo the modulus. The
-- algorithm used is Horner\'s method.
foreign import ccall "nmod_poly.h _nmod_poly_evaluate_nmod"
  _nmod_poly_evaluate_nmod :: Ptr CMp -> CLong -> CMpLimb -> Ptr CNMod -> IO CMpLimb

-- | /nmod_poly_evaluate_nmod/ /poly/ /c/ 
-- 
-- Evaluates @poly@ at the value~@c@ and reduces modulo the modulus of
-- @poly@. The value~@c@ should be reduced modulo the modulus. The
-- algorithm used is Horner\'s method.
foreign import ccall "nmod_poly.h nmod_poly_evaluate_nmod"
  nmod_poly_evaluate_nmod :: Ptr CNModPoly -> CMpLimb -> IO CMpLimb

-- | /nmod_poly_evaluate_mat_horner/ /dest/ /poly/ /c/ 
-- 
-- Evaluates @poly@ with matrix as an argument at the value @c@ and stores
-- the result in @dest@. The dimension and modulus of @dest@ is assumed to
-- be same as that of @c@. @dest@ and @c@ may be aliased. Horner\'s Method
-- is used to compute the result.
foreign import ccall "nmod_poly.h nmod_poly_evaluate_mat_horner"
  nmod_poly_evaluate_mat_horner :: Ptr CNModMat -> Ptr CNModPoly -> Ptr CNModMat -> IO ()

-- | /nmod_poly_evaluate_mat_paterson_stockmeyer/ /dest/ /poly/ /c/ 
-- 
-- Evaluates @poly@ with matrix as an argument at the value @c@ and stores
-- the result in @dest@. The dimension and modulus of @dest@ is assumed to
-- be same as that of @c@. @dest@ and @c@ may be aliased.
-- Paterson-Stockmeyer algorithm is used to compute the result. The
-- algorithm is described in < [Paterson1973]>.
foreign import ccall "nmod_poly.h nmod_poly_evaluate_mat_paterson_stockmeyer"
  nmod_poly_evaluate_mat_paterson_stockmeyer :: Ptr CNModMat -> Ptr CNModPoly -> Ptr CNModMat -> IO ()

-- | /nmod_poly_evaluate_mat/ /dest/ /poly/ /c/ 
-- 
-- Evaluates @poly@ with matrix as an argument at the value @c@ and stores
-- the result in @dest@. The dimension and modulus of @dest@ is assumed to
-- be same as that of @c@. @dest@ and @c@ may be aliased. This function
-- automatically switches between Horner\'s method and the
-- Paterson-Stockmeyer algorithm.
foreign import ccall "nmod_poly.h nmod_poly_evaluate_mat"
  nmod_poly_evaluate_mat :: Ptr CNModMat -> Ptr CNModPoly -> Ptr CNModMat -> IO ()

-- Multipoint evaluation -------------------------------------------------------

-- | /_nmod_poly_evaluate_nmod_vec_iter/ /ys/ /poly/ /len/ /xs/ /n/ /mod/ 
-- 
-- Evaluates (@coeffs@, @len@) at the @n@ values given in the vector @xs@,
-- writing the output values to @ys@. The values in @xs@ should be reduced
-- modulo the modulus.
-- 
-- Uses Horner\'s method iteratively.
foreign import ccall "nmod_poly.h _nmod_poly_evaluate_nmod_vec_iter"
  _nmod_poly_evaluate_nmod_vec_iter :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_evaluate_nmod_vec_iter/ /ys/ /poly/ /xs/ /n/ 
-- 
-- Evaluates @poly@ at the @n@ values given in the vector @xs@, writing the
-- output values to @ys@. The values in @xs@ should be reduced modulo the
-- modulus.
-- 
-- Uses Horner\'s method iteratively.
foreign import ccall "nmod_poly.h nmod_poly_evaluate_nmod_vec_iter"
  nmod_poly_evaluate_nmod_vec_iter :: Ptr CMp -> Ptr CNModPoly -> Ptr CMp -> CLong -> IO ()

-- | /_nmod_poly_evaluate_nmod_vec_fast_precomp/ /vs/ /poly/ /plen/ /tree/ /len/ /mod/ 
-- 
-- Evaluates (@poly@, @plen@) at the @len@ values given by the precomputed
-- subproduct tree @tree@.
foreign import ccall "nmod_poly.h _nmod_poly_evaluate_nmod_vec_fast_precomp"
  _nmod_poly_evaluate_nmod_vec_fast_precomp :: Ptr CMp -> Ptr CMp -> CLong -> Ptr (Ptr CMp) -> CLong -> Ptr CNMod -> IO ()

-- | /_nmod_poly_evaluate_nmod_vec_fast/ /ys/ /poly/ /len/ /xs/ /n/ /mod/ 
-- 
-- Evaluates (@coeffs@, @len@) at the @n@ values given in the vector @xs@,
-- writing the output values to @ys@. The values in @xs@ should be reduced
-- modulo the modulus.
-- 
-- Uses fast multipoint evaluation, building a temporary subproduct tree.
foreign import ccall "nmod_poly.h _nmod_poly_evaluate_nmod_vec_fast"
  _nmod_poly_evaluate_nmod_vec_fast :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_evaluate_nmod_vec_fast/ /ys/ /poly/ /xs/ /n/ 
-- 
-- Evaluates @poly@ at the @n@ values given in the vector @xs@, writing the
-- output values to @ys@. The values in @xs@ should be reduced modulo the
-- modulus.
-- 
-- Uses fast multipoint evaluation, building a temporary subproduct tree.
foreign import ccall "nmod_poly.h nmod_poly_evaluate_nmod_vec_fast"
  nmod_poly_evaluate_nmod_vec_fast :: Ptr CMp -> Ptr CNModPoly -> Ptr CMp -> CLong -> IO ()

-- | /_nmod_poly_evaluate_nmod_vec/ /ys/ /poly/ /len/ /xs/ /n/ /mod/ 
-- 
-- Evaluates (@poly@, @len@) at the @n@ values given in the vector @xs@,
-- writing the output values to @ys@. The values in @xs@ should be reduced
-- modulo the modulus.
foreign import ccall "nmod_poly.h _nmod_poly_evaluate_nmod_vec"
  _nmod_poly_evaluate_nmod_vec :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_evaluate_nmod_vec/ /ys/ /poly/ /xs/ /n/ 
-- 
-- Evaluates @poly@ at the @n@ values given in the vector @xs@, writing the
-- output values to @ys@. The values in @xs@ should be reduced modulo the
-- modulus.
foreign import ccall "nmod_poly.h nmod_poly_evaluate_nmod_vec"
  nmod_poly_evaluate_nmod_vec :: Ptr CMp -> Ptr CNModPoly -> Ptr CMp -> CLong -> IO ()

-- Interpolation ---------------------------------------------------------------

-- | /_nmod_poly_interpolate_nmod_vec/ /poly/ /xs/ /ys/ /n/ /mod/ 
-- 
-- Sets @poly@ to the unique polynomial of length at most @n@ that
-- interpolates the @n@ given evaluation points @xs@ and values @ys@. If
-- the interpolating polynomial is shorter than length @n@, the leading
-- coefficients are set to zero.
-- 
-- The values in @xs@ and @ys@ should be reduced modulo the modulus, and
-- all @xs@ must be distinct. Aliasing between @poly@ and @xs@ or @ys@ is
-- not allowed.
foreign import ccall "nmod_poly.h _nmod_poly_interpolate_nmod_vec"
  _nmod_poly_interpolate_nmod_vec :: Ptr CMp -> Ptr CMp -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_interpolate_nmod_vec/ /poly/ /xs/ /ys/ /n/ 
-- 
-- Sets @poly@ to the unique polynomial of length @n@ that interpolates the
-- @n@ given evaluation points @xs@ and values @ys@. The values in @xs@ and
-- @ys@ should be reduced modulo the modulus, and all @xs@ must be
-- distinct.
foreign import ccall "nmod_poly.h nmod_poly_interpolate_nmod_vec"
  nmod_poly_interpolate_nmod_vec :: Ptr CNModPoly -> Ptr CMp -> Ptr CMp -> CLong -> IO ()

-- | /_nmod_poly_interpolation_weights/ /w/ /tree/ /len/ /mod/ 
-- 
-- Sets @w@ to the barycentric interpolation weights for fast Lagrange
-- interpolation with respect to a given subproduct tree.
foreign import ccall "nmod_poly.h _nmod_poly_interpolation_weights"
  _nmod_poly_interpolation_weights :: Ptr CMp -> Ptr (Ptr CMp) -> CLong -> Ptr CNMod -> IO ()

-- | /_nmod_poly_interpolate_nmod_vec_fast_precomp/ /poly/ /ys/ /tree/ /weights/ /len/ /mod/ 
-- 
-- Performs interpolation using the fast Lagrange interpolation algorithm,
-- generating a temporary subproduct tree.
-- 
-- The function values are given as @ys@. The function takes a precomputed
-- subproduct tree @tree@ and barycentric interpolation weights @weights@
-- corresponding to the roots.
foreign import ccall "nmod_poly.h _nmod_poly_interpolate_nmod_vec_fast_precomp"
  _nmod_poly_interpolate_nmod_vec_fast_precomp :: Ptr CMp -> Ptr CMp -> Ptr (Ptr CMp) -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /_nmod_poly_interpolate_nmod_vec_fast/ /poly/ /xs/ /ys/ /n/ /mod/ 
-- 
-- Performs interpolation using the fast Lagrange interpolation algorithm,
-- generating a temporary subproduct tree.
foreign import ccall "nmod_poly.h _nmod_poly_interpolate_nmod_vec_fast"
  _nmod_poly_interpolate_nmod_vec_fast :: Ptr CMp -> Ptr CMp -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_interpolate_nmod_vec_fast/ /poly/ /xs/ /ys/ /n/ 
-- 
-- Performs interpolation using the fast Lagrange interpolation algorithm,
-- generating a temporary subproduct tree.
foreign import ccall "nmod_poly.h nmod_poly_interpolate_nmod_vec_fast"
  nmod_poly_interpolate_nmod_vec_fast :: Ptr CNModPoly -> Ptr CMp -> Ptr CMp -> CLong -> IO ()

-- | /_nmod_poly_interpolate_nmod_vec_newton/ /poly/ /xs/ /ys/ /n/ /mod/ 
-- 
-- Forms the interpolating polynomial in the Newton basis using the method
-- of divided differences and then converts it to monomial form.
foreign import ccall "nmod_poly.h _nmod_poly_interpolate_nmod_vec_newton"
  _nmod_poly_interpolate_nmod_vec_newton :: Ptr CMp -> Ptr CMp -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_interpolate_nmod_vec_newton/ /poly/ /xs/ /ys/ /n/ 
-- 
-- Forms the interpolating polynomial in the Newton basis using the method
-- of divided differences and then converts it to monomial form.
foreign import ccall "nmod_poly.h nmod_poly_interpolate_nmod_vec_newton"
  nmod_poly_interpolate_nmod_vec_newton :: Ptr CNModPoly -> Ptr CMp -> Ptr CMp -> CLong -> IO ()

-- | /_nmod_poly_interpolate_nmod_vec_barycentric/ /poly/ /xs/ /ys/ /n/ /mod/ 
-- 
-- Forms the interpolating polynomial using a naive implementation of the
-- barycentric form of Lagrange interpolation.
foreign import ccall "nmod_poly.h _nmod_poly_interpolate_nmod_vec_barycentric"
  _nmod_poly_interpolate_nmod_vec_barycentric :: Ptr CMp -> Ptr CMp -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_interpolate_nmod_vec_barycentric/ /poly/ /xs/ /ys/ /n/ 
-- 
-- Forms the interpolating polynomial using a naive implementation of the
-- barycentric form of Lagrange interpolation.
foreign import ccall "nmod_poly.h nmod_poly_interpolate_nmod_vec_barycentric"
  nmod_poly_interpolate_nmod_vec_barycentric :: Ptr CNModPoly -> Ptr CMp -> Ptr CMp -> CLong -> IO ()

-- Composition -----------------------------------------------------------------

-- | /_nmod_poly_compose_horner/ /res/ /poly1/ /len1/ /poly2/ /len2/ /mod/ 
-- 
-- Composes @poly1@ of length @len1@ with @poly2@ of length @len2@ and sets
-- @res@ to the result, i.e.evaluates @poly1@ at @poly2@. The algorithm
-- used is Horner\'s algorithm. We require that @res@ have space for
-- @(len1 - 1)*(len2 - 1) + 1@ coefficients. It is assumed that @len1 > 0@
-- and @len2 > 0@.
foreign import ccall "nmod_poly.h _nmod_poly_compose_horner"
  _nmod_poly_compose_horner :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_compose_horner/ /res/ /poly1/ /poly2/ 
-- 
-- Composes @poly1@ with @poly2@ and sets @res@ to the result,
-- i.e.evaluates @poly1@ at @poly2@. The algorithm used is Horner\'s
-- algorithm.
foreign import ccall "nmod_poly.h nmod_poly_compose_horner"
  nmod_poly_compose_horner :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- -- | /_nmod_poly_compose_divconquer/ /res/ /poly1/ /len1/ /poly2/ /len2/ /mod/ 
-- -- 
-- -- Composes @poly1@ of length @len1@ with @poly2@ of length @len2@ and sets
-- -- @res@ to the result, i.e.evaluates @poly1@ at @poly2@. The algorithm
-- -- used is the divide and conquer algorithm. We require that @res@ have
-- -- space for @(len1 - 1)*(len2 - 1) + 1@ coefficients. It is assumed that
-- -- @len1 > 0@ and @len2 > 0@.
-- foreign import ccall "nmod_poly.h _nmod_poly_compose_divconquer"
--   _nmod_poly_compose_divconquer :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- -- | /nmod_poly_compose_divconquer/ /res/ /poly1/ /poly2/ 
-- -- 
-- -- Composes @poly1@ with @poly2@ and sets @res@ to the result,
-- -- i.e.evaluates @poly1@ at @poly2@. The algorithm used is the divide and
-- -- conquer algorithm.
-- foreign import ccall "nmod_poly.h nmod_poly_compose_divconquer"
--   nmod_poly_compose_divconquer :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- | /_nmod_poly_compose/ /res/ /poly1/ /len1/ /poly2/ /len2/ /mod/ 
-- 
-- Composes @poly1@ of length @len1@ with @poly2@ of length @len2@ and sets
-- @res@ to the result, i.e.evaluates @poly1@ at @poly2@. We require that
-- @res@ have space for @(len1 - 1)*(len2 - 1) + 1@ coefficients. It is
-- assumed that @len1 > 0@ and @len2 > 0@.
foreign import ccall "nmod_poly.h _nmod_poly_compose"
  _nmod_poly_compose :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_compose/ /res/ /poly1/ /poly2/ 
-- 
-- Composes @poly1@ with @poly2@ and sets @res@ to the result, that is,
-- evaluates @poly1@ at @poly2@.
foreign import ccall "nmod_poly.h nmod_poly_compose"
  nmod_poly_compose :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- Taylor shift ----------------------------------------------------------------

-- | /_nmod_poly_taylor_shift_horner/ /poly/ /c/ /len/ /mod/ 
-- 
-- Performs the Taylor shift composing @poly@ by \(x+c\) in-place. Uses an
-- efficient version Horner\'s rule.
foreign import ccall "nmod_poly.h _nmod_poly_taylor_shift_horner"
  _nmod_poly_taylor_shift_horner :: Ptr CMp -> CMpLimb -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_taylor_shift_horner/ /g/ /f/ /c/ 
-- 
-- Performs the Taylor shift composing @f@ by \(x+c\).
foreign import ccall "nmod_poly.h nmod_poly_taylor_shift_horner"
  nmod_poly_taylor_shift_horner :: Ptr CNModPoly -> Ptr CNModPoly -> CMpLimb -> IO ()

-- | /_nmod_poly_taylor_shift_convolution/ /poly/ /c/ /len/ /mod/ 
-- 
-- Performs the Taylor shift composing @poly@ by \(x+c\) in-place. Writes
-- the composition as a single convolution with cost \(O(M(n))\). We
-- require that the modulus is a prime at least as large as the length.
foreign import ccall "nmod_poly.h _nmod_poly_taylor_shift_convolution"
  _nmod_poly_taylor_shift_convolution :: Ptr CMp -> CMpLimb -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_taylor_shift_convolution/ /g/ /f/ /c/ 
-- 
-- Performs the Taylor shift composing @f@ by \(x+c\). Writes the
-- composition as a single convolution with cost \(O(M(n))\). We require
-- that the modulus is a prime at least as large as the length.
foreign import ccall "nmod_poly.h nmod_poly_taylor_shift_convolution"
  nmod_poly_taylor_shift_convolution :: Ptr CNModPoly -> Ptr CNModPoly -> CMpLimb -> IO ()

-- | /_nmod_poly_taylor_shift/ /poly/ /c/ /len/ /mod/ 
-- 
-- Performs the Taylor shift composing @poly@ by \(x+c\) in-place. We
-- require that the modulus is a prime.
foreign import ccall "nmod_poly.h _nmod_poly_taylor_shift"
  _nmod_poly_taylor_shift :: Ptr CMp -> CMpLimb -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_taylor_shift/ /g/ /f/ /c/ 
-- 
-- Performs the Taylor shift composing @f@ by \(x+c\). We require that the
-- modulus is a prime.
foreign import ccall "nmod_poly.h nmod_poly_taylor_shift"
  nmod_poly_taylor_shift :: Ptr CNModPoly -> Ptr CNModPoly -> CMpLimb -> IO ()

-- Modular composition ---------------------------------------------------------

-- | /_nmod_poly_compose_mod_horner/ /res/ /f/ /lenf/ /g/ /h/ /lenh/ /mod/ 
-- 
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero and that the length of \(g\) is one less than the
-- length of \(h\) (possibly with zero padding). The output is not allowed
-- to be aliased with any of the inputs.
-- 
-- The algorithm used is Horner\'s rule.
foreign import ccall "nmod_poly.h _nmod_poly_compose_mod_horner"
  _nmod_poly_compose_mod_horner :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_compose_mod_horner/ /res/ /f/ /g/ /h/ 
-- 
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero. The algorithm used is Horner\'s rule.
foreign import ccall "nmod_poly.h nmod_poly_compose_mod_horner"
  nmod_poly_compose_mod_horner :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- | /_nmod_poly_compose_mod_brent_kung/ /res/ /f/ /lenf/ /g/ /h/ /lenh/ /mod/ 
-- 
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero and that the length of \(g\) is one less than the
-- length of \(h\) (possibly with zero padding). We also require that the
-- length of \(f\) is less than the length of \(h\). The output is not
-- allowed to be aliased with any of the inputs.
-- 
-- The algorithm used is the Brent-Kung matrix algorithm.
foreign import ccall "nmod_poly.h _nmod_poly_compose_mod_brent_kung"
  _nmod_poly_compose_mod_brent_kung :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_compose_mod_brent_kung/ /res/ /f/ /g/ /h/ 
-- 
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero and that \(f\) has smaller degree than \(h\). The
-- algorithm used is the Brent-Kung matrix algorithm.
foreign import ccall "nmod_poly.h nmod_poly_compose_mod_brent_kung"
  nmod_poly_compose_mod_brent_kung :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- | /_nmod_poly_compose_mod_brent_kung_preinv/ /res/ /f/ /lenf/ /g/ /h/ /lenh/ /hinv/ /lenhinv/ /mod/ 
-- 
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero and that the length of \(g\) is one less than the
-- length of \(h\) (possibly with zero padding). We also require that the
-- length of \(f\) is less than the length of \(h\). Furthermore, we
-- require @hinv@ to be the inverse of the reverse of @h@. The output is
-- not allowed to be aliased with any of the inputs.
-- 
-- The algorithm used is the Brent-Kung matrix algorithm.
foreign import ccall "nmod_poly.h _nmod_poly_compose_mod_brent_kung_preinv"
  _nmod_poly_compose_mod_brent_kung_preinv :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_compose_mod_brent_kung_preinv/ /res/ /f/ /g/ /h/ /hinv/ 
-- 
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero and that \(f\) has smaller degree than \(h\).
-- Furthermore, we require @hinv@ to be the inverse of the reverse of @h@.
-- The algorithm used is the Brent-Kung matrix algorithm.
foreign import ccall "nmod_poly.h nmod_poly_compose_mod_brent_kung_preinv"
  nmod_poly_compose_mod_brent_kung_preinv :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- | /_nmod_poly_reduce_matrix_mod_poly/ /A/ /B/ /f/ 
-- 
-- Sets the ith row of @A@ to the reduction of the ith row of \(B\) modulo
-- \(f\) for \(i=1,\ldots,\sqrt{\deg(f)}\). We require \(B\) to be at least
-- a \(\sqrt{\deg(f)}\times \deg(f)\) matrix and \(f\) to be nonzero.
foreign import ccall "nmod_poly.h _nmod_poly_reduce_matrix_mod_poly"
  _nmod_poly_reduce_matrix_mod_poly :: Ptr CNModMat -> Ptr CNModMat -> Ptr CNModPoly -> IO ()

-- | /_nmod_poly_precompute_matrix_worker/ /arg_ptr/ 
-- 
-- Worker function version of @_nmod_poly_precompute_matrix@. Input\/output
-- is stored in @nmod_poly_matrix_precompute_arg_t@.
foreign import ccall "nmod_poly.h _nmod_poly_precompute_matrix_worker"
  _nmod_poly_precompute_matrix_worker :: Ptr () -> IO ()

-- | /_nmod_poly_precompute_matrix/ /A/ /f/ /g/ /leng/ /ginv/ /lenginv/ /mod/ 
-- 
-- Sets the ith row of @A@ to \(f^i\) modulo \(g\) for
-- \(i=1,\ldots,\sqrt{\deg(g)}\). We require \(A\) to be a
-- \(\sqrt{\deg(g)}\times \deg(g)\) matrix. We require @ginv@ to be the
-- inverse of the reverse of @g@ and \(g\) to be nonzero. @f@ has to be
-- reduced modulo @g@ and of length one less than @leng@ (possibly with
-- zero padding).
foreign import ccall "nmod_poly.h _nmod_poly_precompute_matrix"
  _nmod_poly_precompute_matrix :: Ptr CNModMat -> Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_precompute_matrix/ /A/ /f/ /g/ /ginv/ 
-- 
-- Sets the ith row of @A@ to \(f^i\) modulo \(g\) for
-- \(i=1,\ldots,\sqrt{\deg(g)}\). We require \(A\) to be a
-- \(\sqrt{\deg(g)}\times \deg(g)\) matrix. We require @ginv@ to be the
-- inverse of the reverse of @g@.
foreign import ccall "nmod_poly.h nmod_poly_precompute_matrix"
  nmod_poly_precompute_matrix :: Ptr CNModMat -> Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- | /_nmod_poly_compose_mod_brent_kung_precomp_preinv_worker/ /arg_ptr/ 
-- 
-- Worker function version of
-- @_nmod_poly_compose_mod_brent_kung_precomp_preinv@. Input\/output is
-- stored in @nmod_poly_compose_mod_precomp_preinv_arg_t@.
foreign import ccall "nmod_poly.h _nmod_poly_compose_mod_brent_kung_precomp_preinv_worker"
  _nmod_poly_compose_mod_brent_kung_precomp_preinv_worker :: Ptr ()  -> IO ()

-- | /_nmod_poly_compose_mod_brent_kung_precomp_preinv/ /res/ /f/ /lenf/ /A/ /h/ /lenh/ /hinv/ /lenhinv/ /mod/ 
-- 
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero. We require that the ith row of \(A\) contains \(g^i\)
-- for \(i=1,\ldots,\sqrt{\deg(h)}\), i.e. \(A\) is a
-- \(\sqrt{\deg(h)}\times \deg(h)\) matrix. We also require that the length
-- of \(f\) is less than the length of \(h\). Furthermore, we require
-- @hinv@ to be the inverse of the reverse of @h@. The output is not
-- allowed to be aliased with any of the inputs.
-- 
-- The algorithm used is the Brent-Kung matrix algorithm.
foreign import ccall "nmod_poly.h _nmod_poly_compose_mod_brent_kung_precomp_preinv"
  _nmod_poly_compose_mod_brent_kung_precomp_preinv :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CNModMat -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_compose_mod_brent_kung_precomp_preinv/ /res/ /f/ /A/ /h/ /hinv/ 
-- 
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that the
-- ith row of \(A\) contains \(g^i\) for \(i=1,\ldots,\sqrt{\deg(h)}\),
-- i.e. \(A\) is a \(\sqrt{\deg(h)}\times \deg(h)\) matrix. We require that
-- \(h\) is nonzero and that \(f\) has smaller degree than \(h\).
-- Furthermore, we require @hinv@ to be the inverse of the reverse of @h@.
-- This version of Brent-Kung modular composition is particularly useful if
-- one has to perform several modular composition of the form \(f(g)\)
-- modulo \(h\) for fixed \(g\) and \(h\).
foreign import ccall "nmod_poly.h nmod_poly_compose_mod_brent_kung_precomp_preinv"
  nmod_poly_compose_mod_brent_kung_precomp_preinv :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModMat -> Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- | /_nmod_poly_compose_mod_brent_kung_vec_preinv/ /res/ /polys/ /len1/ /l/ /g/ /leng/ /h/ /lenh/ /hinv/ /lenhinv/ /mod/ 
-- 
-- Sets @res@ to the composition \(f_i(g)\) modulo \(h\) for
-- \(1\leq i \leq l\), where \(f_i\) are the first @l@ elements of @polys@.
-- We require that \(h\) is nonzero and that the length of \(g\) is less
-- than the length of \(h\). We also require that the length of \(f_i\) is
-- less than the length of \(h\). We require @res@ to have enough memory
-- allocated to hold @l@ @nmod_poly_struct@\'s. The entries of @res@ need
-- to be initialised and @l@ needs to be less than @len1@ Furthermore, we
-- require @hinv@ to be the inverse of the reverse of @h@. The output is
-- not allowed to be aliased with any of the inputs.
-- 
-- The algorithm used is the Brent-Kung matrix algorithm.
foreign import ccall "nmod_poly.h _nmod_poly_compose_mod_brent_kung_vec_preinv"
  _nmod_poly_compose_mod_brent_kung_vec_preinv :: Ptr (Ptr CNModPoly) -> Ptr (Ptr CNModPoly) -> CLong -> CLong -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_compose_mod_brent_kung_vec_preinv/ /res/ /polys/ /len1/ /n/ /g/ /h/ /hinv/ 
-- 
-- Sets @res@ to the composition \(f_i(g)\) modulo \(h\) for
-- \(1\leq i \leq n\) where \(f_i\) are the first @n@ elements of @polys@.
-- We require @res@ to have enough memory allocated to hold @n@
-- @nmod_poly_struct@. The entries of @res@ need to be initialised and @n@
-- needs to be less than @len1@. We require that \(h\) is nonzero and that
-- \(f_i\) and \(g\) have smaller degree than \(h\). Furthermore, we
-- require @hinv@ to be the inverse of the reverse of @h@. No aliasing of
-- @res@ and @polys@ is allowed. The algorithm used is the Brent-Kung
-- matrix algorithm.
foreign import ccall "nmod_poly.h nmod_poly_compose_mod_brent_kung_vec_preinv"
  nmod_poly_compose_mod_brent_kung_vec_preinv :: Ptr (Ptr CNModPoly) -> Ptr (Ptr CNModPoly) -> CLong -> CLong -> Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- | /_nmod_poly_compose_mod_brent_kung_vec_preinv_threaded_pool/ /res/ /polys/ /lenpolys/ /l/ /g/ /glen/ /poly/ /len/ /polyinv/ /leninv/ /mod/ /threads/ /num_threads/ 
-- 
-- Multithreaded version of @_nmod_poly_compose_mod_brent_kung_vec_preinv@.
-- Distributing the Horner evaluations across @flint_get_num_threads@
-- threads.
foreign import ccall "nmod_poly.h _nmod_poly_compose_mod_brent_kung_vec_preinv_threaded_pool"
  _nmod_poly_compose_mod_brent_kung_vec_preinv_threaded_pool :: Ptr (Ptr CNModPoly) -> Ptr (Ptr CNModPoly) -> CLong -> CLong -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> Ptr CThreadPoolHandle -> CLong -> IO ()

-- | /nmod_poly_compose_mod_brent_kung_vec_preinv_threaded_pool/ /res/ /polys/ /len1/ /n/ /g/ /poly/ /polyinv/ /threads/ /num_threads/ 
-- 
-- Multithreaded version of @nmod_poly_compose_mod_brent_kung_vec_preinv@.
-- Distributing the Horner evaluations across @flint_get_num_threads@
-- threads.
foreign import ccall "nmod_poly.h nmod_poly_compose_mod_brent_kung_vec_preinv_threaded_pool"
  nmod_poly_compose_mod_brent_kung_vec_preinv_threaded_pool :: Ptr (Ptr CNModPoly) -> Ptr (Ptr CNModPoly) -> CLong -> CLong -> Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> Ptr CThreadPoolHandle -> CLong -> IO ()

-- | /nmod_poly_compose_mod_brent_kung_vec_preinv_threaded/ /res/ /polys/ /len1/ /n/ /g/ /poly/ /polyinv/ 
-- 
-- Multithreaded version of @nmod_poly_compose_mod_brent_kung_vec_preinv@.
-- Distributing the Horner evaluations across @flint_get_num_threads@
-- threads.
foreign import ccall "nmod_poly.h nmod_poly_compose_mod_brent_kung_vec_preinv_threaded"
  nmod_poly_compose_mod_brent_kung_vec_preinv_threaded :: Ptr (Ptr CNModPoly) -> Ptr (Ptr CNModPoly) -> CLong -> CLong -> Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- | /_nmod_poly_compose_mod/ /res/ /f/ /lenf/ /g/ /h/ /lenh/ /mod/ 
-- 
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero and that the length of \(g\) is one less than the
-- length of \(h\) (possibly with zero padding). The output is not allowed
-- to be aliased with any of the inputs.
foreign import ccall "nmod_poly.h _nmod_poly_compose_mod"
  _nmod_poly_compose_mod :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_compose_mod/ /res/ /f/ /g/ /h/ 
-- 
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero.
foreign import ccall "nmod_poly.h nmod_poly_compose_mod"
  nmod_poly_compose_mod :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- Greatest common divisor -----------------------------------------------------

-- | /_nmod_poly_gcd_euclidean/ /G/ /A/ /lenA/ /B/ /lenB/ /mod/ 
-- 
-- Computes the GCD of \(A\) of length @lenA@ and \(B\) of length @lenB@,
-- where @lenA >= lenB > 0@. The length of the GCD \(G\) is returned by the
-- function. No attempt is made to make the GCD monic. It is required that
-- \(G\) have space for @lenB@ coefficients.
foreign import ccall "nmod_poly.h _nmod_poly_gcd_euclidean"
  _nmod_poly_gcd_euclidean :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO CLong

-- | /nmod_poly_gcd_euclidean/ /G/ /A/ /B/ 
-- 
-- Computes the GCD of \(A\) and \(B\). The GCD of zero polynomials is
-- defined to be zero, whereas the GCD of the zero polynomial and some
-- other polynomial \(P\) is defined to be \(P\). Except in the case where
-- the GCD is zero, the GCD \(G\) is made monic.
foreign import ccall "nmod_poly.h nmod_poly_gcd_euclidean"
  nmod_poly_gcd_euclidean :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- | /_nmod_poly_hgcd/ /M/ /lenM/ /A/ /lenA/ /B/ /lenB/ /a/ /lena/ /b/ /lenb/ /mod/ 
-- 
-- Computes the HGCD of \(a\) and \(b\), that is, a matrix~\`M\`, a
-- sign~\`sigma\` and two polynomials \(A\) and \(B\) such that
-- 
-- \[`\]
-- \[(A,B)^t = M^{-1} (a,b)^t, \sigma = \det(M),\]
-- 
-- and \(A\) and \(B\) are consecutive remainders in the Euclidean
-- remainder sequence for the division of \(a\) by \(b\) satisfying deg(A)
-- ge frac{deg(a)}{2} > deg(B). Furthermore, \(M\) will be the product of
-- @[[q 1][1 0]]@ for the quotients @q@ generated by such a remainder
-- sequence. Assumes that
-- \(\operatorname{len}(a) > \operatorname{len}(b) > 0\), i.e.
-- \(\deg(a) > :math:`deg(b) > 1\).
-- 
-- Assumes that \(A\) and \(B\) have space of size at least
-- \(\operatorname{len}(a)\) and \(\operatorname{len}(b)\), respectively.
-- On exit, @*lenA@ and @*lenB@ will contain the correct lengths of \(A\)
-- and \(B\).
-- 
-- Assumes that @M[0]@, @M[1]@, @M[2]@, and @M[3]@ each point to a vector
-- of size at least \(\operatorname{len}(a)\).
foreign import ccall "nmod_poly.h _nmod_poly_hgcd"
  _nmod_poly_hgcd :: Ptr (Ptr CMp) -> Ptr CLong -> Ptr CMp -> Ptr CLong -> Ptr CMp -> Ptr CLong -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO CLong

-- | /_nmod_poly_gcd_hgcd/ /G/ /A/ /lenA/ /B/ /lenB/ /mod/ 
-- 
-- Computes the monic GCD of \(A\) and \(B\), assuming that
-- \(\operatorname{len}(A) \geq \operatorname{len}(B) > 0\).
-- 
-- Assumes that \(G\) has space for \(\operatorname{len}(B)\) coefficients
-- and returns the length of \(G\) on output.
foreign import ccall "nmod_poly.h _nmod_poly_gcd_hgcd"
  _nmod_poly_gcd_hgcd :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO CLong

-- | /nmod_poly_gcd_hgcd/ /G/ /A/ /B/ 
-- 
-- Computes the monic GCD of \(A\) and \(B\) using the HGCD algorithm.
-- 
-- As a special case, the GCD of two zero polynomials is defined to be the
-- zero polynomial.
-- 
-- The time complexity of the algorithm is \(\mathcal{O}(n \log^2 n)\). For
-- further details, see~< [ThullYap1990]>.
foreign import ccall "nmod_poly.h nmod_poly_gcd_hgcd"
  nmod_poly_gcd_hgcd :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- | /_nmod_poly_gcd/ /G/ /A/ /lenA/ /B/ /lenB/ /mod/ 
-- 
-- Computes the GCD of \(A\) of length @lenA@ and \(B\) of length @lenB@,
-- where @lenA >= lenB > 0@. The length of the GCD \(G\) is returned by the
-- function. No attempt is made to make the GCD monic. It is required that
-- \(G\) have space for @lenB@ coefficients.
foreign import ccall "nmod_poly.h _nmod_poly_gcd"
  _nmod_poly_gcd :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO CLong

-- | /nmod_poly_gcd/ /G/ /A/ /B/ 
-- 
-- Computes the GCD of \(A\) and \(B\). The GCD of zero polynomials is
-- defined to be zero, whereas the GCD of the zero polynomial and some
-- other polynomial \(P\) is defined to be \(P\). Except in the case where
-- the GCD is zero, the GCD \(G\) is made monic.
foreign import ccall "nmod_poly.h nmod_poly_gcd"
  nmod_poly_gcd :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- | /_nmod_poly_xgcd_euclidean/ /G/ /S/ /T/ /A/ /A_len/ /B/ /B_len/ /mod/ 
-- 
-- Computes the GCD of \(A\) and \(B\) together with cofactors \(S\) and
-- \(T\) such that \(S A + T B = G\). Returns the length of \(G\).
-- 
-- Assumes that \(\operatorname{len}(A) \geq \operatorname{len}(B) \geq 1\)
-- and \((\operatorname{len}(A),\operatorname{len}(B)) \neq (1,1)\).
-- 
-- No attempt is made to make the GCD monic.
-- 
-- Requires that \(G\) have space for \(\operatorname{len}(B)\)
-- coefficients. Writes \(\operatorname{len}(B)-1\) and
-- \(\operatorname{len}(A)-1\) coefficients to \(S\) and \(T\),
-- respectively. Note that, in fact,
-- \(\operatorname{len}(S) \leq \max(\operatorname{len}(B) - \operatorname{len}(G), 1)\)
-- and
-- \(\operatorname{len}(T) \leq \max(\operatorname{len}(A) - \operatorname{len}(G), 1)\).
-- 
-- No aliasing of input and output operands is permitted.
foreign import ccall "nmod_poly.h _nmod_poly_xgcd_euclidean"
  _nmod_poly_xgcd_euclidean :: Ptr CMp -> Ptr CMp -> Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO CLong

-- | /nmod_poly_xgcd_euclidean/ /G/ /S/ /T/ /A/ /B/ 
-- 
-- Computes the GCD of \(A\) and \(B\). The GCD of zero polynomials is
-- defined to be zero, whereas the GCD of the zero polynomial and some
-- other polynomial \(P\) is defined to be \(P\). Except in the case where
-- the GCD is zero, the GCD \(G\) is made monic.
-- 
-- Polynomials @S@ and @T@ are computed such that @S*A + T*B = G@. The
-- length of @S@ will be at most @lenB@ and the length of @T@ will be at
-- most @lenA@.
foreign import ccall "nmod_poly.h nmod_poly_xgcd_euclidean"
  nmod_poly_xgcd_euclidean :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- | /_nmod_poly_xgcd_hgcd/ /G/ /S/ /T/ /A/ /A_len/ /B/ /B_len/ /mod/ 
-- 
-- Computes the GCD of \(A\) and \(B\), where
-- \(\operatorname{len}(A) \geq \operatorname{len}(B) > 0\), together with
-- cofactors \(S\) and \(T\) such that \(S A + T B = G\). Returns the
-- length of \(G\).
-- 
-- No attempt is made to make the GCD monic.
-- 
-- Requires that \(G\) have space for \(\operatorname{len}(B)\)
-- coefficients. Writes \(\operatorname{len}(B) - 1\) and
-- \(\operatorname{len}(A) - 1\) coefficients to \(S\) and \(T\),
-- respectively. Note that, in fact,
-- \(\operatorname{len}(S) \leq \operatorname{len}(B) - \operatorname{len}(G)\)
-- and
-- \(\operatorname{len}(T) \leq \operatorname{len}(A) - \operatorname{len}(G)\).
-- 
-- Both \(S\) and \(T\) must have space for at least \(2\) coefficients.
-- 
-- No aliasing of input and output operands is permitted.
foreign import ccall "nmod_poly.h _nmod_poly_xgcd_hgcd"
  _nmod_poly_xgcd_hgcd :: Ptr CMp -> Ptr CMp -> Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO CLong

-- | /nmod_poly_xgcd_hgcd/ /G/ /S/ /T/ /A/ /B/ 
-- 
-- Computes the GCD of \(A\) and \(B\). The GCD of zero polynomials is
-- defined to be zero, whereas the GCD of the zero polynomial and some
-- other polynomial \(P\) is defined to be \(P\). Except in the case where
-- the GCD is zero, the GCD \(G\) is made monic.
-- 
-- Polynomials @S@ and @T@ are computed such that @S*A + T*B = G@. The
-- length of @S@ will be at most @lenB@ and the length of @T@ will be at
-- most @lenA@.
foreign import ccall "nmod_poly.h nmod_poly_xgcd_hgcd"
  nmod_poly_xgcd_hgcd :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- | /_nmod_poly_xgcd/ /G/ /S/ /T/ /A/ /lenA/ /B/ /lenB/ /mod/ 
-- 
-- Computes the GCD of \(A\) and \(B\), where
-- \(\operatorname{len}(A) \geq \operatorname{len}(B) > 0\), together with
-- cofactors \(S\) and \(T\) such that \(S A + T B = G\). Returns the
-- length of \(G\).
-- 
-- No attempt is made to make the GCD monic.
-- 
-- Requires that \(G\) have space for \(\operatorname{len}(B)\)
-- coefficients. Writes \(\operatorname{len}(B) - 1\) and
-- \(\operatorname{len}(A) - 1\) coefficients to \(S\) and \(T\),
-- respectively. Note that, in fact,
-- \(\operatorname{len}(S) \leq \operatorname{len}(B) - \operatorname{len}(G)\)
-- and
-- \(\operatorname{len}(T) \leq \operatorname{len}(A) - \operatorname{len}(G)\).
-- 
-- No aliasing of input and output operands is permitted.
foreign import ccall "nmod_poly.h _nmod_poly_xgcd"
  _nmod_poly_xgcd :: Ptr CMp -> Ptr CMp -> Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO CLong

-- | /nmod_poly_xgcd/ /G/ /S/ /T/ /A/ /B/ 
-- 
-- Computes the GCD of \(A\) and \(B\). The GCD of zero polynomials is
-- defined to be zero, whereas the GCD of the zero polynomial and some
-- other polynomial \(P\) is defined to be \(P\). Except in the case where
-- the GCD is zero, the GCD \(G\) is made monic.
-- 
-- The polynomials @S@ and @T@ are set such that @S*A + T*B = G@. The
-- length of @S@ will be at most @lenB@ and the length of @T@ will be at
-- most @lenA@.
foreign import ccall "nmod_poly.h nmod_poly_xgcd"
  nmod_poly_xgcd :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- | /_nmod_poly_resultant_euclidean/ /poly1/ /len1/ /poly2/ /len2/ /mod/ 
-- 
-- Returns the resultant of @(poly1, len1)@ and @(poly2, len2)@ using the
-- Euclidean algorithm.
-- 
-- Assumes that @len1 >= len2 > 0@.
-- 
-- Assumes that the modulus is prime.
foreign import ccall "nmod_poly.h _nmod_poly_resultant_euclidean"
  _nmod_poly_resultant_euclidean :: Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO CMpLimb

-- | /nmod_poly_resultant_euclidean/ /f/ /g/ 
-- 
-- Computes the resultant of \(f\) and \(g\) using the Euclidean algorithm.
-- 
-- For two non-zero polynomials \(f(x) = a_m x^m + \dotsb + a_0\) and
-- \(g(x) = b_n x^n + \dotsb + b_0\) of degrees \(m\) and \(n\), the
-- resultant is defined to be
-- 
-- \[`
-- a_m^n b_n^m \prod_{(x, y) : f(x) = g(y) = 0} (x - y).\]
-- 
-- For convenience, we define the resultant to be equal to zero if either
-- of the two polynomials is zero.
foreign import ccall "nmod_poly.h nmod_poly_resultant_euclidean"
  nmod_poly_resultant_euclidean :: Ptr CNModPoly -> Ptr CNModPoly -> IO CMpLimb

-- | /_nmod_poly_resultant_hgcd/ /poly1/ /len1/ /poly2/ /len2/ /mod/ 
-- 
-- Returns the resultant of @(poly1, len1)@ and @(poly2, len2)@ using the
-- half-gcd algorithm.
-- 
-- This algorithm computes the half-gcd as per @_nmod_poly_gcd_hgcd@ but
-- additionally updates the resultant every time a division occurs. The
-- half-gcd algorithm computes the GCD recursively. Given inputs \(a\) and
-- \(b\) it lets @m = len(a)\/2@ and (recursively) performs all quotients
-- in the Euclidean algorithm which do not require the low \(m\)
-- coefficients of \(a\) and \(b\).
-- 
-- This performs quotients in exactly the same order as the ordinary
-- Euclidean algorithm except that the low \(m\) coefficients of the
-- polynomials in the remainder sequence are not computed. A correction
-- step after hgcd has been called computes these low \(m\) coefficients
-- (by matrix multiplication by a transformation matrix also computed by
-- hgcd).
-- 
-- This means that from the point of view of the resultant, all but the
-- last quotient performed by a recursive call to hgcd is an ordinary
-- quotient as per the usual Euclidean algorithm. However, the final
-- quotient may give a remainder of less than \(m + 1\) coefficients, which
-- won\'t be corrected until the hgcd correction step is performed
-- afterwards.
-- 
-- To compute the adjustments to the resultant coming from this corrected
-- quotient, we save the relevant information in an @nmod_poly_res_t@
-- struct at the time the quotient is performed so that when the correction
-- step is performed later, the adjustments to the resultant can be
-- computed at that time also.
-- 
-- The only time an adjustment to the resultant is not required after a
-- call to hgcd is if hgcd does nothing (the remainder may already have had
-- less than \(m + 1\) coefficients when hgcd was called).
-- 
-- Assumes that @len1 >= len2 > 0@.
-- 
-- Assumes that the modulus is prime.
foreign import ccall "nmod_poly.h _nmod_poly_resultant_hgcd"
  _nmod_poly_resultant_hgcd :: Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO CMpLimb

-- | /nmod_poly_resultant_hgcd/ /f/ /g/ 
-- 
-- Computes the resultant of \(f\) and \(g\) using the half-gcd algorithm.
-- 
-- For two non-zero polynomials \(f(x) = a_m x^m + \dotsb + a_0\) and
-- \(g(x) = b_n x^n + \dotsb + b_0\) of degrees \(m\) and \(n\), the
-- resultant is defined to be
-- 
-- \[`\]
-- \[a_m^n b_n^m \prod_{(x, y) : f(x) = g(y) = 0} (x - y).\]
-- 
-- For convenience, we define the resultant to be equal to zero if either
-- of the two polynomials is zero.
foreign import ccall "nmod_poly.h nmod_poly_resultant_hgcd"
  nmod_poly_resultant_hgcd :: Ptr CNModPoly -> Ptr CNModPoly -> IO CMpLimb

-- | /_nmod_poly_resultant/ /poly1/ /len1/ /poly2/ /len2/ /mod/ 
-- 
-- Returns the resultant of @(poly1, len1)@ and @(poly2, len2)@.
-- 
-- Assumes that @len1 >= len2 > 0@.
-- 
-- Assumes that the modulus is prime.
foreign import ccall "nmod_poly.h _nmod_poly_resultant"
  _nmod_poly_resultant :: Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO CMpLimb

-- | /nmod_poly_resultant/ /f/ /g/ 
-- 
-- Computes the resultant of \(f\) and \(g\).
-- 
-- For two non-zero polynomials \(f(x) = a_m x^m + \dotsb + a_0\) and
-- \(g(x) = b_n x^n + \dotsb + b_0\) of degrees \(m\) and \(n\), the
-- resultant is defined to be
-- 
-- \[`\]
-- \[a_m^n b_n^m \prod_{(x, y) : f(x) = g(y) = 0} (x - y).\]
-- 
-- For convenience, we define the resultant to be equal to zero if either
-- of the two polynomials is zero.
foreign import ccall "nmod_poly.h nmod_poly_resultant"
  nmod_poly_resultant :: Ptr CNModPoly -> Ptr CNModPoly -> IO CMpLimb

-- | /_nmod_poly_gcdinv/ /G/ /S/ /A/ /lenA/ /B/ /lenB/ /mod/ 
-- 
-- Computes @(G, lenA)@, @(S, lenB-1)@ such that \(G \cong S A \pmod{B}\),
-- returning the actual length of \(G\).
-- 
-- Assumes that \(0 < \operatorname{len}(A) < \operatorname{len}(B)\).
foreign import ccall "nmod_poly.h _nmod_poly_gcdinv"
  _nmod_poly_gcdinv :: Ptr CMp -> Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO CLong

-- | /nmod_poly_gcdinv/ /G/ /S/ /A/ /B/ 
-- 
-- Computes polynomials \(G\) and \(S\), both reduced modulo~\`B\`, such
-- that \(G \cong S A \pmod{B}\), where \(B\) is assumed to have
-- \(\operatorname{len}(B) \geq 2\).
-- 
-- In the case that \(A = 0 \pmod{B}\), returns \(G = S = 0\).
foreign import ccall "nmod_poly.h nmod_poly_gcdinv"
  nmod_poly_gcdinv :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- | /_nmod_poly_invmod/ /A/ /B/ /lenB/ /P/ /lenP/ /mod/ 
-- 
-- Attempts to set @(A, lenP-1)@ to the inverse of @(B, lenB)@ modulo the
-- polynomial @(P, lenP)@. Returns \(1\) if @(B, lenB)@ is invertible and
-- \(0\) otherwise.
-- 
-- Assumes that \(0 < \operatorname{len}(B) < \operatorname{len}(P)\), and
-- hence also \(\operatorname{len}(P) \geq 2\), but supports zero-padding
-- in @(B, lenB)@.
-- 
-- Does not support aliasing.
-- 
-- Assumes that \(mod\) is a prime number.
foreign import ccall "nmod_poly.h _nmod_poly_invmod"
  _nmod_poly_invmod :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO CInt

-- | /nmod_poly_invmod/ /A/ /B/ /P/ 
-- 
-- Attempts to set \(A\) to the inverse of \(B\) modulo \(P\) in the
-- polynomial ring \((\mathbf{Z}/p\mathbf{Z})[X]\), where we assume that
-- \(p\) is a prime number.
-- 
-- If \(\operatorname{len}(P) < 2\), raises an exception.
-- 
-- If the greatest common divisor of \(B\) and \(P\) is~\`1\`,
-- returns~\`1\` and sets \(A\) to the inverse of \(B\). Otherwise,
-- returns~\`0\` and the value of \(A\) on exit is undefined.
foreign import ccall "nmod_poly.h nmod_poly_invmod"
  nmod_poly_invmod :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> IO CInt

-- Power series composition ----------------------------------------------------

-- | /_nmod_poly_discriminant/ /poly/ /len/ /mod/ 
-- 
-- Return the discriminant of @(poly, len)@. Assumes @len > 1@.
foreign import ccall "nmod_poly.h _nmod_poly_discriminant"
  _nmod_poly_discriminant :: Ptr CMp -> CLong -> Ptr CNMod -> IO CMpLimb

-- | /nmod_poly_discriminant/ /f/ 
-- 
-- Return the discriminant of \(f\). We normalise the discriminant so that
-- \(\operatorname{disc}(f) = (-1)^(n(n-1)/2) \operatorname{res}(f, f') /
-- \operatorname{lc}(f)^(n - m - 2)\), where @n = len(f)@ and
-- @m = len(f\')@. Thus \(\operatorname{disc}(f) =
-- \operatorname{lc}(f)^(2n - 2) \prod_{i < j} (r_i - r_j)^2\), where
-- \(\operatorname{lc}(f)\) is the leading coefficient of \(f\) and \(r_i\)
-- are the roots of \(f\).
foreign import ccall "nmod_poly.h nmod_poly_discriminant"
  nmod_poly_discriminant :: Ptr CNModPoly -> IO CMpLimb

-- Power series composition ----------------------------------------------------

-- | /_nmod_poly_compose_series/ /res/ /poly1/ /len1/ /poly2/ /len2/ /n/ 
-- 
-- Sets @res@ to the composition of @poly1@ and @poly2@ modulo \(x^n\),
-- where the constant term of @poly2@ is required to be zero.
-- 
-- Assumes that @len1, len2, n > 0@, that @len1, len2 \<= n@, and that\\
-- @(len1-1) * (len2-1) + 1 \<= n@, and that @res@ has space for @n@
-- coefficients. Does not support aliasing between any of the inputs and
-- the output.
-- 
-- Wraps @_gr_poly_compose_series@ which chooses automatically between
-- various algorithms.
foreign import ccall "nmod_poly.h _nmod_poly_compose_series"
  _nmod_poly_compose_series :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> CLong -> IO ()

-- | /nmod_poly_compose_series/ /res/ /poly1/ /poly2/ /n/ 
-- 
-- Sets @res@ to the composition of @poly1@ and @poly2@ modulo \(x^n\),
-- where the constant term of @poly2@ is required to be zero.
foreign import ccall "nmod_poly.h nmod_poly_compose_series"
  nmod_poly_compose_series :: Ptr CNModPoly -> Ptr CNModPoly -> Ptr CNModPoly -> CLong -> IO ()

-- Power series reversion ------------------------------------------------------

-- | /_nmod_poly_revert_series_lagrange/ /Qinv/ /Q/ /n/ /mod/ 
-- 
-- Sets @Qinv@ to the compositional inverse or reversion of @Q@ as a power
-- series, i.e. computes \(Q^{-1}\) such that
-- \(Q(Q^{-1}(x)) = Q^{-1}(Q(x)) = x \bmod x^n\). The arguments must both
-- have length @n@ and may not be aliased.
-- 
-- It is required that \(Q_0 = 0\) and that \(Q_1\) as well as the integers
-- \(1, 2, \ldots, n-1\) are invertible modulo the modulus.
-- 
-- This implementation uses the Lagrange inversion formula.
foreign import ccall "nmod_poly.h _nmod_poly_revert_series_lagrange"
  _nmod_poly_revert_series_lagrange :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_revert_series_lagrange/ /Qinv/ /Q/ /n/ 
-- 
-- Sets @Qinv@ to the compositional inverse or reversion of @Q@ as a power
-- series, i.e. computes \(Q^{-1}\) such that
-- \(Q(Q^{-1}(x)) = Q^{-1}(Q(x)) = x \bmod x^n\).
-- 
-- It is required that \(Q_0 = 0\) and that \(Q_1\) as well as the integers
-- \(1, 2, \ldots, n-1\) are invertible modulo the modulus.
-- 
-- This implementation uses the Lagrange inversion formula.
foreign import ccall "nmod_poly.h nmod_poly_revert_series_lagrange"
  nmod_poly_revert_series_lagrange :: Ptr CNModPoly -> Ptr CNModPoly -> CLong -> IO ()

-- | /_nmod_poly_revert_series_lagrange_fast/ /Qinv/ /Q/ /n/ /mod/ 
-- 
-- Sets @Qinv@ to the compositional inverse or reversion of @Q@ as a power
-- series, i.e. computes \(Q^{-1}\) such that
-- \(Q(Q^{-1}(x)) = Q^{-1}(Q(x)) = x \bmod x^n\). The arguments must both
-- have length @n@ and may not be aliased.
-- 
-- It is required that \(Q_0 = 0\) and that \(Q_1\) as well as the integers
-- \(1, 2, \ldots, n-1\) are invertible modulo the modulus.
-- 
-- This implementation uses a reduced-complexity implementation of the
-- Lagrange inversion formula.
foreign import ccall "nmod_poly.h _nmod_poly_revert_series_lagrange_fast"
  _nmod_poly_revert_series_lagrange_fast :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_revert_series_lagrange_fast/ /Qinv/ /Q/ /n/ 
-- 
-- Sets @Qinv@ to the compositional inverse or reversion of @Q@ as a power
-- series, i.e. computes \(Q^{-1}\) such that
-- \(Q(Q^{-1}(x)) = Q^{-1}(Q(x)) = x \bmod x^n\).
-- 
-- It is required that \(Q_0 = 0\) and that \(Q_1\) as well as the integers
-- \(1, 2, \ldots, n-1\) are invertible modulo the modulus.
-- 
-- This implementation uses a reduced-complexity implementation of the
-- Lagrange inversion formula.
foreign import ccall "nmod_poly.h nmod_poly_revert_series_lagrange_fast"
  nmod_poly_revert_series_lagrange_fast :: Ptr CNModPoly -> Ptr CNModPoly -> CLong -> IO ()

-- | /_nmod_poly_revert_series_newton/ /Qinv/ /Q/ /n/ /mod/ 
-- 
-- Sets @Qinv@ to the compositional inverse or reversion of @Q@ as a power
-- series, i.e. computes \(Q^{-1}\) such that
-- \(Q(Q^{-1}(x)) = Q^{-1}(Q(x)) = x \bmod x^n\). The arguments must both
-- have length @n@ and may not be aliased.
-- 
-- It is required that \(Q_0 = 0\) and that \(Q_1\) as well as the integers
-- \(1, 2, \ldots, n-1\) are invertible modulo the modulus.
-- 
-- This implementation uses Newton iteration < [BrentKung1978]>.
foreign import ccall "nmod_poly.h _nmod_poly_revert_series_newton"
  _nmod_poly_revert_series_newton :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_revert_series_newton/ /Qinv/ /Q/ /n/ 
-- 
-- Sets @Qinv@ to the compositional inverse or reversion of @Q@ as a power
-- series, i.e. computes \(Q^{-1}\) such that
-- \(Q(Q^{-1}(x)) = Q^{-1}(Q(x)) = x \bmod x^n\).
-- 
-- It is required that \(Q_0 = 0\) and that \(Q_1\) as well as the integers
-- \(1, 2, \ldots, n-1\) are invertible modulo the modulus.
-- 
-- This implementation uses Newton iteration < [BrentKung1978]>.
foreign import ccall "nmod_poly.h nmod_poly_revert_series_newton"
  nmod_poly_revert_series_newton :: Ptr CNModPoly -> Ptr CNModPoly -> CLong -> IO ()

-- | /_nmod_poly_revert_series/ /Qinv/ /Q/ /n/ /mod/ 
-- 
-- Sets @Qinv@ to the compositional inverse or reversion of @Q@ as a power
-- series, i.e. computes \(Q^{-1}\) such that
-- \(Q(Q^{-1}(x)) = Q^{-1}(Q(x)) = x \bmod x^n\). The arguments must both
-- have length @n@ and may not be aliased.
-- 
-- It is required that \(Q_0 = 0\) and that \(Q_1\) as well as the integers
-- \(1, 2, \ldots, n-1\) are invertible modulo the modulus.
-- 
-- This implementation automatically chooses between the Lagrange inversion
-- formula and Newton iteration based on the size of the input.
foreign import ccall "nmod_poly.h _nmod_poly_revert_series"
  _nmod_poly_revert_series :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_revert_series/ /Qinv/ /Q/ /n/ 
-- 
-- Sets @Qinv@ to the compositional inverse or reversion of @Q@ as a power
-- series, i.e. computes \(Q^{-1}\) such that
-- \(Q(Q^{-1}(x)) = Q^{-1}(Q(x)) = x \bmod x^n\).
-- 
-- It is required that \(Q_0 = 0\) and that \(Q_1\) as well as the integers
-- \(1, 2, \ldots, n-1\) are invertible modulo the modulus.
-- 
-- This implementation automatically chooses between the Lagrange inversion
-- formula and Newton iteration based on the size of the input.
foreign import ccall "nmod_poly.h nmod_poly_revert_series"
  nmod_poly_revert_series :: Ptr CNModPoly -> Ptr CNModPoly -> CLong -> IO ()

-- Square roots ----------------------------------------------------------------

-- The series expansions for \(\sqrt{h}\) and \(1/\sqrt{h}\) are defined by
-- means of the generalised binomial theorem
-- @h^r = (1+y)^r = \\sum_{k=0}^{\\infty} {r \\choose k} y^k.@ It is
-- assumed that \(h\) has constant term \(1\) and that the coefficients
-- 2^{-k} exist in the coefficient ring (i.e. \(2\) must be invertible).
--
-- | /_nmod_poly_invsqrt_series/ /g/ /h/ /hlen/ /n/ /mod/ 
-- 
-- Set the first \(n\) terms of \(g\) to the series expansion of
-- \(1/\sqrt{h}\). It is assumed that \(n > 0\), that \(h\) has constant
-- term 1. Aliasing is not permitted.
foreign import ccall "nmod_poly.h _nmod_poly_invsqrt_series"
  _nmod_poly_invsqrt_series :: Ptr CMp -> Ptr CMp -> CLong -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_invsqrt_series/ /g/ /h/ /n/ 
-- 
-- Set \(g\) to the series expansion of \(1/\sqrt{h}\) to order \(O(x^n)\).
-- It is assumed that \(h\) has constant term 1.
foreign import ccall "nmod_poly.h nmod_poly_invsqrt_series"
  nmod_poly_invsqrt_series :: Ptr CNModPoly -> Ptr CNModPoly -> CLong -> IO ()

-- | /_nmod_poly_sqrt_series/ /g/ /h/ /hlen/ /n/ /mod/ 
-- 
-- Set the first \(n\) terms of \(g\) to the series expansion of
-- \(\sqrt{h}\). It is assumed that \(n > 0\), that \(h\) has constant term
-- 1. Aliasing is not permitted.
foreign import ccall "nmod_poly.h _nmod_poly_sqrt_series"
  _nmod_poly_sqrt_series :: Ptr CMp -> Ptr CMp -> CLong -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_sqrt_series/ /g/ /h/ /n/ 
-- 
-- Set \(g\) to the series expansion of \(\sqrt{h}\) to order \(O(x^n)\).
-- It is assumed that \(h\) has constant term 1.
foreign import ccall "nmod_poly.h nmod_poly_sqrt_series"
  nmod_poly_sqrt_series :: Ptr CNModPoly -> Ptr CNModPoly -> CLong -> IO ()

-- | /_nmod_poly_sqrt/ /s/ /p/ /n/ /mod/ 
-- 
-- If @(p, n)@ is a perfect square, sets @(s, n \/ 2 + 1)@ to a square root
-- of \(p\) and returns 1. Otherwise returns 0.
foreign import ccall "nmod_poly.h _nmod_poly_sqrt"
  _nmod_poly_sqrt :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CNMod -> IO CInt

-- | /nmod_poly_sqrt/ /s/ /p/ 
-- 
-- If \(p\) is a perfect square, sets \(s\) to a square root of \(p\) and
-- returns 1. Otherwise returns 0.
foreign import ccall "nmod_poly.h nmod_poly_sqrt"
  nmod_poly_sqrt :: Ptr CNModPoly -> Ptr CNModPoly -> IO CInt

-- Power sums ------------------------------------------------------------------

-- | /_nmod_poly_power_sums_naive/ /res/ /poly/ /len/ /n/ /mod/ 
-- 
-- Compute the (truncated) power sums series of the polynomial @(poly,len)@
-- up to length \(n\) using Newton identities.
foreign import ccall "nmod_poly.h _nmod_poly_power_sums_naive"
  _nmod_poly_power_sums_naive :: Ptr CMp -> Ptr CMp -> CLong -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_power_sums_naive/ /res/ /poly/ /n/ 
-- 
-- Compute the (truncated) power sum series of the polynomial @poly@ up to
-- length \(n\) using Newton identities.
foreign import ccall "nmod_poly.h nmod_poly_power_sums_naive"
  nmod_poly_power_sums_naive :: Ptr CNModPoly -> Ptr CNModPoly -> CLong -> IO ()

-- | /_nmod_poly_power_sums_schoenhage/ /res/ /poly/ /len/ /n/ /mod/ 
-- 
-- Compute the (truncated) power sums series of the polynomial @(poly,len)@
-- up to length \(n\) using a series expansion (a formula due to
-- Schoenhage).
foreign import ccall "nmod_poly.h _nmod_poly_power_sums_schoenhage"
  _nmod_poly_power_sums_schoenhage :: Ptr CMp -> Ptr CMp -> CLong -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_power_sums_schoenhage/ /res/ /poly/ /n/ 
-- 
-- Compute the (truncated) power sums series of the polynomial @poly@ up to
-- length \(n\) using a series expansion (a formula due to Schoenhage).
foreign import ccall "nmod_poly.h nmod_poly_power_sums_schoenhage"
  nmod_poly_power_sums_schoenhage :: Ptr CNModPoly -> Ptr CNModPoly -> CLong -> IO ()

-- | /_nmod_poly_power_sums/ /res/ /poly/ /len/ /n/ /mod/ 
-- 
-- Compute the (truncated) power sums series of the polynomial @(poly,len)@
-- up to length \(n\).
foreign import ccall "nmod_poly.h _nmod_poly_power_sums"
  _nmod_poly_power_sums :: Ptr CMp -> Ptr CMp -> CLong -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_power_sums/ /res/ /poly/ /n/ 
-- 
-- Compute the (truncated) power sums series of the polynomial @poly@ up to
-- length \(n\).
foreign import ccall "nmod_poly.h nmod_poly_power_sums"
  nmod_poly_power_sums :: Ptr CNModPoly -> Ptr CNModPoly -> CLong -> IO ()

-- | /_nmod_poly_power_sums_to_poly_naive/ /res/ /poly/ /len/ /mod/ 
-- 
-- Compute the (monic) polynomial given by its power sums series
-- @(poly,len)@ using Newton identities.
foreign import ccall "nmod_poly.h _nmod_poly_power_sums_to_poly_naive"
  _nmod_poly_power_sums_to_poly_naive :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_power_sums_to_poly_naive/ /res/ /Q/ 
-- 
-- Compute the (monic) polynomial given by its power sums series @Q@ using
-- Newton identities.
foreign import ccall "nmod_poly.h nmod_poly_power_sums_to_poly_naive"
  nmod_poly_power_sums_to_poly_naive :: Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- | /_nmod_poly_power_sums_to_poly_schoenhage/ /res/ /poly/ /len/ /mod/ 
-- 
-- Compute the (monic) polynomial given by its power sums series
-- @(poly,len)@ using series expansion (a formula due to Schoenhage).
foreign import ccall "nmod_poly.h _nmod_poly_power_sums_to_poly_schoenhage"
  _nmod_poly_power_sums_to_poly_schoenhage :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_power_sums_to_poly_schoenhage/ /res/ /Q/ 
-- 
-- Compute the (monic) polynomial given by its power sums series @Q@ using
-- series expansion (a formula due to Schoenhage).
foreign import ccall "nmod_poly.h nmod_poly_power_sums_to_poly_schoenhage"
  nmod_poly_power_sums_to_poly_schoenhage :: Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- | /_nmod_poly_power_sums_to_poly/ /res/ /poly/ /len/ /mod/ 
-- 
-- Compute the (monic) polynomial given by its power sums series
-- @(poly,len)@.
foreign import ccall "nmod_poly.h _nmod_poly_power_sums_to_poly"
  _nmod_poly_power_sums_to_poly :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_power_sums_to_poly/ /res/ /Q/ 
-- 
-- Compute the (monic) polynomial given by its power sums series @Q@.
foreign import ccall "nmod_poly.h nmod_poly_power_sums_to_poly"
  nmod_poly_power_sums_to_poly :: Ptr CNModPoly -> Ptr CNModPoly -> IO ()

-- Transcendental functions ----------------------------------------------------

-- The elementary transcendental functions of a formal power series \(h\)
-- are defined as
--
-- exp(h(x)) = sum_{k=0}^{infty} frac{(h(x))^k}{k!}
--
-- log(h(x)) = int_0^x frac{h\'(t)}{h(t)} dt
--
-- operatorname{atan}(h(x)) = int_0^xfrac{h\'(t)}{1+(h(t))^2} dt
--
-- operatorname{atanh}(h(x)) = int_0^xfrac{h\'(t)}{1-(h(t))^2} dt
--
-- operatorname{asin}(h(x)) = int_0^xfrac{h\'(t)}{sqrt{1-(h(t))^2}} dt
--
-- operatorname{asinh}(h(x)) = int_0^xfrac{h\'(t)}{sqrt{1+(h(t))^2}} dt
--
-- The functions sin, cos, tan, etc. are defined using standard inverse or
-- functional relations. The logarithm function assumes that \(h\) has
-- constant term \(1\). All other functions assume that \(h\) has constant
-- term \(0\). All functions assume that the coefficient \(1/k\) or
-- \(1/k!\) exists for all indices \(k\). When computing to order
-- \(O(x^n)\), the modulus \(p\) must therefore be a prime satisfying
-- \(p \ge n\). Further, we always require that \(p > 2\) in order to be
-- able to multiply by \(1/2\) for internal purposes. If the input does not
-- satisfy all these conditions, results are undefined. Except where
-- otherwise noted, functions are implemented with optimal (up to
-- constants) complexity \(O(M(n))\), where \(M(n)\) is the cost of
-- polynomial multiplication.
--
-- | /_nmod_poly_log_series/ /g/ /h/ /hlen/ /n/ /mod/ 
-- 
-- Set \(g = \log(h) + O(x^n)\). Assumes \(n > 0\) and @hlen > 0@. Aliasing
-- of \(g\) and \(h\) is allowed.
foreign import ccall "nmod_poly.h _nmod_poly_log_series"
  _nmod_poly_log_series :: Ptr CMp -> Ptr CMp -> CLong -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_log_series/ /g/ /h/ /n/ 
-- 
-- Set \(g = \log(h) + O(x^n)\). The case \(h = 1+cx^r\) is automatically
-- detected and handled efficiently.
foreign import ccall "nmod_poly.h nmod_poly_log_series"
  nmod_poly_log_series :: Ptr CNModPoly -> Ptr CNModPoly -> CLong -> IO ()

-- | /_nmod_poly_exp_series/ /f/ /h/ /hlen/ /n/ /mod/ 
-- 
-- Set \(f = \exp(h) + O(x^n)\) where @h@ is a polynomial. Assume
-- \(n > 0\). Aliasing of \(g\) and \(h\) is not allowed.
-- 
-- Uses Newton iteration (an improved version of the algorithm in
-- < [HanZim2004]>). For small \(n\), falls back to the basecase algorithm.
foreign import ccall "nmod_poly.h _nmod_poly_exp_series"
  _nmod_poly_exp_series :: Ptr CMp -> Ptr CMp -> CLong -> CLong -> Ptr CNMod -> IO ()

-- | /_nmod_poly_exp_expinv_series/ /f/ /g/ /h/ /n/ /mod/ 
-- 
-- Set \(f = \exp(h) + O(x^n)\) and \(g = \exp(-h) + O(x^n)\), more
-- efficiently for large \(n\) than performing a separate inversion to
-- obtain \(g\). Assumes \(n > 0\) and that \(h\) is zero-padded as
-- necessary to length \(n\). Aliasing is not allowed.
-- 
-- Uses Newton iteration (the version given in < [HanZim2004]>). For small
-- \(n\), falls back to the basecase algorithm.
foreign import ccall "nmod_poly.h _nmod_poly_exp_expinv_series"
  _nmod_poly_exp_expinv_series :: Ptr CMp -> Ptr CMp -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_exp_series/ /g/ /h/ /n/ 
-- 
-- Set \(g = \exp(h) + O(x^n)\). The case \(h = cx^r\) is automatically
-- detected and handled efficiently. Otherwise this function automatically
-- uses the basecase algorithm for small \(n\) and Newton iteration
-- otherwise.
foreign import ccall "nmod_poly.h nmod_poly_exp_series"
  nmod_poly_exp_series :: Ptr CNModPoly -> Ptr CNModPoly -> CLong -> IO ()

-- | /_nmod_poly_atan_series/ /g/ /h/ /n/ /mod/ 
-- 
-- Set \(g = \operatorname{atan}(h) + O(x^n)\). Assumes \(n > 0\). Aliasing
-- of \(g\) and \(h\) is allowed.
foreign import ccall "nmod_poly.h _nmod_poly_atan_series"
  _nmod_poly_atan_series :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_atan_series/ /g/ /h/ /n/ 
-- 
-- Set \(g = \operatorname{atan}(h) + O(x^n)\).
foreign import ccall "nmod_poly.h nmod_poly_atan_series"
  nmod_poly_atan_series :: Ptr CNModPoly -> Ptr CNModPoly -> CLong -> IO ()

-- | /_nmod_poly_atanh_series/ /g/ /h/ /n/ /mod/ 
-- 
-- Set \(g = \operatorname{atanh}(h) + O(x^n)\). Assumes \(n > 0\).
-- Aliasing of \(g\) and \(h\) is allowed.
foreign import ccall "nmod_poly.h _nmod_poly_atanh_series"
  _nmod_poly_atanh_series :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_atanh_series/ /g/ /h/ /n/ 
-- 
-- Set \(g = \operatorname{atanh}(h) + O(x^n)\).
foreign import ccall "nmod_poly.h nmod_poly_atanh_series"
  nmod_poly_atanh_series :: Ptr CNModPoly -> Ptr CNModPoly -> CLong -> IO ()

-- | /_nmod_poly_asin_series/ /g/ /h/ /hlen/ /n/ /mod/ 
-- 
-- Set \(g = \operatorname{asin}(h) + O(x^n)\). Assumes \(n > 0\). Aliasing
-- of \(g\) and \(h\) is allowed.
foreign import ccall "nmod_poly.h _nmod_poly_asin_series"
  _nmod_poly_asin_series :: Ptr CMp -> Ptr CMp -> CLong -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_asin_series/ /g/ /h/ /n/ 
-- 
-- Set \(g = \operatorname{asin}(h) + O(x^n)\).
foreign import ccall "nmod_poly.h nmod_poly_asin_series"
  nmod_poly_asin_series :: Ptr CNModPoly -> Ptr CNModPoly -> CLong -> IO ()

-- | /_nmod_poly_asinh_series/ /g/ /h/ /hlen/ /n/ /mod/ 
-- 
-- Set \(g = \operatorname{asinh}(h) + O(x^n)\). Assumes \(n > 0\).
-- Aliasing of \(g\) and \(h\) is allowed.
foreign import ccall "nmod_poly.h _nmod_poly_asinh_series"
  _nmod_poly_asinh_series :: Ptr CMp -> Ptr CMp -> CLong -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_asinh_series/ /g/ /h/ /n/ 
-- 
-- Set \(g = \operatorname{asinh}(h) + O(x^n)\).
foreign import ccall "nmod_poly.h nmod_poly_asinh_series"
  nmod_poly_asinh_series :: Ptr CNModPoly -> Ptr CNModPoly -> CLong -> IO ()

-- | /_nmod_poly_sin_series/ /g/ /h/ /n/ /mod/ 
-- 
-- Set \(g = \operatorname{sin}(h) + O(x^n)\). Assumes \(n > 0\) and that
-- \(h\) is zero-padded as necessary to length \(n\). Aliasing of \(g\) and
-- \(h\) is allowed. The value is computed using the identity
-- \(\sin(x) = 2 \tan(x/2)) / (1 + \tan^2(x/2)).\)
foreign import ccall "nmod_poly.h _nmod_poly_sin_series"
  _nmod_poly_sin_series :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_sin_series/ /g/ /h/ /n/ 
-- 
-- Set \(g = \operatorname{sin}(h) + O(x^n)\).
foreign import ccall "nmod_poly.h nmod_poly_sin_series"
  nmod_poly_sin_series :: Ptr CNModPoly -> Ptr CNModPoly -> CLong -> IO ()

-- | /_nmod_poly_cos_series/ /g/ /h/ /n/ /mod/ 
-- 
-- Set \(g = \operatorname{cos}(h) + O(x^n)\). Assumes \(n > 0\) and that
-- \(h\) is zero-padded as necessary to length \(n\). Aliasing of \(g\) and
-- \(h\) is allowed. The value is computed using the identity
-- \(\cos(x) = (1-\tan^2(x/2)) / (1 + \tan^2(x/2)).\)
foreign import ccall "nmod_poly.h _nmod_poly_cos_series"
  _nmod_poly_cos_series :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_cos_series/ /g/ /h/ /n/ 
-- 
-- Set \(g = \operatorname{cos}(h) + O(x^n)\).
foreign import ccall "nmod_poly.h nmod_poly_cos_series"
  nmod_poly_cos_series :: Ptr CNModPoly -> Ptr CNModPoly -> CLong -> IO ()

-- | /_nmod_poly_tan_series/ /g/ /h/ /n/ /mod/ 
-- 
-- Set \(g = \operatorname{tan}(h) + O(x^n)\). Assumes \(n > 0\) and that
-- \(h\) is zero-padded as necessary to length \(n\). Aliasing of \(g\) and
-- \(h\) is not allowed. Uses Newton iteration to invert the atan function.
foreign import ccall "nmod_poly.h _nmod_poly_tan_series"
  _nmod_poly_tan_series :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_tan_series/ /g/ /h/ /n/ 
-- 
-- Set \(g = \operatorname{tan}(h) + O(x^n)\).
foreign import ccall "nmod_poly.h nmod_poly_tan_series"
  nmod_poly_tan_series :: Ptr CNModPoly -> Ptr CNModPoly -> CLong -> IO ()

-- | /_nmod_poly_sinh_series/ /g/ /h/ /n/ /mod/ 
-- 
-- Set \(g = \operatorname{sinh}(h) + O(x^n)\). Assumes \(n > 0\) and that
-- \(h\) is zero-padded as necessary to length \(n\). Aliasing of \(g\) and
-- \(h\) is not allowed. Uses the identity \(\sinh(x) = (e^x - e^{-x})/2\).
foreign import ccall "nmod_poly.h _nmod_poly_sinh_series"
  _nmod_poly_sinh_series :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_sinh_series/ /g/ /h/ /n/ 
-- 
-- Set \(g = \operatorname{sinh}(h) + O(x^n)\).
foreign import ccall "nmod_poly.h nmod_poly_sinh_series"
  nmod_poly_sinh_series :: Ptr CNModPoly -> Ptr CNModPoly -> CLong -> IO ()

-- | /_nmod_poly_cosh_series/ /g/ /h/ /n/ /mod/ 
-- 
-- Set \(g = \operatorname{cos}(h) + O(x^n)\). Assumes \(n > 0\) and that
-- \(h\) is zero-padded as necessary to length \(n\). Aliasing of \(g\) and
-- \(h\) is not allowed. Uses the identity \(\cosh(x) = (e^x + e^{-x})/2\).
foreign import ccall "nmod_poly.h _nmod_poly_cosh_series"
  _nmod_poly_cosh_series :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_cosh_series/ /g/ /h/ /n/ 
-- 
-- Set \(g = \operatorname{cosh}(h) + O(x^n)\).
foreign import ccall "nmod_poly.h nmod_poly_cosh_series"
  nmod_poly_cosh_series :: Ptr CNModPoly -> Ptr CNModPoly -> CLong -> IO ()

-- | /_nmod_poly_tanh_series/ /g/ /h/ /n/ /mod/ 
-- 
-- Set \(g = \operatorname{tanh}(h) + O(x^n)\). Assumes \(n > 0\) and that
-- \(h\) is zero-padded as necessary to length \(n\). Uses the identity
-- \(\tanh(x) = (e^{2x}-1)/(e^{2x}+1)\).
foreign import ccall "nmod_poly.h _nmod_poly_tanh_series"
  _nmod_poly_tanh_series :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_tanh_series/ /g/ /h/ /n/ 
-- 
-- Set \(g = \operatorname{tanh}(h) + O(x^n)\).
foreign import ccall "nmod_poly.h nmod_poly_tanh_series"
  nmod_poly_tanh_series :: Ptr CNModPoly -> Ptr CNModPoly -> CLong -> IO ()

-- Products --------------------------------------------------------------------

-- | /_nmod_poly_product_roots_nmod_vec/ /poly/ /xs/ /n/ /mod/ 
-- 
-- Sets @(poly, n + 1)@ to the monic polynomial which is the product of
-- \((x - x_0)(x - x_1) \cdots (x - x_{n-1})\), the roots \(x_i\) being
-- given by @xs@.
-- 
-- Aliasing of the input and output is not allowed.
foreign import ccall "nmod_poly.h _nmod_poly_product_roots_nmod_vec"
  _nmod_poly_product_roots_nmod_vec :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /nmod_poly_product_roots_nmod_vec/ /poly/ /xs/ /n/ 
-- 
-- Sets @poly@ to the monic polynomial which is the product of
-- \((x - x_0)(x - x_1) \cdots (x - x_{n-1})\), the roots \(x_i\) being
-- given by @xs@.
foreign import ccall "nmod_poly.h nmod_poly_product_roots_nmod_vec"
  nmod_poly_product_roots_nmod_vec :: Ptr CNModPoly -> Ptr CMp -> CLong -> IO ()

-- | /nmod_poly_find_distinct_nonzero_roots/ /roots/ /A/ 
-- 
-- If @A@ has \(\deg(A)\) distinct nonzero roots in \(\mathbb{F}_p\), write
-- these roots out to @roots[0]@ to @roots[deg(A) - 1]@ and return @1@.
-- Otherwise, return @0@. It is assumed that @A@ is nonzero and that the
-- modulus of @A@ is prime. This function uses Rabin\'s probabilistic
-- method via gcd\'s with \((x + \delta)^{\frac{p-1}{2}} - 1\).
foreign import ccall "nmod_poly.h nmod_poly_find_distinct_nonzero_roots"
  nmod_poly_find_distinct_nonzero_roots :: Ptr CMpLimb -> Ptr CNModPoly -> IO CInt

-- Subproduct trees ------------------------------------------------------------

-- | /_nmod_poly_tree_alloc/ /len/ 
-- 
-- Allocates space for a subproduct tree of the given length, having linear
-- factors at the lowest level.
-- 
-- Entry \(i\) in the tree is a pointer to a single array of limbs, capable
-- of storing \(\lfloor n / 2^i \rfloor\) subproducts of degree \(2^i\)
-- adjacently, plus a trailing entry if \(n / 2^i\) is not an integer.
-- 
-- For example, a tree of length 7 built from monic linear factors has the
-- following structure, where spaces have been inserted for illustrative
-- purposes:
-- 
-- > X1 X1 X1 X1 X1 X1 X1
-- > XX1   XX1   XX1   X1
-- > XXXX1       XX1   X1
-- > XXXXXXX1
foreign import ccall "nmod_poly.h _nmod_poly_tree_alloc"
  _nmod_poly_tree_alloc :: CLong -> IO (Ptr (Ptr CMp))

-- | /_nmod_poly_tree_free/ /tree/ /len/ 
-- 
-- Free the allocated space for the subproduct.
foreign import ccall "nmod_poly.h _nmod_poly_tree_free"
  _nmod_poly_tree_free :: Ptr (Ptr CMp) -> CLong -> IO ()

-- | /_nmod_poly_tree_build/ /tree/ /roots/ /len/ /mod/ 
-- 
-- Builds a subproduct tree in the preallocated space from the @len@ monic
-- linear factors \((x-r_i)\). The top level product is not computed.
foreign import ccall "nmod_poly.h _nmod_poly_tree_build"
  _nmod_poly_tree_build :: Ptr (Ptr CMp) -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- Inflation and deflation -----------------------------------------------------

-- | /nmod_poly_inflate/ /result/ /input/ /inflation/ 
-- 
-- Sets @result@ to the inflated polynomial \(p(x^n)\) where \(p\) is given
-- by @input@ and \(n\) is given by @deflation@.
foreign import ccall "nmod_poly.h nmod_poly_inflate"
  nmod_poly_inflate :: Ptr CNModPoly -> Ptr CNModPoly -> CULong -> IO ()

-- | /nmod_poly_deflate/ /result/ /input/ /deflation/ 
-- 
-- Sets @result@ to the deflated polynomial \(p(x^{1/n})\) where \(p\) is
-- given by @input@ and \(n\) is given by @deflation@. Requires \(n > 0\).
foreign import ccall "nmod_poly.h nmod_poly_deflate"
  nmod_poly_deflate :: Ptr CNModPoly -> Ptr CNModPoly -> CULong -> IO ()

-- | /nmod_poly_deflation/ /input/ 
-- 
-- Returns the largest integer by which @input@ can be deflated. As special
-- cases, returns 0 if @input@ is the zero polynomial and 1 of @input@ is a
-- constant polynomial.
foreign import ccall "nmod_poly.h nmod_poly_deflation"
  nmod_poly_deflation :: Ptr CNModPoly -> IO CULong

-- Chinese Remaindering --------------------------------------------------------




-- | /nmod_poly_multi_crt_init/ /CRT/ 
-- 
-- Initialize @CRT@ for Chinese remaindering.
foreign import ccall "nmod_poly.h nmod_poly_multi_crt_init"
  nmod_poly_multi_crt_init :: Ptr CNModPolyMultiCRT -> IO ()

-- | /nmod_poly_multi_crt_precompute/ /CRT/ /moduli/ /len/ 
-- 
-- Configure @CRT@ for repeated Chinese remaindering of @moduli@. The
-- number of moduli, @len@, should be positive. A return of @0@ indicates
-- that the compilation failed and future calls to
-- @nmod_poly_multi_crt_precomp@ will leave the output undefined. A return
-- of @1@ indicates that the compilation was successful, which occurs if
-- and only if either (1) @len == 1@ and @modulus + 0@ is nonzero, or (2)
-- all of the moduli have positive degree and are pairwise relatively
-- prime.
foreign import ccall "nmod_poly.h nmod_poly_multi_crt_precompute"
  nmod_poly_multi_crt_precompute :: Ptr CNModPolyMultiCRT -> Ptr (Ptr CNModPoly) -> CLong -> IO CInt

-- | /nmod_poly_multi_crt_precomp/ /output/ /CRT/ /values/ 
-- 
-- Set @output@ to the polynomial of lowest possible degree that is
-- congruent to @values + i@ modulo the @moduli + i@ in
-- @nmod_poly_multi_crt_precompute@. The inputs
-- @values + 0, ..., values + len - 1@ where @len@ was used in
-- @nmod_poly_multi_crt_precompute@ are expected to be valid and have
-- modulus matching the modulus of the moduli used in
-- @nmod_poly_multi_crt_precompute@.
foreign import ccall "nmod_poly.h nmod_poly_multi_crt_precomp"
  nmod_poly_multi_crt_precomp :: Ptr CNModPoly -> Ptr CNModPolyMultiCRT -> Ptr (Ptr CNModPoly) -> IO ()

-- | /nmod_poly_multi_crt/ /output/ /moduli/ /values/ /len/ 
-- 
-- Perform the same operation as @nmod_poly_multi_crt_precomp@ while
-- internally constructing and destroying the precomputed data. All of the
-- remarks in @nmod_poly_multi_crt_precompute@ apply.
foreign import ccall "nmod_poly.h nmod_poly_multi_crt"
  nmod_poly_multi_crt :: Ptr CNModPoly -> Ptr (Ptr CNModPoly) -> Ptr (Ptr CNModPoly) -> CLong -> IO CInt

-- | /nmod_poly_multi_crt_clear/ /CRT/ 
-- 
-- Free all space used by @CRT@.
foreign import ccall "nmod_poly.h nmod_poly_multi_crt_clear"
  nmod_poly_multi_crt_clear :: Ptr CNModPolyMultiCRT -> IO ()

-- | /_nmod_poly_multi_crt_local_size/ /CRT/ 
-- 
-- Return the required length of the output for @_nmod_poly_multi_crt_run@.
foreign import ccall "nmod_poly.h _nmod_poly_multi_crt_local_size"
  _nmod_poly_multi_crt_local_size :: Ptr CNModPolyMultiCRT -> IO CLong

-- | /_nmod_poly_multi_crt_run/ /outputs/ /CRT/ /inputs/ 
-- 
-- Perform the same operation as @nmod_poly_multi_crt_precomp@ using
-- supplied temporary space. The actual output is placed in @outputs + 0@,
-- and @outputs@ should contain space for all temporaries and should be at
-- least as long as @_nmod_poly_multi_crt_local_size(CRT)@. Of course the
-- moduli of these temporaries should match the modulus of the inputs.
foreign import ccall "nmod_poly.h _nmod_poly_multi_crt_run"
  _nmod_poly_multi_crt_run :: Ptr (Ptr CNModPoly) -> Ptr CNModPolyMultiCRT -> Ptr (Ptr CNModPoly) -> IO ()

-- Berlekamp-Massey Algorithm --------------------------------------------------

-- | /nmod_berlekamp_massey_init/ /B/ /p/ 
-- 
-- Initialize @B@ in characteristic @p@ with an empty stream.
foreign import ccall "nmod_poly.h nmod_berlekamp_massey_init"
  nmod_berlekamp_massey_init :: Ptr CNModBerlekampMassey -> CMpLimb -> IO ()

-- | /nmod_berlekamp_massey_clear/ /B/ 
-- 
-- Free any space used by @B@.
foreign import ccall "nmod_poly.h nmod_berlekamp_massey_clear"
  nmod_berlekamp_massey_clear :: Ptr CNModBerlekampMassey -> IO ()

foreign import ccall "nmod_poly.h &nmod_berlekamp_massey_clear"
  p_nmod_berlekamp_massey_clear :: FunPtr (Ptr CNModBerlekampMassey -> IO ())

-- | /nmod_berlekamp_massey_start_over/ /B/ 
-- 
-- Empty the stream of points in @B@.
foreign import ccall "nmod_poly.h nmod_berlekamp_massey_start_over"
  nmod_berlekamp_massey_start_over :: Ptr CNModBerlekampMassey -> IO ()

-- | /nmod_berlekamp_massey_set_prime/ /B/ /p/ 
-- 
-- Set the characteristic of the field and empty the stream of points in
-- @B@.
foreign import ccall "nmod_poly.h nmod_berlekamp_massey_set_prime"
  nmod_berlekamp_massey_set_prime :: Ptr CNModBerlekampMassey -> CMpLimb -> IO ()

-- | /nmod_berlekamp_massey_add_points/ /B/ /a/ /count/ 
-- 
-- Add point(s) to the stream processed by @B@. The addition of any number
-- of points will not update the \(V\) and \(R\) polynomial.
foreign import ccall "nmod_poly.h nmod_berlekamp_massey_add_points"
  nmod_berlekamp_massey_add_points :: Ptr CNModBerlekampMassey -> Ptr CMpLimb -> CLong -> IO ()

-- | /nmod_berlekamp_massey_reduce/ /B/ 
-- 
-- Ensure that the polynomials \(V\) and \(R\) are up to date. The return
-- value is @1@ if this function changed \(V\) and @0@ otherwise. For
-- example, if this function is called twice in a row without adding any
-- points in between, the return of the second call should be @0@. As
-- another example, suppose the object is emptied, the points
-- \(1, 1, 2, 3\) are added, then reduce is called. This reduce should
-- return @1@ with \(\deg(R) < \deg(V) = 2\) because the Fibonacci sequence
-- has been recognized. The further addition of the two points \(5, 8\) and
-- a reduce will result in a return value of @0@.
foreign import ccall "nmod_poly.h nmod_berlekamp_massey_reduce"
  nmod_berlekamp_massey_reduce :: Ptr CNModBerlekampMassey -> IO CInt

-- | /nmod_berlekamp_massey_point_count/ /B/ 
-- 
-- Return the number of points stored in @B@.
foreign import ccall "nmod_poly.h nmod_berlekamp_massey_point_count"
  nmod_berlekamp_massey_point_count :: Ptr CNModBerlekampMassey -> IO CLong

-- | /nmod_berlekamp_massey_points/ /B/ 
-- 
-- Return a pointer to the array of points stored in @B@. This may be
-- @NULL@ if @nmod_berlekamp_massey_point_count@ returns @0@.
foreign import ccall "nmod_poly.h nmod_berlekamp_massey_points"
  nmod_berlekamp_massey_points :: Ptr CNModBerlekampMassey -> IO (Ptr CMpLimb)

-- | /nmod_berlekamp_massey_V_poly/ /B/ 
-- 
-- Return the polynomial \(V\) in @B@.
foreign import ccall "nmod_poly.h nmod_berlekamp_massey_V_poly"
  nmod_berlekamp_massey_V_poly :: Ptr CNModBerlekampMassey -> IO (Ptr (Ptr CNModPoly))

-- | /nmod_berlekamp_massey_R_poly/ /B/ 
-- 
-- Return the polynomial \(R\) in @B@.
foreign import ccall "nmod_poly.h nmod_berlekamp_massey_R_poly"
  nmod_berlekamp_massey_R_poly :: Ptr CNModBerlekampMassey -> IO (Ptr (Ptr CNModPoly))

