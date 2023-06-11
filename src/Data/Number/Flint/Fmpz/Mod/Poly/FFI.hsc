{-# language
    CApiFFI
  , FlexibleInstances
  , ForeignFunctionInterface
  , MultiParamTypeClasses
  , TupleSections
  , TypeFamilies
  #-}

module Data.Number.Flint.Fmpz.Mod.Poly.FFI (
  -- * Polynomials over integers mod n
    FmpzModPoly (..)
  , CFmpzModPoly (..)
  , newFmpzModPoly
  , withFmpzModPoly
  , withNewFmpzModPoly
  -- * Memory management
  , fmpz_mod_poly_init
  , fmpz_mod_poly_init2
  , fmpz_mod_poly_clear
  , fmpz_mod_poly_realloc
  , fmpz_mod_poly_fit_length
  , _fmpz_mod_poly_normalise
  , _fmpz_mod_poly_set_length
  , fmpz_mod_poly_truncate
  , fmpz_mod_poly_set_trunc
  -- * Randomisation
  , fmpz_mod_poly_randtest
  , fmpz_mod_poly_randtest_irreducible
  , fmpz_mod_poly_randtest_not_zero
  , fmpz_mod_poly_randtest_monic
  , fmpz_mod_poly_randtest_monic_irreducible
  , fmpz_mod_poly_randtest_monic_primitive
  , fmpz_mod_poly_randtest_trinomial
  , fmpz_mod_poly_randtest_trinomial_irreducible
  , fmpz_mod_poly_randtest_pentomial
  , fmpz_mod_poly_randtest_pentomial_irreducible
  , fmpz_mod_poly_randtest_sparse_irreducible
  -- * Attributes
  , fmpz_mod_poly_degree
  , fmpz_mod_poly_length
  , fmpz_mod_poly_lead
  -- * Assignment and basic manipulation
  , fmpz_mod_poly_set
  , fmpz_mod_poly_swap
  , fmpz_mod_poly_zero
  , fmpz_mod_poly_one
  , fmpz_mod_poly_zero_coeffs
  , fmpz_mod_poly_reverse
  -- * Conversion
  , fmpz_mod_poly_set_ui
  , fmpz_mod_poly_set_fmpz
  , fmpz_mod_poly_set_fmpz_poly
  , fmpz_mod_poly_get_fmpz_poly
  , fmpz_mod_poly_get_nmod_poly
  , fmpz_mod_poly_set_nmod_poly
  -- * Comparison
  , fmpz_mod_poly_equal
  , fmpz_mod_poly_equal_trunc
  , fmpz_mod_poly_is_zero
  , fmpz_mod_poly_is_one
  , fmpz_mod_poly_is_gen
  -- * Getting and setting coefficients
  , fmpz_mod_poly_set_coeff_fmpz
  , fmpz_mod_poly_set_coeff_ui
  , fmpz_mod_poly_get_coeff_fmpz
  -- , fmpz_mod_poly_set_coeff_mpz
  -- , fmpz_mod_poly_get_coeff_mpz
  -- * Shifting
  , _fmpz_mod_poly_shift_left
  , fmpz_mod_poly_shift_left
  , _fmpz_mod_poly_shift_right
  , fmpz_mod_poly_shift_right
  -- * Addition and subtraction
  , _fmpz_mod_poly_add
  , fmpz_mod_poly_add
  , fmpz_mod_poly_add_series
  , _fmpz_mod_poly_sub
  , fmpz_mod_poly_sub
  , fmpz_mod_poly_sub_series
  , _fmpz_mod_poly_neg
  , fmpz_mod_poly_neg
  -- * Scalar multiplication and division
  , _fmpz_mod_poly_scalar_mul_fmpz
  , fmpz_mod_poly_scalar_mul_fmpz
  , fmpz_mod_poly_scalar_addmul_fmpz
  , _fmpz_mod_poly_scalar_div_fmpz
  , fmpz_mod_poly_scalar_div_fmpz
  -- * Multiplication
  , _fmpz_mod_poly_mul
  , fmpz_mod_poly_mul
  , _fmpz_mod_poly_mullow
  , fmpz_mod_poly_mullow
  , _fmpz_mod_poly_sqr
  , fmpz_mod_poly_sqr
  , fmpz_mod_poly_mulhigh
  , _fmpz_mod_poly_mulmod
  , fmpz_mod_poly_mulmod
  , _fmpz_mod_poly_mulmod_preinv
  , fmpz_mod_poly_mulmod_preinv
  -- * Products
  , _fmpz_mod_poly_product_roots_fmpz_vec
  , fmpz_mod_poly_product_roots_fmpz_vec
  , fmpz_mod_poly_find_distinct_nonzero_roots
  , _fmpz_mod_poly_pow
  , fmpz_mod_poly_pow
  , _fmpz_mod_poly_pow_trunc
  , fmpz_mod_poly_pow_trunc
  , _fmpz_mod_poly_pow_trunc_binexp
  , fmpz_mod_poly_pow_trunc_binexp
  , _fmpz_mod_poly_powmod_ui_binexp
  , fmpz_mod_poly_powmod_ui_binexp
  , _fmpz_mod_poly_powmod_ui_binexp_preinv
  , fmpz_mod_poly_powmod_ui_binexp_preinv
  , _fmpz_mod_poly_powmod_fmpz_binexp
  , fmpz_mod_poly_powmod_fmpz_binexp
  , _fmpz_mod_poly_powmod_fmpz_binexp_preinv
  , fmpz_mod_poly_powmod_fmpz_binexp_preinv
  , _fmpz_mod_poly_powmod_x_fmpz_preinv
  , fmpz_mod_poly_powmod_x_fmpz_preinv
  , _fmpz_mod_poly_powers_mod_preinv_naive
  , fmpz_mod_poly_powers_mod_naive
  , _fmpz_mod_poly_powers_mod_preinv_threaded_pool
  , fmpz_mod_poly_powers_mod_bsgs
  , fmpz_mod_poly_frobenius_powers_2exp_precomp
  , fmpz_mod_poly_frobenius_powers_2exp_clear
  , fmpz_mod_poly_frobenius_power
  , fmpz_mod_poly_frobenius_powers_precomp
  , fmpz_mod_poly_frobenius_powers_clear
  -- * Division
  , _fmpz_mod_poly_divrem_basecase
  , fmpz_mod_poly_divrem_basecase
  , _fmpz_mod_poly_divrem_newton_n_preinv
  , fmpz_mod_poly_divrem_newton_n_preinv
  -- , _fmpz_mod_poly_div_basecase -- deprecated
  -- , fmpz_mod_poly_div_basecase -- deprecated
  -- , _fmpz_mod_poly_div_divconquer_recursive -- deprecated
  -- , _fmpz_mod_poly_div_newton -- deprecated
  -- , fmpz_mod_poly_div_newton -- deprecated
  , _fmpz_mod_poly_div_newton_n_preinv
  , fmpz_mod_poly_div_newton_n_preinv
  , fmpz_mod_poly_remove
  , _fmpz_mod_poly_rem_basecase
  , fmpz_mod_poly_rem_basecase
  -- , _fmpz_mod_poly_divrem_divconquer_recursive -- deprecated
  -- , _fmpz_mod_poly_divrem_divconquer -- deprecated
  -- , _fmpz_mod_poly_div_divconquer -- deprecated
  -- , fmpz_mod_poly_div_divconquer -- deprecated
  -- , fmpz_mod_poly_divrem_divconquer -- deprecated
  , _fmpz_mod_poly_div
  , fmpz_mod_poly_div
  , _fmpz_mod_poly_divrem
  , fmpz_mod_poly_divrem
  , fmpz_mod_poly_divrem_f
  , _fmpz_mod_poly_rem
  -- , _fmpz_mod_poly_rem_f
  -- , fmpz_mod_poly_rem
  -- * Divisibility testing
  , _fmpz_mod_poly_divides_classical
  , fmpz_mod_poly_divides_classical
  , _fmpz_mod_poly_divides
  , fmpz_mod_poly_divides
  -- * Power series inversion
  -- , _fmpz_mod_poly_inv_series_newton
  -- , fmpz_mod_poly_inv_series_newton
  -- , fmpz_mod_poly_inv_series_newton_f
  , _fmpz_mod_poly_inv_series
  , fmpz_mod_poly_inv_series
  , fmpz_mod_poly_inv_series_f
  -- * Power series division
  , _fmpz_mod_poly_div_series
  , fmpz_mod_poly_div_series
  -- * Greatest common divisor
  , fmpz_mod_poly_make_monic
  , fmpz_mod_poly_make_monic_f
  -- , _fmpz_mod_poly_gcd_euclidean
  -- , fmpz_mod_poly_gcd_euclidean
  , _fmpz_mod_poly_gcd
  , fmpz_mod_poly_gcd
  , _fmpz_mod_poly_gcd_euclidean_f
  , fmpz_mod_poly_gcd_euclidean_f
  , _fmpz_mod_poly_gcd_f
  , fmpz_mod_poly_gcd_f
  , _fmpz_mod_poly_hgcd
  -- , _fmpz_mod_poly_gcd_hgcd
  -- , fmpz_mod_poly_gcd_hgcd
  -- , _fmpz_mod_poly_xgcd_euclidean
  , _fmpz_mod_poly_xgcd_euclidean_f
  -- , fmpz_mod_poly_xgcd_euclidean
  , fmpz_mod_poly_xgcd_euclidean_f
  -- , _fmpz_mod_poly_xgcd_hgcd
  -- , fmpz_mod_poly_xgcd_hgcd
  , _fmpz_mod_poly_xgcd
  , fmpz_mod_poly_xgcd
  , fmpz_mod_poly_xgcd_f
  , _fmpz_mod_poly_gcdinv_euclidean
  , fmpz_mod_poly_gcdinv_euclidean
  , _fmpz_mod_poly_gcdinv_euclidean_f
  , fmpz_mod_poly_gcdinv_euclidean_f
  , _fmpz_mod_poly_gcdinv
  , _fmpz_mod_poly_gcdinv_f
  , fmpz_mod_poly_gcdinv
  , fmpz_mod_poly_gcdinv_f
  , _fmpz_mod_poly_invmod
  , _fmpz_mod_poly_invmod_f
  , fmpz_mod_poly_invmod
  , fmpz_mod_poly_invmod_f
  -- * Minpoly
  , _fmpz_mod_poly_minpoly_bm
  , fmpz_mod_poly_minpoly_bm
  , _fmpz_mod_poly_minpoly_hgcd
  , fmpz_mod_poly_minpoly_hgcd
  , _fmpz_mod_poly_minpoly
  , fmpz_mod_poly_minpoly
  -- * Resultant
  , _fmpz_mod_poly_resultant_euclidean
  , fmpz_mod_poly_resultant_euclidean
  , _fmpz_mod_poly_resultant_hgcd
  , fmpz_mod_poly_resultant_hgcd
  , _fmpz_mod_poly_resultant
  , fmpz_mod_poly_resultant
  -- * Discriminant
  , _fmpz_mod_poly_discriminant
  , fmpz_mod_poly_discriminant
  -- * Derivative
  , _fmpz_mod_poly_derivative
  , fmpz_mod_poly_derivative
  -- * Evaluation
  , _fmpz_mod_poly_evaluate_fmpz
  , fmpz_mod_poly_evaluate_fmpz
  -- * Multipoint evaluation
  , _fmpz_mod_poly_evaluate_fmpz_vec_iter
  , fmpz_mod_poly_evaluate_fmpz_vec_iter
  , _fmpz_mod_poly_evaluate_fmpz_vec_fast_precomp
  , _fmpz_mod_poly_evaluate_fmpz_vec_fast
  , fmpz_mod_poly_evaluate_fmpz_vec_fast
  , _fmpz_mod_poly_evaluate_fmpz_vec
  , fmpz_mod_poly_evaluate_fmpz_vec
  -- * Composition
  -- , _fmpz_mod_poly_compose_horner
  -- , fmpz_mod_poly_compose_horner
  --, _fmpz_mod_poly_compose_divconquer
  --, fmpz_mod_poly_compose_divconquer
  , _fmpz_mod_poly_compose
  , fmpz_mod_poly_compose
  -- * Square roots
  , _fmpz_mod_poly_invsqrt_series
  , fmpz_mod_poly_invsqrt_series
  , _fmpz_mod_poly_sqrt_series
  , fmpz_mod_poly_sqrt_series
  , _fmpz_mod_poly_sqrt
  , fmpz_mod_poly_sqrt
  -- * Modular composition
  , _fmpz_mod_poly_compose_mod
  , fmpz_mod_poly_compose_mod
  , _fmpz_mod_poly_compose_mod_horner
  , fmpz_mod_poly_compose_mod_horner
  , _fmpz_mod_poly_compose_mod_brent_kung
  , fmpz_mod_poly_compose_mod_brent_kung
  , _fmpz_mod_poly_reduce_matrix_mod_poly
  , _fmpz_mod_poly_precompute_matrix_worker
  , _fmpz_mod_poly_precompute_matrix
  , fmpz_mod_poly_precompute_matrix
  , _fmpz_mod_poly_compose_mod_brent_kung_precomp_preinv_worker
  , _fmpz_mod_poly_compose_mod_brent_kung_precomp_preinv
  , fmpz_mod_poly_compose_mod_brent_kung_precomp_preinv
  , _fmpz_mod_poly_compose_mod_brent_kung_preinv
  , fmpz_mod_poly_compose_mod_brent_kung_preinv
  , _fmpz_mod_poly_compose_mod_brent_kung_vec_preinv
  , fmpz_mod_poly_compose_mod_brent_kung_vec_preinv
  , _fmpz_mod_poly_compose_mod_brent_kung_vec_preinv_threaded_pool
  , fmpz_mod_poly_compose_mod_brent_kung_vec_preinv_threaded_pool
  , fmpz_mod_poly_compose_mod_brent_kung_vec_preinv_threaded
  -- * Subproduct trees
  , _fmpz_mod_poly_tree_alloc
  , _fmpz_mod_poly_tree_free
  , _fmpz_mod_poly_tree_build
  -- * Radix conversion
  , _fmpz_mod_poly_radix_init
  , fmpz_mod_poly_radix_init
  , _fmpz_mod_poly_radix
  , fmpz_mod_poly_radix
  -- * Input and output
  , _fmpz_mod_poly_fprint
  , fmpz_mod_poly_fprint
  , fmpz_mod_poly_fprint_pretty
  , fmpz_mod_poly_print
  , fmpz_mod_poly_print_pretty
  -- * Inflation and deflation
  , fmpz_mod_poly_inflate
  , fmpz_mod_poly_deflate
  , fmpz_mod_poly_deflation
  -- * Berlekamp-Massey Algorithm
  , fmpz_mod_berlekamp_massey_init
  , fmpz_mod_berlekamp_massey_clear
  , fmpz_mod_berlekamp_massey_start_over
  , fmpz_mod_berlekamp_massey_add_points
  , fmpz_mod_berlekamp_massey_reduce
  , fmpz_mod_berlekamp_massey_point_count
  , fmpz_mod_berlekamp_massey_points
  , fmpz_mod_berlekamp_massey_V_poly
  , fmpz_mod_berlekamp_massey_R_poly
  -- * Characteristic polynomial
  , fmpz_mod_mat_charpoly
  -- * Minimal polynomial
  , fmpz_mod_mat_minpoly
) where 

-- polynomials over integers mod n ---------------------------------------------

import Control.Monad

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr )
import Foreign.Storable
import Foreign.Marshal ( free )

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Poly
import Data.Number.Flint.Fmpz.Mat
import Data.Number.Flint.Fmpz.Mod
import Data.Number.Flint.Fmpz.Mod.Mat
import Data.Number.Flint.NMod.Types
import Data.Number.Flint.ThreadPool

#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpz_mod_poly.h>

-- fmpz_mod_poly_t -------------------------------------------------------------

data FmpzModPoly = FmpzModPoly {-# UNPACK #-} !(ForeignPtr CFmpzModPoly)
data CFmpzModPoly = CFmpzModPoly (Ptr CFmpz) CLong CLong

newFmpzModPoly n = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x ->
    withFmpzModCtx n $ \n -> do
      fmpz_mod_poly_init x n
      addForeignPtrFinalizerEnv p_fmpz_mod_poly_clear n =<< newForeignPtr_ x
  return $ FmpzModPoly x

{-# INLINE withFmpzModPoly #-}
withFmpzModPoly (FmpzModPoly x) f = do
  withForeignPtr x $ \px -> f px >>= return . (FmpzModPoly x,)

{-# INLINE withNewFmpzModPoly #-}
withNewFmpzModPoly n f = do
  x <- newFmpzModPoly n
  withFmpzModPoly x $ \x -> f x

instance Storable CFmpzModPoly where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fmpz_mod_poly_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fmpz_mod_poly_t}
  peek ptr = return CFmpzModPoly 
    `ap` #{peek fmpz_mod_poly_struct, coeffs} ptr
    `ap` #{peek fmpz_mod_poly_struct, alloc } ptr
    `ap` #{peek fmpz_mod_poly_struct, length} ptr
  poke = error "poke undefined for CFmpzModPoly"
  
-- various other structures ----------------------------------------------------

data FmpzModBerlekampMassey = FmpzModBerlekampMassey {-# UNPACK #-} !(ForeignPtr CFmpzModBerlekampMassey)
type CFmpzModBerlekampMassey = CFlint FmpzModBerlekampMassey

data FmpzModPolyRadix = FmpzModPolyRadix {-# UNPACK #-} !(ForeignPtr CFmpzModPolyRadix)
type CFmpzModPolyRadix = CFlint FmpzModPolyRadix

data FmpzModPolyFrobeniusPowers = FmpzModPolyFrobeniusPowers {-# UNPACK #-} !(ForeignPtr CFmpzModPolyFrobeniusPowers)
type CFmpzModPolyFrobeniusPowers = CFlint FmpzModPolyFrobeniusPowers

data FmpzModPolyFrobeniusPowers2Exp = FmpzModPolyFrobeniusPowers2Exp {-# UNPACK #-} !(ForeignPtr CFmpzModPolyFrobeniusPowers2Exp)
type CFmpzModPolyFrobeniusPowers2Exp = CFlint FmpzModPolyFrobeniusPowers2Exp

-- Memory management -----------------------------------------------------------

-- | /fmpz_mod_poly_init/ /poly/ /ctx/ 
-- 
-- Initialises @poly@ for use with context @ctx@ and set it to zero. A
-- corresponding call to @fmpz_mod_poly_clear@ must be made to free the
-- memory used by the polynomial.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_init"
  fmpz_mod_poly_init :: Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_init2/ /poly/ /alloc/ /ctx/ 
-- 
-- Initialises @poly@ with space for at least @alloc@ coefficients and sets
-- the length to zero. The allocated coefficients are all set to zero.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_init2"
  fmpz_mod_poly_init2 :: Ptr CFmpzModPoly -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_clear/ /poly/ /ctx/ 
-- 
-- Clears the given polynomial, releasing any memory used. It must be
-- reinitialised in order to be used again.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_clear"
  fmpz_mod_poly_clear :: Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

foreign import ccall "fmpz_mod_poly.h &fmpz_mod_poly_clear"
  p_fmpz_mod_poly_clear :: FunPtr (Ptr CFmpzModCtx -> Ptr CFmpzModPoly -> IO ())

-- | /fmpz_mod_poly_realloc/ /poly/ /alloc/ /ctx/ 
-- 
-- Reallocates the given polynomial to have space for @alloc@ coefficients.
-- If @alloc@ is zero the polynomial is cleared and then reinitialised. If
-- the current length is greater than @alloc@ the polynomial is first
-- truncated to length @alloc@.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_realloc"
  fmpz_mod_poly_realloc :: Ptr CFmpzModPoly -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_fit_length/ /poly/ /len/ /ctx/ 
-- 
-- If @len@ is greater than the number of coefficients currently allocated,
-- then the polynomial is reallocated to have space for at least @len@
-- coefficients. No data is lost when calling this function.
-- 
-- The function efficiently deals with the case where it is called many
-- times in small increments by at least doubling the number of allocated
-- coefficients when length is larger than the number of coefficients
-- currently allocated.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_fit_length"
  fmpz_mod_poly_fit_length :: Ptr CFmpzModPoly -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_normalise/ /poly/ 
-- 
-- Sets the length of @poly@ so that the top coefficient is non-zero. If
-- all coefficients are zero, the length is set to zero. This function is
-- mainly used internally, as all functions guarantee normalisation.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_normalise"
  _fmpz_mod_poly_normalise :: Ptr CFmpzModPoly -> IO ()

-- | /_fmpz_mod_poly_set_length/ /poly/ /len/ 
-- 
-- Demotes the coefficients of @poly@ beyond @len@ and sets the length of
-- @poly@ to @len@.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_set_length"
  _fmpz_mod_poly_set_length :: Ptr CFmpzModPoly -> CLong -> IO ()

-- | /fmpz_mod_poly_truncate/ /poly/ /len/ /ctx/ 
-- 
-- If the current length of @poly@ is greater than @len@, it is truncated
-- to have the given length. Discarded coefficients are not necessarily set
-- to zero.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_truncate"
  fmpz_mod_poly_truncate :: Ptr CFmpzModPoly -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_set_trunc/ /res/ /poly/ /n/ /ctx/ 
-- 
-- Notionally truncate @poly@ to length \(n\) and set @res@ to the result.
-- The result is normalised.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_set_trunc"
  fmpz_mod_poly_set_trunc :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> CLong -> Ptr CFmpzModCtx -> IO ()

-- Randomisation ---------------------------------------------------------------

-- | /fmpz_mod_poly_randtest/ /f/ /state/ /len/ /ctx/ 
-- 
-- Sets the polynomial~\`f\` to a random polynomial of length up~@len@.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_randtest"
  fmpz_mod_poly_randtest :: Ptr CFmpzModPoly -> Ptr CFRandState -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_randtest_irreducible/ /f/ /state/ /len/ /ctx/ 
-- 
-- Sets the polynomial~\`f\` to a random irreducible polynomial of length
-- up~@len@, assuming @len@ is positive.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_randtest_irreducible"
  fmpz_mod_poly_randtest_irreducible :: Ptr CFmpzModPoly -> Ptr CFRandState -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_randtest_not_zero/ /f/ /state/ /len/ /ctx/ 
-- 
-- Sets the polynomial~\`f\` to a random polynomial of length up~@len@,
-- assuming @len@ is positive.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_randtest_not_zero"
  fmpz_mod_poly_randtest_not_zero :: Ptr CFmpzModPoly -> Ptr CFRandState -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_randtest_monic/ /poly/ /state/ /len/ /ctx/ 
-- 
-- Generates a random monic polynomial with length @len@.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_randtest_monic"
  fmpz_mod_poly_randtest_monic :: Ptr CFmpzModPoly -> Ptr CFRandState -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_randtest_monic_irreducible/ /poly/ /state/ /len/ /ctx/ 
-- 
-- Generates a random monic irreducible polynomial with length @len@.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_randtest_monic_irreducible"
  fmpz_mod_poly_randtest_monic_irreducible :: Ptr CFmpzModPoly -> Ptr CFRandState -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_randtest_monic_primitive/ /poly/ /state/ /len/ /ctx/ 
-- 
-- Generates a random monic irreducible primitive polynomial with length
-- @len@.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_randtest_monic_primitive"
  fmpz_mod_poly_randtest_monic_primitive :: Ptr CFmpzModPoly -> Ptr CFRandState -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_randtest_trinomial/ /poly/ /state/ /len/ /ctx/ 
-- 
-- Generates a random monic trinomial of length @len@.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_randtest_trinomial"
  fmpz_mod_poly_randtest_trinomial :: Ptr CFmpzModPoly -> Ptr CFRandState -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_randtest_trinomial_irreducible/ /poly/ /state/ /len/ /max_attempts/ /ctx/ 
-- 
-- Attempts to set @poly@ to a monic irreducible trinomial of length @len@.
-- It will generate up to @max_attempts@ trinomials in attempt to find an
-- irreducible one. If @max_attempts@ is @0@, then it will keep generating
-- trinomials until an irreducible one is found. Returns \(1\) if one is
-- found and \(0\) otherwise.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_randtest_trinomial_irreducible"
  fmpz_mod_poly_randtest_trinomial_irreducible :: Ptr CFmpzModPoly -> Ptr CFRandState -> CLong -> CLong -> Ptr CFmpzModCtx -> IO CInt

-- | /fmpz_mod_poly_randtest_pentomial/ /poly/ /state/ /len/ /ctx/ 
-- 
-- Generates a random monic pentomial of length @len@.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_randtest_pentomial"
  fmpz_mod_poly_randtest_pentomial :: Ptr CFmpzModPoly -> Ptr CFRandState -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_randtest_pentomial_irreducible/ /poly/ /state/ /len/ /max_attempts/ /ctx/ 
-- 
-- Attempts to set @poly@ to a monic irreducible pentomial of length @len@.
-- It will generate up to @max_attempts@ pentomials in attempt to find an
-- irreducible one. If @max_attempts@ is @0@, then it will keep generating
-- pentomials until an irreducible one is found. Returns \(1\) if one is
-- found and \(0\) otherwise.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_randtest_pentomial_irreducible"
  fmpz_mod_poly_randtest_pentomial_irreducible :: Ptr CFmpzModPoly -> Ptr CFRandState -> CLong -> CLong -> Ptr CFmpzModCtx -> IO CInt

-- | /fmpz_mod_poly_randtest_sparse_irreducible/ /poly/ /state/ /len/ /ctx/ 
-- 
-- Attempts to set @poly@ to a sparse, monic irreducible polynomial with
-- length @len@. It attempts to find an irreducible trinomial. If that does
-- not succeed, it attempts to find a irreducible pentomial. If that fails,
-- then @poly@ is just set to a random monic irreducible polynomial.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_randtest_sparse_irreducible"
  fmpz_mod_poly_randtest_sparse_irreducible :: Ptr CFmpzModPoly -> Ptr CFRandState -> CLong -> Ptr CFmpzModCtx -> IO ()

-- Attributes ------------------------------------------------------------------

-- | /fmpz_mod_poly_degree/ /poly/ /ctx/ 
-- 
-- Returns the degree of the polynomial. The degree of the zero polynomial
-- is defined to be \(-1\).
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_degree"
  fmpz_mod_poly_degree :: Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO CLong

-- | /fmpz_mod_poly_length/ /poly/ /ctx/ 
-- 
-- Returns the length of the polynomial, which is one more than its degree.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_length"
  fmpz_mod_poly_length :: Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO CLong

-- | /fmpz_mod_poly_lead/ /poly/ /ctx/ 
-- 
-- Returns a pointer to the first leading coefficient of @poly@ if this is
-- non-zero, otherwise returns @NULL@.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_lead"
  fmpz_mod_poly_lead :: Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO (Ptr CFmpz)

-- Assignment and basic manipulation -------------------------------------------

-- | /fmpz_mod_poly_set/ /poly1/ /poly2/ /ctx/ 
-- 
-- Sets the polynomial @poly1@ to the value of @poly2@.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_set"
  fmpz_mod_poly_set :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_swap/ /poly1/ /poly2/ /ctx/ 
-- 
-- Swaps the two polynomials. This is done efficiently by swapping pointers
-- rather than individual coefficients.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_swap"
  fmpz_mod_poly_swap :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_zero/ /poly/ /ctx/ 
-- 
-- Sets @poly@ to the zero polynomial.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_zero"
  fmpz_mod_poly_zero :: Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_one/ /poly/ /ctx/ 
-- 
-- Sets @poly@ to the constant polynomial \(1\).
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_one"
  fmpz_mod_poly_one :: Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_zero_coeffs/ /poly/ /i/ /j/ /ctx/ 
-- 
-- Sets the coefficients of \(X^k\) for \(k \in [i, j)\) in the polynomial
-- to zero.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_zero_coeffs"
  fmpz_mod_poly_zero_coeffs :: Ptr CFmpzModPoly -> CLong -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_reverse/ /res/ /poly/ /n/ /ctx/ 
-- 
-- This function considers the polynomial @poly@ to be of length \(n\),
-- notionally truncating and zero padding if required, and reverses the
-- result. Since the function normalises its result @res@ may be of length
-- less than \(n\).
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_reverse"
  fmpz_mod_poly_reverse :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> CLong -> Ptr CFmpzModCtx -> IO ()

-- Conversion ------------------------------------------------------------------

-- | /fmpz_mod_poly_set_ui/ /f/ /c/ /ctx/ 
-- 
-- Sets the polynomial \(f\) to the constant \(c\) reduced modulo \(p\).
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_set_ui"
  fmpz_mod_poly_set_ui :: Ptr CFmpzModPoly -> CULong -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_set_fmpz/ /f/ /c/ /ctx/ 
-- 
-- Sets the polynomial \(f\) to the constant \(c\) reduced modulo \(p\).
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_set_fmpz"
  fmpz_mod_poly_set_fmpz :: Ptr CFmpzModPoly -> Ptr CFmpz -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_set_fmpz_poly/ /f/ /g/ /ctx/ 
-- 
-- Sets \(f\) to \(g\) reduced modulo \(p\), where \(p\) is the modulus
-- that is part of the data structure of \(f\).
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_set_fmpz_poly"
  fmpz_mod_poly_set_fmpz_poly :: Ptr CFmpzModPoly -> Ptr CFmpzPoly -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_get_fmpz_poly/ /f/ /g/ /ctx/ 
-- 
-- Sets \(f\) to \(g\). This is done simply by lifting the coefficients of
-- \(g\) taking representatives \([0, p) \subset \mathbf{Z}\).
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_get_fmpz_poly"
  fmpz_mod_poly_get_fmpz_poly :: Ptr CFmpzPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_get_nmod_poly/ /f/ /g/ 
-- 
-- Sets \(f\) to \(g\) assuming the modulus of both polynomials is the same
-- (no checking is performed).
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_get_nmod_poly"
  fmpz_mod_poly_get_nmod_poly :: Ptr CNModPoly -> Ptr CFmpzModPoly -> IO ()

-- | /fmpz_mod_poly_set_nmod_poly/ /f/ /g/ 
-- 
-- Sets \(f\) to \(g\) assuming the modulus of both polynomials is the same
-- (no checking is performed).
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_set_nmod_poly"
  fmpz_mod_poly_set_nmod_poly :: Ptr CFmpzModPoly -> Ptr CNModPoly -> IO ()

-- Comparison ------------------------------------------------------------------

-- | /fmpz_mod_poly_equal/ /poly1/ /poly2/ /ctx/ 
-- 
-- Returns non-zero if the two polynomials are equal, otherwise returns
-- zero.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_equal"
  fmpz_mod_poly_equal :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO CInt

-- | /fmpz_mod_poly_equal_trunc/ /poly1/ /poly2/ /n/ /ctx/ 
-- 
-- Notionally truncates the two polynomials to length \(n\) and returns
-- non-zero if the two polynomials are equal, otherwise returns zero.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_equal_trunc"
  fmpz_mod_poly_equal_trunc :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> CLong -> Ptr CFmpzModCtx -> IO CInt

-- | /fmpz_mod_poly_is_zero/ /poly/ /ctx/ 
-- 
-- Returns non-zero if the polynomial is zero.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_is_zero"
  fmpz_mod_poly_is_zero :: Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO CInt

-- | /fmpz_mod_poly_is_one/ /poly/ /ctx/ 
-- 
-- Returns non-zero if the polynomial is the constant \(1\).
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_is_one"
  fmpz_mod_poly_is_one :: Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO CInt

-- | /fmpz_mod_poly_is_gen/ /poly/ /ctx/ 
-- 
-- Returns non-zero if the polynomial is the degree \(1\) polynomial \(x\).
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_is_gen"
  fmpz_mod_poly_is_gen :: Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO CInt

-- Getting and setting coefficients --------------------------------------------

-- | /fmpz_mod_poly_set_coeff_fmpz/ /poly/ /n/ /x/ /ctx/ 
-- 
-- Sets the coefficient of \(X^n\) in the polynomial to \(x\), assuming
-- \(n \geq 0\).
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_set_coeff_fmpz"
  fmpz_mod_poly_set_coeff_fmpz :: Ptr CFmpzModPoly -> CLong -> Ptr CFmpz -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_set_coeff_ui/ /poly/ /n/ /x/ /ctx/ 
-- 
-- Sets the coefficient of \(X^n\) in the polynomial to \(x\), assuming
-- \(n \geq 0\).
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_set_coeff_ui"
  fmpz_mod_poly_set_coeff_ui :: Ptr CFmpzModPoly -> CLong -> CULong -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_get_coeff_fmpz/ /x/ /poly/ /n/ /ctx/ 
-- 
-- Sets \(x\) to the coefficient of \(X^n\) in the polynomial, assuming
-- \(n \geq 0\).
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_get_coeff_fmpz"
  fmpz_mod_poly_get_coeff_fmpz :: Ptr CFmpz -> Ptr CFmpzModPoly -> CLong -> Ptr CFmpzModCtx -> IO ()

-- -- | /fmpz_mod_poly_set_coeff_mpz/ /poly/ /n/ /x/ /ctx/ 
-- -- 
-- -- Sets the coefficient of \(X^n\) in the polynomial to \(x\), assuming
-- -- \(n \geq 0\).
-- foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_set_coeff_mpz"
--   fmpz_mod_poly_set_coeff_mpz :: Ptr CFmpzModPoly -> CLong -> Ptr CMpz -> Ptr CFmpzModCtx -> IO ()

-- -- | /fmpz_mod_poly_get_coeff_mpz/ /x/ /poly/ /n/ /ctx/ 
-- -- 
-- -- Sets \(x\) to the coefficient of \(X^n\) in the polynomial, assuming
-- -- \(n \geq 0\).
-- foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_get_coeff_mpz"
--   fmpz_mod_poly_get_coeff_mpz :: Ptr CMpz -> Ptr CFmpzModPoly -> CLong -> Ptr CFmpzModCtx -> IO ()

-- Shifting --------------------------------------------------------------------

-- | /_fmpz_mod_poly_shift_left/ /res/ /poly/ /len/ /n/ /ctx/ 
-- 
-- Sets @(res, len + n)@ to @(poly, len)@ shifted left by \(n\)
-- coefficients.
-- 
-- Inserts zero coefficients at the lower end. Assumes that @len@ and \(n\)
-- are positive, and that @res@ fits @len + n@ elements. Supports aliasing
-- between @res@ and @poly@.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_shift_left"
  _fmpz_mod_poly_shift_left :: Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_shift_left/ /f/ /g/ /n/ /ctx/ 
-- 
-- Sets @res@ to @poly@ shifted left by \(n\) coeffs. Zero coefficients are
-- inserted.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_shift_left"
  fmpz_mod_poly_shift_left :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_shift_right/ /res/ /poly/ /len/ /n/ /ctx/ 
-- 
-- Sets @(res, len - n)@ to @(poly, len)@ shifted right by \(n\)
-- coefficients.
-- 
-- Assumes that @len@ and \(n\) are positive, that @len > n@, and that
-- @res@ fits @len - n@ elements. Supports aliasing between @res@ and
-- @poly@, although in this case the top coefficients of @poly@ are not set
-- to zero.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_shift_right"
  _fmpz_mod_poly_shift_right :: Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_shift_right/ /f/ /g/ /n/ /ctx/ 
-- 
-- Sets @res@ to @poly@ shifted right by \(n\) coefficients. If \(n\) is
-- equal to or greater than the current length of @poly@, @res@ is set to
-- the zero polynomial.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_shift_right"
  fmpz_mod_poly_shift_right :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> CLong -> Ptr CFmpzModCtx -> IO ()

-- Addition and subtraction ----------------------------------------------------

-- | /_fmpz_mod_poly_add/ /res/ /poly1/ /len1/ /poly2/ /len2/ /p/ 
-- 
-- Sets @res@ to the sum of @(poly1, len1)@ and @(poly2, len2)@. It is
-- assumed that @res@ has sufficient space for the longer of the two
-- polynomials.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_add"
  _fmpz_mod_poly_add :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_add/ /res/ /poly1/ /poly2/ /ctx/ 
-- 
-- Sets @res@ to the sum of @poly1@ and @poly2@.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_add"
  fmpz_mod_poly_add :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_add_series/ /res/ /poly1/ /poly2/ /n/ /ctx/ 
-- 
-- Notionally truncate @poly1@ and @poly2@ to length \(n\) and set @res@ to
-- the sum.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_add_series"
  fmpz_mod_poly_add_series :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_sub/ /res/ /poly1/ /len1/ /poly2/ /len2/ /p/ 
-- 
-- Sets @res@ to @(poly1, len1)@ minus @(poly2, len2)@. It is assumed that
-- @res@ has sufficient space for the longer of the two polynomials.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_sub"
  _fmpz_mod_poly_sub :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_sub/ /res/ /poly1/ /poly2/ /ctx/ 
-- 
-- Sets @res@ to @poly1@ minus @poly2@.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_sub"
  fmpz_mod_poly_sub :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_sub_series/ /res/ /poly1/ /poly2/ /n/ /ctx/ 
-- 
-- Notionally truncate @poly1@ and @poly2@ to length \(n\) and set @res@ to
-- the difference.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_sub_series"
  fmpz_mod_poly_sub_series :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_neg/ /res/ /poly/ /len/ /p/ 
-- 
-- Sets @(res, len)@ to the negative of @(poly, len)@ modulo \(p\).
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_neg"
  _fmpz_mod_poly_neg :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_neg/ /res/ /poly/ /ctx/ 
-- 
-- Sets @res@ to the negative of @poly@ modulo \(p\).
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_neg"
  fmpz_mod_poly_neg :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- Scalar multiplication and division ------------------------------------------

-- | /_fmpz_mod_poly_scalar_mul_fmpz/ /res/ /poly/ /len/ /x/ /p/ 
-- 
-- Sets @(res, len@) to @(poly, len)@ multiplied by \(x\), reduced modulo
-- \(p\).
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_scalar_mul_fmpz"
  _fmpz_mod_poly_scalar_mul_fmpz :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_scalar_mul_fmpz/ /res/ /poly/ /x/ /ctx/ 
-- 
-- Sets @res@ to @poly@ multiplied by \(x\).
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_scalar_mul_fmpz"
  fmpz_mod_poly_scalar_mul_fmpz :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpz -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_scalar_addmul_fmpz/ /rop/ /op/ /x/ /ctx/ 
-- 
-- Adds to @rop@ the product of @op@ by the scalar @x@.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_scalar_addmul_fmpz"
  fmpz_mod_poly_scalar_addmul_fmpz :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpz -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_scalar_div_fmpz/ /res/ /poly/ /len/ /x/ /p/ 
-- 
-- Sets @(res, len@) to @(poly, len)@ divided by \(x\) (i.e. multiplied by
-- the inverse of \(x \pmod{p}\)). The result is reduced modulo \(p\).
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_scalar_div_fmpz"
  _fmpz_mod_poly_scalar_div_fmpz :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_scalar_div_fmpz/ /res/ /poly/ /x/ /ctx/ 
-- 
-- Sets @res@ to @poly@ divided by \(x\), (i.e. multiplied by the inverse
-- of \(x \pmod{p}\)). The result is reduced modulo \(p\).
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_scalar_div_fmpz"
  fmpz_mod_poly_scalar_div_fmpz :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpz -> Ptr CFmpzModCtx -> IO ()

-- Multiplication --------------------------------------------------------------

-- | /_fmpz_mod_poly_mul/ /res/ /poly1/ /len1/ /poly2/ /len2/ /p/ 
-- 
-- Sets @(res, len1 + len2 - 1)@ to the product of @(poly1, len1)@ and
-- @(poly2, len2)@. Assumes @len1 >= len2 > 0@. Allows zero-padding of the
-- two input polynomials.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_mul"
  _fmpz_mod_poly_mul :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_mul/ /res/ /poly1/ /poly2/ /ctx/ 
-- 
-- Sets @res@ to the product of @poly1@ and @poly2@.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_mul"
  fmpz_mod_poly_mul :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_mullow/ /res/ /poly1/ /len1/ /poly2/ /len2/ /p/ /n/ 
-- 
-- Sets @(res, n)@ to the lowest \(n\) coefficients of the product of
-- @(poly1, len1)@ and @(poly2, len2)@.
-- 
-- Assumes @len1 >= len2 > 0@ and @0 \< n \<= len1 + len2 - 1@. Allows for
-- zero-padding in the inputs. Does not support aliasing between the inputs
-- and the output.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_mullow"
  _fmpz_mod_poly_mullow :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> IO ()

-- | /fmpz_mod_poly_mullow/ /res/ /poly1/ /poly2/ /n/ /ctx/ 
-- 
-- Sets @res@ to the lowest \(n\) coefficients of the product of @poly1@
-- and @poly2@.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_mullow"
  fmpz_mod_poly_mullow :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_sqr/ /res/ /poly/ /len/ /p/ 
-- 
-- Sets @res@ to the square of @poly@.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_sqr"
  _fmpz_mod_poly_sqr :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_sqr/ /res/ /poly/ /ctx/ 
-- 
-- Computes @res@ as the square of @poly@.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_sqr"
  fmpz_mod_poly_sqr :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_mulhigh/ /res/ /poly1/ /poly2/ /start/ /ctx/ 
-- 
-- Computes the product of @poly1@ and @poly2@ and writes the coefficients
-- from @start@ onwards into the high coefficients of @res@, the remaining
-- coefficients being arbitrary.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_mulhigh"
  fmpz_mod_poly_mulhigh :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_mulmod/ /res/ /poly1/ /len1/ /poly2/ /len2/ /f/ /lenf/ /p/ 
-- 
-- Sets @res, len1 + len2 - 1@ to the remainder of the product of @poly1@
-- and @poly2@ upon polynomial division by @f@.
-- 
-- It is required that @len1 + len2 - lenf > 0@, which is equivalent to
-- requiring that the result will actually be reduced. Otherwise, simply
-- use @_fmpz_mod_poly_mul@ instead.
-- 
-- Aliasing of @f@ and @res@ is not permitted.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_mulmod"
  _fmpz_mod_poly_mulmod :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_mulmod/ /res/ /poly1/ /poly2/ /f/ /ctx/ 
-- 
-- Sets @res@ to the remainder of the product of @poly1@ and @poly2@ upon
-- polynomial division by @f@.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_mulmod"
  fmpz_mod_poly_mulmod :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_mulmod_preinv/ /res/ /poly1/ /len1/ /poly2/ /len2/ /f/ /lenf/ /finv/ /lenfinv/ /p/ 
-- 
-- Sets @res, len1 + len2 - 1@ to the remainder of the product of @poly1@
-- and @poly2@ upon polynomial division by @f@.
-- 
-- It is required that @finv@ is the inverse of the reverse of @f@ mod
-- @x^lenf@. It is required that @len1 + len2 - lenf > 0@, which is
-- equivalent to requiring that the result will actually be reduced. It is
-- required that @len1 \< lenf@ and @len2 \< lenf@. Otherwise, simply use
-- @_fmpz_mod_poly_mul@ instead.
-- 
-- Aliasing of @f@ or @finv@ and @res@ is not permitted.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_mulmod_preinv"
  _fmpz_mod_poly_mulmod_preinv :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_mulmod_preinv/ /res/ /poly1/ /poly2/ /f/ /finv/ /ctx/ 
-- 
-- Sets @res@ to the remainder of the product of @poly1@ and @poly2@ upon
-- polynomial division by @f@. @finv@ is the inverse of the reverse of @f@.
-- It is required that @poly1@ and @poly2@ are reduced modulo @f@.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_mulmod_preinv"
  fmpz_mod_poly_mulmod_preinv :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- Products --------------------------------------------------------------------

-- | /_fmpz_mod_poly_product_roots_fmpz_vec/ /poly/ /xs/ /n/ /f/ 
-- 
-- Sets @(poly, n + 1)@ to the monic polynomial which is the product of
-- \((x - x_0)(x - x_1) \cdots (x - x_{n-1})\), the roots \(x_i\) being
-- given by @xs@. It is required that the roots are canonical.
-- 
-- Aliasing of the input and output is not allowed.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_product_roots_fmpz_vec"
  _fmpz_mod_poly_product_roots_fmpz_vec :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_product_roots_fmpz_vec/ /poly/ /xs/ /n/ /f/ /ctx/ 
-- 
-- Sets @poly@ to the monic polynomial which is the product of
-- \((x - x_0)(x - x_1) \cdots (x - x_{n-1})\), the roots \(x_i\) being
-- given by @xs@. It is required that the roots are canonical.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_product_roots_fmpz_vec"
  fmpz_mod_poly_product_roots_fmpz_vec :: Ptr CFmpzModPoly -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_find_distinct_nonzero_roots/ /roots/ /A/ /ctx/ 
-- 
-- If @A@ has \(\deg(A)\) distinct nonzero roots in \(\mathbb{F}_p\), write
-- these roots out to @roots[0]@ to @roots[deg(A) - 1]@ and return @1@.
-- Otherwise, return @0@. It is assumed that @A@ is nonzero and that the
-- modulus of @A@ is prime. This function uses Rabin\'s probabilistic
-- method via gcd\'s with \((x + \delta)^{\frac{p-1}{2}} - 1\).
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_find_distinct_nonzero_roots"
  fmpz_mod_poly_find_distinct_nonzero_roots :: Ptr CFmpz -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO CInt

-- Powering
--



-- | /_fmpz_mod_poly_pow/ /rop/ /op/ /len/ /e/ /p/ 
-- 
-- Sets @rop = poly^e@, assuming that \(e > 1\) and @elen > 0@, and that
-- @res@ has space for @e*(len - 1) + 1@ coefficients. Does not support
-- aliasing.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_pow"
  _fmpz_mod_poly_pow :: Ptr CFmpz -> Ptr CFmpz -> CLong -> CULong -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_pow/ /rop/ /op/ /e/ /ctx/ 
-- 
-- Computes @rop = poly^e@. If \(e\) is zero, returns one, so that in
-- particular @0^0 = 1@.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_pow"
  fmpz_mod_poly_pow :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> CULong -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_pow_trunc/ /res/ /poly/ /e/ /trunc/ /p/ 
-- 
-- Sets @res@ to the low @trunc@ coefficients of @poly@ (assumed to be zero
-- padded if necessary to length @trunc@) to the power @e@. This is
-- equivalent to doing a powering followed by a truncation. We require that
-- @res@ has enough space for @trunc@ coefficients, that @trunc > 0@ and
-- that @e > 1@. Aliasing is not permitted.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_pow_trunc"
  _fmpz_mod_poly_pow_trunc :: Ptr CFmpz -> Ptr CFmpz -> CULong -> CLong -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_pow_trunc/ /res/ /poly/ /e/ /trunc/ /ctx/ 
-- 
-- Sets @res@ to the low @trunc@ coefficients of @poly@ to the power @e@.
-- This is equivalent to doing a powering followed by a truncation.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_pow_trunc"
  fmpz_mod_poly_pow_trunc :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> CULong -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_pow_trunc_binexp/ /res/ /poly/ /e/ /trunc/ /p/ 
-- 
-- Sets @res@ to the low @trunc@ coefficients of @poly@ (assumed to be zero
-- padded if necessary to length @trunc@) to the power @e@. This is
-- equivalent to doing a powering followed by a truncation. We require that
-- @res@ has enough space for @trunc@ coefficients, that @trunc > 0@ and
-- that @e > 1@. Aliasing is not permitted. Uses the binary exponentiation
-- method.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_pow_trunc_binexp"
  _fmpz_mod_poly_pow_trunc_binexp :: Ptr CFmpz -> Ptr CFmpz -> CULong -> CLong -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_pow_trunc_binexp/ /res/ /poly/ /e/ /trunc/ /ctx/ 
-- 
-- Sets @res@ to the low @trunc@ coefficients of @poly@ to the power @e@.
-- This is equivalent to doing a powering followed by a truncation. Uses
-- the binary exponentiation method.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_pow_trunc_binexp"
  fmpz_mod_poly_pow_trunc_binexp :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> CULong -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_powmod_ui_binexp/ /res/ /poly/ /e/ /f/ /lenf/ /p/ 
-- 
-- Sets @res@ to @poly@ raised to the power @e@ modulo @f@, using binary
-- exponentiation. We require @e > 0@.
-- 
-- We require @lenf > 1@. It is assumed that @poly@ is already reduced
-- modulo @f@ and zero-padded as necessary to have length exactly
-- @lenf - 1@. The output @res@ must have room for @lenf - 1@ coefficients.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_powmod_ui_binexp"
  _fmpz_mod_poly_powmod_ui_binexp :: Ptr CFmpz -> Ptr CFmpz -> CULong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_powmod_ui_binexp/ /res/ /poly/ /e/ /f/ /ctx/ 
-- 
-- Sets @res@ to @poly@ raised to the power @e@ modulo @f@, using binary
-- exponentiation. We require @e >= 0@.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_powmod_ui_binexp"
  fmpz_mod_poly_powmod_ui_binexp :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> CULong -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_powmod_ui_binexp_preinv/ /res/ /poly/ /e/ /f/ /lenf/ /finv/ /lenfinv/ /p/ 
-- 
-- Sets @res@ to @poly@ raised to the power @e@ modulo @f@, using binary
-- exponentiation. We require @e > 0@. We require @finv@ to be the inverse
-- of the reverse of @f@.
-- 
-- We require @lenf > 1@. It is assumed that @poly@ is already reduced
-- modulo @f@ and zero-padded as necessary to have length exactly
-- @lenf - 1@. The output @res@ must have room for @lenf - 1@ coefficients.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_powmod_ui_binexp_preinv"
  _fmpz_mod_poly_powmod_ui_binexp_preinv :: Ptr CFmpz -> Ptr CFmpz -> CULong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_powmod_ui_binexp_preinv/ /res/ /poly/ /e/ /f/ /finv/ /ctx/ 
-- 
-- Sets @res@ to @poly@ raised to the power @e@ modulo @f@, using binary
-- exponentiation. We require @e >= 0@. We require @finv@ to be the inverse
-- of the reverse of @f@.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_powmod_ui_binexp_preinv"
  fmpz_mod_poly_powmod_ui_binexp_preinv :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> CULong -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_powmod_fmpz_binexp/ /res/ /poly/ /e/ /f/ /lenf/ /p/ 
-- 
-- Sets @res@ to @poly@ raised to the power @e@ modulo @f@, using binary
-- exponentiation. We require @e > 0@.
-- 
-- We require @lenf > 1@. It is assumed that @poly@ is already reduced
-- modulo @f@ and zero-padded as necessary to have length exactly
-- @lenf - 1@. The output @res@ must have room for @lenf - 1@ coefficients.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_powmod_fmpz_binexp"
  _fmpz_mod_poly_powmod_fmpz_binexp :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_powmod_fmpz_binexp/ /res/ /poly/ /e/ /f/ /ctx/ 
-- 
-- Sets @res@ to @poly@ raised to the power @e@ modulo @f@, using binary
-- exponentiation. We require @e >= 0@.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_powmod_fmpz_binexp"
  fmpz_mod_poly_powmod_fmpz_binexp :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpz -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_powmod_fmpz_binexp_preinv/ /res/ /poly/ /e/ /f/ /lenf/ /finv/ /lenfinv/ /p/ 
-- 
-- Sets @res@ to @poly@ raised to the power @e@ modulo @f@, using binary
-- exponentiation. We require @e > 0@. We require @finv@ to be the inverse
-- of the reverse of @f@.
-- 
-- We require @lenf > 1@. It is assumed that @poly@ is already reduced
-- modulo @f@ and zero-padded as necessary to have length exactly
-- @lenf - 1@. The output @res@ must have room for @lenf - 1@ coefficients.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_powmod_fmpz_binexp_preinv"
  _fmpz_mod_poly_powmod_fmpz_binexp_preinv :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_powmod_fmpz_binexp_preinv/ /res/ /poly/ /e/ /f/ /finv/ /ctx/ 
-- 
-- Sets @res@ to @poly@ raised to the power @e@ modulo @f@, using binary
-- exponentiation. We require @e >= 0@. We require @finv@ to be the inverse
-- of the reverse of @f@.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_powmod_fmpz_binexp_preinv"
  fmpz_mod_poly_powmod_fmpz_binexp_preinv :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpz -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_powmod_x_fmpz_preinv/ /res/ /e/ /f/ /lenf/ /finv/ /lenfinv/ /p/ 
-- 
-- Sets @res@ to @x@ raised to the power @e@ modulo @f@, using sliding
-- window exponentiation. We require @e > 0@. We require @finv@ to be the
-- inverse of the reverse of @f@.
-- 
-- We require @lenf > 2@. The output @res@ must have room for @lenf - 1@
-- coefficients.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_powmod_x_fmpz_preinv"
  _fmpz_mod_poly_powmod_x_fmpz_preinv :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_powmod_x_fmpz_preinv/ /res/ /e/ /f/ /finv/ /ctx/ 
-- 
-- Sets @res@ to @x@ raised to the power @e@ modulo @f@, using sliding
-- window exponentiation. We require @e >= 0@. We require @finv@ to be the
-- inverse of the reverse of \`\`
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_powmod_x_fmpz_preinv"
  fmpz_mod_poly_powmod_x_fmpz_preinv :: Ptr CFmpzModPoly -> Ptr CFmpz -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_powers_mod_preinv_naive/ /res/ /f/ /flen/ /n/ /g/ /glen/ /ginv/ /ginvlen/ /p/ 
-- 
-- Compute @f^0, f^1, ..., f^(n-1) mod g@, where @g@ has length @glen@ and
-- @f@ is reduced mod @g@ and has length @flen@ (possibly zero spaced).
-- Assumes @res@ is an array of @n@ arrays each with space for at least
-- @glen - 1@ coefficients and that @flen > 0@. We require that @ginv@ of
-- length @ginvlen@ is set to the power series inverse of the reverse of
-- @g@.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_powers_mod_preinv_naive"
  _fmpz_mod_poly_powers_mod_preinv_naive :: Ptr (Ptr CFmpz) -> Ptr CFmpz -> CLong -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_powers_mod_naive/ /res/ /f/ /n/ /g/ /ctx/ 
-- 
-- Set the entries of the array @res@ to @f^0, f^1, ..., f^(n-1) mod g@. No
-- aliasing is permitted between the entries of @res@ and either of the
-- inputs.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_powers_mod_naive"
  fmpz_mod_poly_powers_mod_naive :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> CLong -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_powers_mod_preinv_threaded_pool/ /res/ /f/ /flen/ /n/ /g/ /glen/ /ginv/ /ginvlen/ /p/ /threads/ /num_threads/ 
-- 
-- Compute @f^0, f^1, ..., f^(n-1) mod g@, where @g@ has length @glen@ and
-- @f@ is reduced mod @g@ and has length @flen@ (possibly zero spaced).
-- Assumes @res@ is an array of @n@ arrays each with space for at least
-- @glen - 1@ coefficients and that @flen > 0@. We require that @ginv@ of
-- length @ginvlen@ is set to the power series inverse of the reverse of
-- @g@.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_powers_mod_preinv_threaded_pool"
  _fmpz_mod_poly_powers_mod_preinv_threaded_pool :: Ptr (Ptr CFmpz) -> Ptr CFmpz -> CLong -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CThreadPoolHandle -> CLong -> IO ()

-- | /fmpz_mod_poly_powers_mod_bsgs/ /res/ /f/ /n/ /g/ /ctx/ 
-- 
-- Set the entries of the array @res@ to @f^0, f^1, ..., f^(n-1) mod g@. No
-- aliasing is permitted between the entries of @res@ and either of the
-- inputs.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_powers_mod_bsgs"
  fmpz_mod_poly_powers_mod_bsgs :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> CLong -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_frobenius_powers_2exp_precomp/ /pow/ /f/ /finv/ /m/ /ctx/ 
-- 
-- If @p = f->p@, compute \(x^{(p^1)}\), \(x^{(p^2)}\), \(x^{(p^4)}\), ...,
-- \(x^{(p^{(2^l)})} \pmod{f}\) where \(2^l\) is the greatest power of
-- \(2\) less than or equal to \(m\).
-- 
-- Allows construction of \(x^{(p^k)}\) for \(k = 0\), \(1\), ...,
-- \(x^{(p^m)} \pmod{f}\) using @fmpz_mod_poly_frobenius_power@.
-- 
-- Requires precomputed inverse of \(f\), i.e. newton inverse.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_frobenius_powers_2exp_precomp"
  fmpz_mod_poly_frobenius_powers_2exp_precomp :: Ptr CFmpzModPolyFrobeniusPowers2Exp -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> CULong -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_frobenius_powers_2exp_clear/ /pow/ /ctx/ 
-- 
-- Clear resources used by the @fmpz_mod_poly_frobenius_powers_2exp_t@
-- struct.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_frobenius_powers_2exp_clear"
  fmpz_mod_poly_frobenius_powers_2exp_clear :: Ptr CFmpzModPolyFrobeniusPowers2Exp -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_frobenius_power/ /res/ /pow/ /f/ /m/ /ctx/ 
-- 
-- If @p = f->p@, compute \(x^{(p^m)} \pmod{f}\).
-- 
-- Requires precomputed frobenius powers supplied by
-- @fmpz_mod_poly_frobenius_powers_2exp_precomp@.
-- 
-- If \(m == 0\) and \(f\) has degree \(0\) or \(1\), this performs a
-- division. However an impossible inverse by the leading coefficient of
-- \(f\) will have been caught by
-- @fmpz_mod_poly_frobenius_powers_2exp_precomp@.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_frobenius_power"
  fmpz_mod_poly_frobenius_power :: Ptr CFmpzModPoly -> Ptr CFmpzModPolyFrobeniusPowers2Exp -> Ptr CFmpzModPoly -> CULong -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_frobenius_powers_precomp/ /pow/ /f/ /finv/ /m/ /ctx/ 
-- 
-- If @p = f->p@, compute \(x^{(p^0)}\), \(x^{(p^1)}\), \(x^{(p^2)}\),
-- \(x^{(p^3)}\), ..., \(x^{(p^m)} \pmod{f}\).
-- 
-- Requires precomputed inverse of \(f\), i.e. newton inverse.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_frobenius_powers_precomp"
  fmpz_mod_poly_frobenius_powers_precomp :: Ptr CFmpzModPolyFrobeniusPowers -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> CULong -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_frobenius_powers_clear/ /pow/ /ctx/ 
-- 
-- Clear resources used by the @fmpz_mod_poly_frobenius_powers_t@ struct.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_frobenius_powers_clear"
  fmpz_mod_poly_frobenius_powers_clear :: Ptr CFmpzModPolyFrobeniusPowers -> Ptr CFmpzModCtx -> IO ()

-- Division --------------------------------------------------------------------

-- | /_fmpz_mod_poly_divrem_basecase/ /Q/ /R/ /A/ /lenA/ /B/ /lenB/ /invB/ /p/ 
-- 
-- Computes @(Q, lenA - lenB + 1)@, @(R, lenA)@ such that \(A = B Q + R\)
-- with \(0 \leq \operatorname{len}(R) < \operatorname{len}(B)\).
-- 
-- Assumes that the leading coefficient of \(B\) is invertible modulo
-- \(p\), and that @invB@ is the inverse.
-- 
-- Assumes that \(\operatorname{len}(A), \operatorname{len}(B) > 0\).
-- Allows zero-padding in @(A, lenA)@. \(R\) and \(A\) may be aliased, but
-- apart from this no aliasing of input and output operands is allowed.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_divrem_basecase"
  _fmpz_mod_poly_divrem_basecase :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_divrem_basecase/ /Q/ /R/ /A/ /B/ /ctx/ 
-- 
-- Computes \(Q\), \(R\) such that \(A = B Q + R\) with
-- \(0 \leq \operatorname{len}(R) < \operatorname{len}(B)\).
-- 
-- Assumes that the leading coefficient of \(B\) is invertible modulo
-- \(p\).
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_divrem_basecase"
  fmpz_mod_poly_divrem_basecase :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_divrem_newton_n_preinv/ /Q/ /R/ /A/ /lenA/ /B/ /lenB/ /Binv/ /lenBinv/ /mod/ 
-- 
-- Computes \(Q\) and \(R\) such that \(A = BQ + R\) with
-- \(\operatorname{len}(R)\) less than @lenB@, where \(A\) is of length
-- @lenA@ and \(B\) is of length @lenB@. We require that \(Q\) have space
-- for @lenA - lenB + 1@ coefficients. Furthermore, we assume that \(Binv\)
-- is the inverse of the reverse of \(B\) mod
-- \(x^{\operatorname{len}(B)}\). The algorithm used is to call
-- @div_newton_n_preinv@ and then multiply out and compute the remainder.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_divrem_newton_n_preinv"
  _fmpz_mod_poly_divrem_newton_n_preinv :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_divrem_newton_n_preinv/ /Q/ /R/ /A/ /B/ /Binv/ /ctx/ 
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
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_divrem_newton_n_preinv"
  fmpz_mod_poly_divrem_newton_n_preinv :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- -- | /_fmpz_mod_poly_div_basecase/ /Q/ /R/ /A/ /lenA/ /B/ /lenB/ /invB/ /p/ 
-- -- 
-- -- Notationally, computes \(Q\), \(R\) such that \(A = B Q + R\) with
-- -- \(0 \leq \operatorname{len}(R) < \operatorname{len}(B)\) but only sets
-- -- @(Q, lenA - lenB + 1)@.
-- -- 
-- -- Requires temporary space @(R, lenA)@. Allows aliasing only between \(A\)
-- -- and \(R\). Allows zero-padding in \(A\) but not in \(B\). Assumes that
-- -- the leading coefficient of \(B\) is a unit modulo \(p\).
-- foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_div_basecase"
--   _fmpz_mod_poly_div_basecase :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- -- | /fmpz_mod_poly_div_basecase/ /Q/ /A/ /B/ /ctx/ 
-- -- 
-- -- Notationally, computes \(Q\), \(R\) such that \(A = B Q + R\) with
-- -- \(0 \leq \operatorname{len}(R) < \operatorname{len}(B)\) assuming that
-- -- the leading term of \(B\) is a unit.
-- foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_div_basecase"
--   fmpz_mod_poly_div_basecase :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- -- | /_fmpz_mod_poly_div_divconquer_recursive/ /Q/ /W/ /A/ /B/ /lenB/ /invB/ /p/ 
-- -- 
-- -- [Computes \(Q\) and \(R\) such that \(A = BQ + R\) with \(\operatorname{len}(R)\) less than]
-- --     @lenB@, where @A@ is of length @2 * lenB - 1@ and @B@ is of length
-- --     @lenB@. We require that @Q@ have space for @lenB@ coefficients and
-- --     that @W@ be temporary space of size @2*lenB@.
-- foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_div_divconquer_recursive"
--   _fmpz_mod_poly_div_divconquer_recursive :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- -- | /_fmpz_mod_poly_div_newton/ /Q/ /A/ /lenA/ /B/ /lenB/ /p/ 
-- -- 
-- -- Notationally, computes \(Q\), \(R\) such that \(A = B Q + R\) with
-- -- \(0 \leq \operatorname{len}(R) < \operatorname{len}(B)\) but only sets
-- -- @(Q, lenA - lenB + 1)@.
-- -- 
-- -- Assumes that the leading coefficient of \(B\) is a unit modulo \(p\).
-- -- 
-- -- Reverses the polynomials, divides the resulting series using Newton
-- -- iteration, then reverses the result.
-- foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_div_newton"
--   _fmpz_mod_poly_div_newton :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- -- | /fmpz_mod_poly_div_newton/ /Q/ /A/ /B/ /ctx/ 
-- -- 
-- -- Notationally, computes \(Q\), \(R\) such that \(A = B Q + R\) with
-- -- \(0 \leq \operatorname{len}(R) < \operatorname{len}(B)\) assuming that
-- -- the leading term of \(B\) is a unit.
-- foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_div_newton"
--   fmpz_mod_poly_div_newton :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_div_newton_n_preinv/ /Q/ /A/ /lenA/ /B/ /lenB/ /Binv/ /lenBinv/ /mod/ 
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
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_div_newton_n_preinv"
  _fmpz_mod_poly_div_newton_n_preinv :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_div_newton_n_preinv/ /Q/ /A/ /B/ /Binv/ /ctx/ 
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
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_div_newton_n_preinv"
  fmpz_mod_poly_div_newton_n_preinv :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_remove/ /f/ /g/ /ctx/ 
-- 
-- Removes the highest possible power of @g@ from @f@ and returns the
-- exponent.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_remove"
  fmpz_mod_poly_remove :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO CULong

-- | /_fmpz_mod_poly_rem_basecase/ /R/ /A/ /lenA/ /B/ /lenB/ /invB/ /p/ 
-- 
-- Notationally, computes \(Q\), \(R\) such that \(A = B Q + R\) with
-- \(0 \leq \operatorname{len}(R) < \operatorname{len}(B)\) but only sets
-- @(R, lenB - 1)@.
-- 
-- Allows aliasing only between \(A\) and \(R\). Allows zero-padding in
-- \(A\) but not in \(B\). Assumes that the leading coefficient of \(B\) is
-- a unit modulo \(p\).
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_rem_basecase"
  _fmpz_mod_poly_rem_basecase :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_rem_basecase/ /R/ /A/ /B/ /ctx/ 
-- 
-- Notationally, computes \(Q\), \(R\) such that \(A = B Q + R\) with
-- \(0 \leq \operatorname{len}(R) < \operatorname{len}(B)\) assuming that
-- the leading term of \(B\) is a unit.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_rem_basecase"
  fmpz_mod_poly_rem_basecase :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- -- | /_fmpz_mod_poly_divrem_divconquer_recursive/ /Q/ /BQ/ /W/ /A/ /B/ /lenB/ /invB/ /p/ 
-- -- 
-- -- Computes @(Q, lenB)@, @(BQ, 2 lenB - 1)@ such that \(BQ = B \times Q\)
-- -- and \(A = B Q + R\) where
-- -- \(0 \leq \operatorname{len}(R) < \operatorname{len}(B)\).
-- -- 
-- -- Assumes that the leading coefficient of \(B\) is invertible modulo
-- -- \(p\), and that @invB@ is the inverse.
-- -- 
-- -- Assumes \(\operatorname{len}(B) > 0\). Allows zero-padding in
-- -- @(A, lenA)@. Requires a temporary array @(W, 2 lenB - 1)@. No aliasing
-- -- of input and output operands is allowed.
-- -- 
-- -- This function does not read the bottom \(\operatorname{len}(B) - 1\)
-- -- coefficients from \(A\), which means that they might not even need to
-- -- exist in allocated memory.
-- foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_divrem_divconquer_recursive"
--   _fmpz_mod_poly_divrem_divconquer_recursive :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- -- | /_fmpz_mod_poly_divrem_divconquer/ /Q/ /R/ /A/ /lenA/ /B/ /lenB/ /invB/ /p/ 
-- -- 
-- -- Computes @(Q, lenA - lenB + 1)@, @(R, lenB - 1)@ such that
-- -- \(A = B Q + R\) and
-- -- \(0 \leq \operatorname{len}(R) < \operatorname{len}(B)\).
-- -- 
-- -- Assumes that the leading coefficient of \(B\) is invertible modulo
-- -- \(p\), and that @invB@ is the inverse.
-- -- 
-- -- Assumes \(\operatorname{len}(A) \geq \operatorname{len}(B) > 0\). Allows
-- -- zero-padding in @(A, lenA)@. No aliasing of input and output operands is
-- -- allowed.
-- foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_divrem_divconquer"
--   _fmpz_mod_poly_divrem_divconquer :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- -- | /_fmpz_mod_poly_div_divconquer/ /Q/ /A/ /lenA/ /B/ /lenB/ /invB/ /p/ 
-- -- 
-- -- Notionally computes polynomials \(Q\) and \(R\) such that \(A = BQ + R\)
-- -- with \(\operatorname{len}(R)\) less than @lenB@, where @A@ is of length
-- -- @lenA@ and @B@ is of length @lenB@, but returns only @Q@. We require
-- -- that @Q@ have space for @lenA - lenB + 1@ coefficients.
-- foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_div_divconquer"
--   _fmpz_mod_poly_div_divconquer :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- -- | /fmpz_mod_poly_div_divconquer/ /Q/ /A/ /B/ /ctx/ 
-- -- 
-- -- Notionally computes \(Q\) and \(R\) such that \(A = BQ + R\) with
-- -- \(\operatorname{len}(R) < \operatorname{len}(B)\), but returns only
-- -- \(Q\).
-- foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_div_divconquer"
--   fmpz_mod_poly_div_divconquer :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- -- | /fmpz_mod_poly_divrem_divconquer/ /Q/ /R/ /A/ /B/ /ctx/ 
-- -- 
-- -- Computes \(Q\), \(R\) such that \(A = B Q + R\) and
-- -- \(0 \leq \operatorname{len}(R) < \operatorname{len}(B)\).
-- -- 
-- -- Assumes that \(B\) is non-zero and that the leading coefficient of \(B\)
-- -- is invertible modulo \(p\).
-- foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_divrem_divconquer"
--   fmpz_mod_poly_divrem_divconquer :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_div/ /Q/ /A/ /lenA/ /B/ /lenB/ /p/ 
-- 
-- Notationally, computes \(Q\), \(R\) such that \(A = B Q + R\) with
-- \(0 \leq \operatorname{len}(R) < \operatorname{len}(B)\) but only sets
-- @(Q, lenA - lenB + 1)@.
-- 
-- Assumes that the leading coefficient of \(B\) is a unit modulo \(p\).
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_div"
  _fmpz_mod_poly_div :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_div/ /Q/ /A/ /B/ /ctx/ 
-- 
-- Notationally, computes \(Q\), \(R\) such that \(A = B Q + R\) with
-- \(0 \leq \operatorname{len}(R) < \operatorname{len}(B)\) assuming that
-- the leading term of \(B\) is a unit.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_div"
  fmpz_mod_poly_div :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_divrem/ /Q/ /R/ /A/ /lenA/ /B/ /lenB/ /invB/ /p/ 
-- 
-- Computes @(Q, lenA - lenB + 1)@, @(R, lenB - 1)@ such that
-- \(A = B Q + R\) and
-- \(0 \leq \operatorname{len}(R) < \operatorname{len}(B)\).
-- 
-- Assumes that \(B\) is non-zero, that the leading coefficient of \(B\) is
-- invertible modulo \(p\) and that @invB@ is the inverse.
-- 
-- Assumes \(\operatorname{len}(A) \geq \operatorname{len}(B) > 0\). Allows
-- zero-padding in @(A, lenA)@. No aliasing of input and output operands is
-- allowed.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_divrem"
  _fmpz_mod_poly_divrem :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_divrem/ /Q/ /R/ /A/ /B/ /ctx/ 
-- 
-- Computes \(Q\), \(R\) such that \(A = B Q + R\) and
-- \(0 \leq \operatorname{len}(R) < \operatorname{len}(B)\).
-- 
-- Assumes that \(B\) is non-zero and that the leading coefficient of \(B\)
-- is invertible modulo \(p\).
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_divrem"
  fmpz_mod_poly_divrem :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_divrem_f/ /f/ /Q/ /R/ /A/ /B/ /ctx/ 
-- 
-- Either finds a non-trivial factor~\`f\` of the modulus~\`p\`, or
-- computes \(Q\), \(R\) such that \(A = B Q + R\) and
-- \(0 \leq \operatorname{len}(R) < \operatorname{len}(B)\).
-- 
-- If the leading coefficient of \(B\) is invertible in \(\mathbf{Z}/(p)\),
-- the division with remainder operation is carried out, \(Q\) and \(R\)
-- are computed correctly, and \(f\) is set to \(1\). Otherwise, \(f\) is
-- set to a non-trivial factor of \(p\) and \(Q\) and \(R\) are not
-- touched.
-- 
-- Assumes that \(B\) is non-zero.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_divrem_f"
  fmpz_mod_poly_divrem_f :: Ptr CFmpz -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_rem/ /R/ /A/ /lenA/ /B/ /lenB/ /invB/ /p/ 
-- 
-- Notationally, computes @(Q, lenA - lenB + 1)@, @(R, lenB - 1)@ such that
-- \(A = B Q + R\) and
-- \(0 \leq \operatorname{len}(R) < \operatorname{len}(B)\), returning only
-- the remainder part.
-- 
-- Assumes that \(B\) is non-zero, that the leading coefficient of \(B\) is
-- invertible modulo \(p\) and that @invB@ is the inverse.
-- 
-- Assumes \(\operatorname{len}(A) \geq \operatorname{len}(B) > 0\). Allows
-- zero-padding in @(A, lenA)@. No aliasing of input and output operands is
-- allowed.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_rem"
  _fmpz_mod_poly_rem :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- -- | /_fmpz_mod_poly_rem_f/ /f/ /R/ /A/ /lenA/ /B/ /lenB/ /invB/ /p/ 
-- -- 
-- -- If \(f\) returns with the value \(1\) then the function operates as
-- -- @_fmpz_mod_poly_rem@, otherwise \(f\) will be set to a nontrivial factor
-- -- of \(p\).
-- foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_rem_f"
--   _fmpz_mod_poly_rem_f :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- -- | /fmpz_mod_poly_rem/ /R/ /A/ /B/ /ctx/ 
-- -- 
-- -- Notationally, computes \(Q\), \(R\) such that \(A = B Q + R\) and
-- -- \(0 \leq \operatorname{len}(R) < \operatorname{len}(B)\), returning only
-- -- the remainder part.
-- -- 
-- -- Assumes that \(B\) is non-zero and that the leading coefficient of \(B\)
-- -- is invertible modulo \(p\).
-- foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_rem"
--   fmpz_mod_poly_rem :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- Divisibility testing --------------------------------------------------------

-- | /_fmpz_mod_poly_divides_classical/ /Q/ /A/ /lenA/ /B/ /lenB/ /mod/ 
-- 
-- Returns \(1\) if \((B, lenB)\) divides \((A, lenA)\) and sets
-- \((Q, lenA - lenB + 1)\) to the quotient. Otherwise, returns \(0\) and
-- sets \((Q, lenA - lenB + 1)\) to zero. We require that
-- \(lenA >= lenB > 0\).
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_divides_classical"
  _fmpz_mod_poly_divides_classical :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpzModCtx -> IO CInt

-- | /fmpz_mod_poly_divides_classical/ /Q/ /A/ /B/ /ctx/ 
-- 
-- Returns \(1\) if \(B\) divides \(A\) and sets \(Q\) to the quotient.
-- Otherwise returns \(0\) and sets \(Q\) to zero.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_divides_classical"
  fmpz_mod_poly_divides_classical :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO CInt

-- | /_fmpz_mod_poly_divides/ /Q/ /A/ /lenA/ /B/ /lenB/ /mod/ 
-- 
-- Returns \(1\) if \((B, lenB)\) divides \((A, lenA)\) and sets
-- \((Q, lenA - lenB + 1)\) to the quotient. Otherwise, returns \(0\) and
-- sets \((Q, lenA - lenB + 1)\) to zero. We require that
-- \(lenA >= lenB > 0\).
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_divides"
  _fmpz_mod_poly_divides :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpzModCtx -> IO CInt

-- | /fmpz_mod_poly_divides/ /Q/ /A/ /B/ /ctx/ 
-- 
-- Returns \(1\) if \(B\) divides \(A\) and sets \(Q\) to the quotient.
-- Otherwise returns \(0\) and sets \(Q\) to zero.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_divides"
  fmpz_mod_poly_divides :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO CInt

-- Power series inversion ------------------------------------------------------

-- -- | /_fmpz_mod_poly_inv_series_newton/ /Qinv/ /Q/ /n/ /cinv/ /p/ 
-- -- 
-- -- Sets @(Qinv, n)@ to the inverse of @(Q, n)@ modulo \(x^n\), where
-- -- \(n \geq 1\), assuming that the bottom coefficient of \(Q\) is
-- -- invertible modulo \(p\) and that its inverse is @cinv@.
-- foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_inv_series_newton"
--   _fmpz_mod_poly_inv_series_newton :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- -- | /fmpz_mod_poly_inv_series_newton/ /Qinv/ /Q/ /n/ /ctx/ 
-- -- 
-- -- Sets @Qinv@ to the inverse of @Q@ modulo \(x^n\), where \(n \geq 1\),
-- -- assuming that the bottom coefficient of \(Q\) is a unit.
-- foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_inv_series_newton"
--   fmpz_mod_poly_inv_series_newton :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> CLong -> Ptr CFmpzModCtx -> IO ()

-- -- | /fmpz_mod_poly_inv_series_newton_f/ /f/ /Qinv/ /Q/ /n/ /ctx/ 
-- -- 
-- -- Either sets \(f\) to a nontrivial factor of \(p\) with the value of
-- -- @Qinv@ undefined, or sets @Qinv@ to the inverse of @Q@ modulo \(x^n\),
-- -- where \(n \geq 1\).
-- foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_inv_series_newton_f"
--   fmpz_mod_poly_inv_series_newton_f :: Ptr CFmpz -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_inv_series/ /Qinv/ /Q/ /n/ /cinv/ /p/ 
-- 
-- Sets @(Qinv, n)@ to the inverse of @(Q, n)@ modulo \(x^n\), where
-- \(n \geq 1\), assuming that the bottom coefficient of \(Q\) is
-- invertible modulo \(p\) and that its inverse is @cinv@.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_inv_series"
  _fmpz_mod_poly_inv_series :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_inv_series/ /Qinv/ /Q/ /n/ /ctx/ 
-- 
-- Sets @Qinv@ to the inverse of @Q@ modulo \(x^n\), where \(n \geq 1\),
-- assuming that the bottom coefficient of \(Q\) is a unit.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_inv_series"
  fmpz_mod_poly_inv_series :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_inv_series_f/ /f/ /Qinv/ /Q/ /n/ /ctx/ 
-- 
-- Either sets \(f\) to a nontrivial factor of \(p\) with the value of
-- @Qinv@ undefined, or sets @Qinv@ to the inverse of @Q@ modulo \(x^n\),
-- where \(n \geq 1\).
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_inv_series_f"
  fmpz_mod_poly_inv_series_f :: Ptr CFmpz -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> CLong -> Ptr CFmpzModCtx -> IO ()

-- Power series division -------------------------------------------------------

-- | /_fmpz_mod_poly_div_series/ /Q/ /A/ /Alen/ /B/ /Blen/ /p/ /n/ 
-- 
-- Set @(Q, n)@ to the quotient of the series @(A, Alen@) and @(B, Blen)@
-- assuming @Alen, Blen \<= n@. We assume the bottom coefficient of @B@ is
-- invertible modulo \(p\).
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_div_series"
  _fmpz_mod_poly_div_series :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> IO ()

-- | /fmpz_mod_poly_div_series/ /Q/ /A/ /B/ /n/ /ctx/ 
-- 
-- Set \(Q\) to the quotient of the series \(A\) by \(B\), thinking of the
-- series as though they were of length \(n\). We assume that the bottom
-- coefficient of \(B\) is a unit.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_div_series"
  fmpz_mod_poly_div_series :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> CLong -> Ptr CFmpzModCtx -> IO ()

-- Greatest common divisor -----------------------------------------------------

-- | /fmpz_mod_poly_make_monic/ /res/ /poly/ /ctx/ 
-- 
-- If @poly@ is non-zero, sets @res@ to @poly@ divided by its leading
-- coefficient. This assumes that the leading coefficient of @poly@ is
-- invertible modulo \(p\).
-- 
-- Otherwise, if @poly@ is zero, sets @res@ to zero.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_make_monic"
  fmpz_mod_poly_make_monic :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_make_monic_f/ /f/ /res/ /poly/ /ctx/ 
-- 
-- Either set \(f\) to \(1\) and @res@ to @poly@ divided by its leading
-- coefficient or set \(f\) to a nontrivial factor of \(p\) and leave @res@
-- undefined.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_make_monic_f"
  fmpz_mod_poly_make_monic_f :: Ptr CFmpz -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- -- | /_fmpz_mod_poly_gcd_euclidean/ /G/ /A/ /lenA/ /B/ /lenB/ /invB/ /p/ 
-- -- 
-- -- Sets \(G\) to the greatest common divisor of
-- -- \((A, \operatorname{len}(A))\) and \((B, \operatorname{len}(B))\) and
-- -- returns its length.
-- -- 
-- -- Assumes that \(\operatorname{len}(A) \geq \operatorname{len}(B) > 0\)
-- -- and that the vector \(G\) has space for sufficiently many coefficients.
-- -- 
-- -- Assumes that @invB@ is the inverse of the leading coefficients of \(B\)
-- -- modulo the prime number \(p\).
-- foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_gcd_euclidean"
--   _fmpz_mod_poly_gcd_euclidean :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> IO CLong

-- -- | /fmpz_mod_poly_gcd_euclidean/ /G/ /A/ /B/ /ctx/ 
-- -- 
-- -- Sets \(G\) to the greatest common divisor of \(A\) and \(B\).
-- -- 
-- -- The algorithm used to compute \(G\) is the classical Euclidean
-- -- algorithm.
-- -- 
-- -- In general, the greatest common divisor is defined in the polynomial
-- -- ring \((\mathbf{Z}/(p \mathbf{Z}))[X]\) if and only if \(p\) is a prime
-- -- number. Thus, this function assumes that \(p\) is prime.
-- foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_gcd_euclidean"
--   fmpz_mod_poly_gcd_euclidean :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_gcd/ /G/ /A/ /lenA/ /B/ /lenB/ /invB/ /p/ 
-- 
-- Sets \(G\) to the greatest common divisor of
-- \((A, \operatorname{len}(A))\) and \((B, \operatorname{len}(B))\) and
-- returns its length.
-- 
-- Assumes that \(\operatorname{len}(A) \geq \operatorname{len}(B) > 0\)
-- and that the vector \(G\) has space for sufficiently many coefficients.
-- 
-- Assumes that @invB@ is the inverse of the leading coefficients of \(B\)
-- modulo the prime number \(p\).
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_gcd"
  _fmpz_mod_poly_gcd :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> IO CLong

-- | /fmpz_mod_poly_gcd/ /G/ /A/ /B/ /ctx/ 
-- 
-- Sets \(G\) to the greatest common divisor of \(A\) and \(B\).
-- 
-- In general, the greatest common divisor is defined in the polynomial
-- ring \((\mathbf{Z}/(p \mathbf{Z}))[X]\) if and only if \(p\) is a prime
-- number. Thus, this function assumes that \(p\) is prime.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_gcd"
  fmpz_mod_poly_gcd :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_gcd_euclidean_f/ /f/ /G/ /A/ /lenA/ /B/ /lenB/ /p/ 
-- 
-- Either sets \(f = 1\) and \(G\) to the greatest common divisor of
-- \((A, \operatorname{len}(A))\) and \((B, \operatorname{len}(B))\) and
-- returns its length, or sets \(f \in (1,p)\) to a non-trivial factor of
-- \(p\) and leaves the contents of the vector \((G, lenB)\) undefined.
-- 
-- Assumes that \(\operatorname{len}(A) \geq \operatorname{len}(B) > 0\)
-- and that the vector \(G\) has space for sufficiently many coefficients.
-- 
-- Does not support aliasing of any of the input arguments with any of the
-- output argument.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_gcd_euclidean_f"
  _fmpz_mod_poly_gcd_euclidean_f :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO CLong

-- | /fmpz_mod_poly_gcd_euclidean_f/ /f/ /G/ /A/ /B/ /ctx/ 
-- 
-- Either sets \(f = 1\) and \(G\) to the greatest common divisor of \(A\)
-- and \(B\), or \( \in (1,p)\) to a non-trivial factor of \(p\).
-- 
-- In general, the greatest common divisor is defined in the polynomial
-- ring \((\mathbf{Z}/(p \mathbf{Z}))[X]\) if and only if \(p\) is a prime
-- number.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_gcd_euclidean_f"
  fmpz_mod_poly_gcd_euclidean_f :: Ptr CFmpz -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_gcd_f/ /f/ /G/ /A/ /lenA/ /B/ /lenB/ /p/ 
-- 
-- Either sets \(f = 1\) and \(G\) to the greatest common divisor of
-- \((A, \operatorname{len}(A))\) and \((B, \operatorname{len}(B))\) and
-- returns its length, or sets \(f \in (1,p)\) to a non-trivial factor of
-- \(p\) and leaves the contents of the vector \((G, lenB)\) undefined.
-- 
-- Assumes that \(\operatorname{len}(A) \geq \operatorname{len}(B) > 0\)
-- and that the vector \(G\) has space for sufficiently many coefficients.
-- 
-- Does not support aliasing of any of the input arguments with any of the
-- output arguments.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_gcd_f"
  _fmpz_mod_poly_gcd_f :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO CLong

-- | /fmpz_mod_poly_gcd_f/ /f/ /G/ /A/ /B/ /ctx/ 
-- 
-- Either sets \(f = 1\) and \(G\) to the greatest common divisor of \(A\)
-- and \(B\), or \(f \in (1,p)\) to a non-trivial factor of \(p\).
-- 
-- In general, the greatest common divisor is defined in the polynomial
-- ring \((\mathbf{Z}/(p \mathbf{Z}))[X]\) if and only if \(p\) is a prime
-- number.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_gcd_f"
  fmpz_mod_poly_gcd_f :: Ptr CFmpz -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_hgcd/ /M/ /lenM/ /A/ /lenA/ /B/ /lenB/ /a/ /lena/ /b/ /lenb/ /mod/ 
-- 
-- Computes the HGCD of \(a\) and \(b\), that is, a matrix~\`M\`, a
-- sign~\`sigma\` and two polynomials \(A\) and \(B\) such that
-- 
-- \[`\]
-- \[(A,B)^t = \sigma M^{-1} (a,b)^t.\]
-- 
-- Assumes that \(\operatorname{len}(a) > \operatorname{len}(b) > 0\).
-- 
-- Assumes that \(A\) and \(B\) have space of size at least
-- \(\operatorname{len}(a)\) and \(\operatorname{len}(b)\), respectively.
-- On exit, @*lenA@ and @*lenB@ will contain the correct lengths of \(A\)
-- and \(B\).
-- 
-- Assumes that @M[0]@, @M[1]@, @M[2]@, and @M[3]@ each point to a vector
-- of size at least \(\operatorname{len}(a)\).
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_hgcd"
  _fmpz_mod_poly_hgcd :: Ptr (Ptr CFmpz) -> Ptr CLong -> Ptr CFmpz -> Ptr CLong -> Ptr CFmpz -> Ptr CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO CLong

-- -- | /_fmpz_mod_poly_gcd_hgcd/ /G/ /A/ /lenA/ /B/ /lenB/ /mod/ 
-- -- 
-- -- Computes the monic GCD of \(A\) and \(B\), assuming that
-- -- \(\operatorname{len}(A) \geq \operatorname{len}(B) > 0\).
-- -- 
-- -- Assumes that \(G\) has space for \(\operatorname{len}(B)\) coefficients
-- -- and returns the length of \(G\) on output.
-- foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_gcd_hgcd"
--   _fmpz_mod_poly_gcd_hgcd :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO CLong

-- -- | /fmpz_mod_poly_gcd_hgcd/ /G/ /A/ /B/ /ctx/ 
-- -- 
-- -- Computes the monic GCD of \(A\) and \(B\) using the HGCD algorithm.
-- -- 
-- -- As a special case, the GCD of two zero polynomials is defined to be the
-- -- zero polynomial.
-- -- 
-- -- The time complexity of the algorithm is \(\mathcal{O}(n \log^2 n)\) ring
-- -- operations. For further details, see < [ThullYap1990]>.
-- foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_gcd_hgcd"
--   fmpz_mod_poly_gcd_hgcd :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- -- | /_fmpz_mod_poly_xgcd_euclidean/ /G/ /S/ /T/ /A/ /lenA/ /B/ /lenB/ /invB/ /p/ 
-- -- 
-- -- Computes the GCD of \(A\) and \(B\) together with cofactors \(S\) and
-- -- \(T\) such that \(S A + T B = G\). Returns the length of \(G\).
-- -- 
-- -- Assumes that \(\operatorname{len}(A) \geq \operatorname{len}(B) \geq 1\)
-- -- and \((\operatorname{len}(A),\operatorname{len}(B)) \neq (1,1)\).
-- -- 
-- -- No attempt is made to make the GCD monic.
-- -- 
-- -- Requires that \(G\) have space for \(\operatorname{len}(B)\)
-- -- coefficients. Writes \(\operatorname{len}(B)-1\) and
-- -- \(\operatorname{len}(A)-1\) coefficients to \(S\) and \(T\),
-- -- respectively. Note that, in fact,
-- -- \(\operatorname{len}(S) \leq \max(\operatorname{len}(B) - \operatorname{len}(G), 1)\)
-- -- and
-- -- \(\operatorname{len}(T) \leq \max(\operatorname{len}(A) - \operatorname{len}(G), 1)\).
-- -- 
-- -- No aliasing of input and output operands is permitted.
-- foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_xgcd_euclidean"
--   _fmpz_mod_poly_xgcd_euclidean :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> IO CLong

-- | /_fmpz_mod_poly_xgcd_euclidean_f/ /f/ /G/ /S/ /T/ /A/ /lenA/ /B/ /lenB/ /invB/ /p/ 
-- 
-- If \(f\) returns with the value \(1\) then the function operates as per
-- @_fmpz_mod_poly_xgcd_euclidean@, otherwise \(f\) is set to a nontrivial
-- factor of \(p\).
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_xgcd_euclidean_f"
  _fmpz_mod_poly_xgcd_euclidean_f :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> IO CLong

-- -- | /fmpz_mod_poly_xgcd_euclidean/ /G/ /S/ /T/ /A/ /B/ /ctx/ 
-- -- 
-- -- Computes the GCD of \(A\) and \(B\). The GCD of zero polynomials is
-- -- defined to be zero, whereas the GCD of the zero polynomial and some
-- -- other polynomial \(P\) is defined to be \(P\). Except in the case where
-- -- the GCD is zero, the GCD \(G\) is made monic.
-- -- 
-- -- Polynomials @S@ and @T@ are computed such that @S*A + T*B = G@. The
-- -- length of @S@ will be at most @lenB@ and the length of @T@ will be at
-- -- most @lenA@.
-- foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_xgcd_euclidean"
--   fmpz_mod_poly_xgcd_euclidean :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_xgcd_euclidean_f/ /f/ /G/ /S/ /T/ /A/ /B/ /ctx/ 
-- 
-- If \(f\) returns with the value \(1\) then the function operates as per
-- @fmpz_mod_poly_xgcd_euclidean@, otherwise \(f\) is set to a nontrivial
-- factor of \(p\).
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_xgcd_euclidean_f"
  fmpz_mod_poly_xgcd_euclidean_f :: Ptr CFmpz -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- -- | /_fmpz_mod_poly_xgcd_hgcd/ /G/ /S/ /T/ /A/ /lenA/ /B/ /lenB/ /mod/ 
-- -- 
-- -- Computes the GCD of \(A\) and \(B\), where
-- -- \(\operatorname{len}(A) \geq \operatorname{len}(B) > 0\), together with
-- -- cofactors \(S\) and \(T\) such that \(S A + T B = G\). Returns the
-- -- length of \(G\).
-- -- 
-- -- No attempt is made to make the GCD monic.
-- -- 
-- -- Requires that \(G\) have space for \(\operatorname{len}(B)\)
-- -- coefficients. Writes \(\operatorname{len}(B) - 1\) and
-- -- \(\operatorname{len}(A) - 1\) coefficients to \(S\) and \(T\),
-- -- respectively. Note that, in fact,
-- -- \(\operatorname{len}(S) \leq \operatorname{len}(B) - \operatorname{len}(G)\)
-- -- and
-- -- \(\operatorname{len}(T) \leq \operatorname{len}(A) - \operatorname{len}(G)\).
-- -- 
-- -- Both \(S\) and \(T\) must have space for at least \(2\) coefficients.
-- -- 
-- -- No aliasing of input and output operands is permitted.
-- foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_xgcd_hgcd"
--   _fmpz_mod_poly_xgcd_hgcd :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO CLong

-- -- | /fmpz_mod_poly_xgcd_hgcd/ /G/ /S/ /T/ /A/ /B/ /ctx/ 
-- -- 
-- -- Computes the GCD of \(A\) and \(B\). The GCD of zero polynomials is
-- -- defined to be zero, whereas the GCD of the zero polynomial and some
-- -- other polynomial \(P\) is defined to be \(P\). Except in the case where
-- -- the GCD is zero, the GCD \(G\) is made monic.
-- -- 
-- -- Polynomials @S@ and @T@ are computed such that @S*A + T*B = G@. The
-- -- length of @S@ will be at most @lenB@ and the length of @T@ will be at
-- -- most @lenA@.
-- foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_xgcd_hgcd"
--   fmpz_mod_poly_xgcd_hgcd :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_xgcd/ /G/ /S/ /T/ /A/ /lenA/ /B/ /lenB/ /invB/ /p/ 
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
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_xgcd"
  _fmpz_mod_poly_xgcd :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> IO CLong

-- | /fmpz_mod_poly_xgcd/ /G/ /S/ /T/ /A/ /B/ /ctx/ 
-- 
-- Computes the GCD of \(A\) and \(B\). The GCD of zero polynomials is
-- defined to be zero, whereas the GCD of the zero polynomial and some
-- other polynomial \(P\) is defined to be \(P\). Except in the case where
-- the GCD is zero, the GCD \(G\) is made monic.
-- 
-- Polynomials @S@ and @T@ are computed such that @S*A + T*B = G@. The
-- length of @S@ will be at most @lenB@ and the length of @T@ will be at
-- most @lenA@.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_xgcd"
  fmpz_mod_poly_xgcd :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_xgcd_f/ /f/ /G/ /S/ /T/ /A/ /B/ /ctx/ 
-- 
-- If \(f\) returns with the value \(1\) then the function operates as per
-- @fmpz_mod_poly_xgcd@, otherwise \(f\) is set to a nontrivial factor of
-- \(p\).
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_xgcd_f"
  fmpz_mod_poly_xgcd_f :: Ptr CFmpz -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_gcdinv_euclidean/ /G/ /S/ /A/ /lenA/ /B/ /lenB/ /p/ 
-- 
-- Computes @(G, lenA)@, @(S, lenB-1)@ such that \(G \cong S A \pmod{B}\),
-- returning the actual length of \(G\).
-- 
-- Assumes that \(0 < \operatorname{len}(A) < \operatorname{len}(B)\).
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_gcdinv_euclidean"
  _fmpz_mod_poly_gcdinv_euclidean :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO CLong

-- | /fmpz_mod_poly_gcdinv_euclidean/ /G/ /S/ /A/ /B/ /ctx/ 
-- 
-- Computes polynomials \(G\) and \(S\), both reduced modulo~\`B\`, such
-- that \(G \cong S A \pmod{B}\), where \(B\) is assumed to have
-- \(\operatorname{len}(B) \geq 2\).
-- 
-- In the case that \(A = 0 \pmod{B}\), returns \(G = S = 0\).
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_gcdinv_euclidean"
  fmpz_mod_poly_gcdinv_euclidean :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_gcdinv_euclidean_f/ /f/ /G/ /S/ /A/ /lenA/ /B/ /lenB/ /p/ 
-- 
-- If \(f\) returns with value \(1\) then the function operates as per
-- @_fmpz_mod_poly_gcdinv_euclidean@, otherwise \(f\) is set to a
-- nontrivial factor of \(p\).
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_gcdinv_euclidean_f"
  _fmpz_mod_poly_gcdinv_euclidean_f :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO CLong

-- | /fmpz_mod_poly_gcdinv_euclidean_f/ /f/ /G/ /S/ /A/ /B/ /ctx/ 
-- 
-- If \(f\) returns with value \(1\) then the function operates as per
-- @fmpz_mod_poly_gcdinv_euclidean@, otherwise \(f\) is set to a nontrivial
-- factor of the modulus of \(A\).
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_gcdinv_euclidean_f"
  fmpz_mod_poly_gcdinv_euclidean_f :: Ptr CFmpz -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_gcdinv/ /G/ /S/ /A/ /lenA/ /B/ /lenB/ /p/ 
-- 
-- Computes @(G, lenA)@, @(S, lenB-1)@ such that \(G \cong S A \pmod{B}\),
-- returning the actual length of \(G\).
-- 
-- Assumes that \(0 < \operatorname{len}(A) < \operatorname{len}(B)\).
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_gcdinv"
  _fmpz_mod_poly_gcdinv :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO CLong

-- | /_fmpz_mod_poly_gcdinv_f/ /f/ /G/ /S/ /A/ /lenA/ /B/ /lenB/ /p/ 
-- 
-- If \(f\) returns with value \(1\) then the function operates as per
-- @_fmpz_mod_poly_gcdinv@, otherwise \(f\) will be set to a nontrivial
-- factor of \(p\).
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_gcdinv_f"
  _fmpz_mod_poly_gcdinv_f :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO CLong

-- | /fmpz_mod_poly_gcdinv/ /G/ /S/ /A/ /B/ /ctx/ 
-- 
-- Computes polynomials \(G\) and \(S\), both reduced modulo~\`B\`, such
-- that \(G \cong S A \pmod{B}\), where \(B\) is assumed to have
-- \(\operatorname{len}(B) \geq 2\).
-- 
-- In the case that \(A = 0 \pmod{B}\), returns \(G = S = 0\).
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_gcdinv"
  fmpz_mod_poly_gcdinv :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_gcdinv_f/ /f/ /G/ /S/ /A/ /B/ /ctx/ 
-- 
-- If \(f\) returns with value \(1\) then the function operates as per
-- @fmpz_mod_poly_gcdinv@, otherwise \(f\) will be set to a nontrivial
-- factor of \(p\).
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_gcdinv_f"
  fmpz_mod_poly_gcdinv_f :: Ptr CFmpz -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_invmod/ /A/ /B/ /lenB/ /P/ /lenP/ /p/ 
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
-- Assumes that \(p\) is a prime number.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_invmod"
  _fmpz_mod_poly_invmod :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO CInt

-- | /_fmpz_mod_poly_invmod_f/ /f/ /A/ /B/ /lenB/ /P/ /lenP/ /p/ 
-- 
-- If \(f\) returns with the value \(1\), then the function operates as per
-- @_fmpz_mod_poly_invmod@. Otherwise \(f\) is set to a nontrivial factor
-- of \(p\).
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_invmod_f"
  _fmpz_mod_poly_invmod_f :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO CInt

-- | /fmpz_mod_poly_invmod/ /A/ /B/ /P/ /ctx/ 
-- 
-- Attempts to set \(A\) to the inverse of \(B\) modulo \(P\) in the
-- polynomial ring \((\mathbf{Z}/p\mathbf{Z})[X]\), where we assume that
-- \(p\) is a prime number.
-- 
-- If \(\deg(P) < 2\), raises an exception.
-- 
-- If the greatest common divisor of \(B\) and \(P\) is~\`1\`,
-- returns~\`1\` and sets \(A\) to the inverse of \(B\). Otherwise,
-- returns~\`0\` and the value of \(A\) on exit is undefined.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_invmod"
  fmpz_mod_poly_invmod :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO CInt

-- | /fmpz_mod_poly_invmod_f/ /f/ /A/ /B/ /P/ /ctx/ 
-- 
-- If \(f\) returns with the value \(1\), then the function operates as per
-- @fmpz_mod_poly_invmod@. Otherwise \(f\) is set to a nontrivial factor of
-- \(p\).
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_invmod_f"
  fmpz_mod_poly_invmod_f :: Ptr CFmpz -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO CInt

-- Minpoly ---------------------------------------------------------------------

-- | /_fmpz_mod_poly_minpoly_bm/ /poly/ /seq/ /len/ /p/ 
-- 
-- Sets @poly@ to the coefficients of a minimal generating polynomial for
-- sequence @(seq, len)@ modulo \(p\).
-- 
-- The return value equals the length of @poly@.
-- 
-- It is assumed that \(p\) is prime and @poly@ has space for at least
-- \(len+1\) coefficients. No aliasing between inputs and outputs is
-- allowed.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_minpoly_bm"
  _fmpz_mod_poly_minpoly_bm :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO CLong

-- | /fmpz_mod_poly_minpoly_bm/ /poly/ /seq/ /len/ /ctx/ 
-- 
-- Sets @poly@ to a minimal generating polynomial for sequence @seq@ of
-- length @len@.
-- 
-- Assumes that the modulus is prime.
-- 
-- This version uses the Berlekamp-Massey algorithm, whose running time is
-- proportional to @len@ times the size of the minimal generator.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_minpoly_bm"
  fmpz_mod_poly_minpoly_bm :: Ptr CFmpzModPoly -> Ptr CFmpz -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_minpoly_hgcd/ /poly/ /seq/ /len/ /p/ 
-- 
-- Sets @poly@ to the coefficients of a minimal generating polynomial for
-- sequence @(seq, len)@ modulo \(p\).
-- 
-- The return value equals the length of @poly@.
-- 
-- It is assumed that \(p\) is prime and @poly@ has space for at least
-- \(len+1\) coefficients. No aliasing between inputs and outputs is
-- allowed.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_minpoly_hgcd"
  _fmpz_mod_poly_minpoly_hgcd :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO CLong

-- | /fmpz_mod_poly_minpoly_hgcd/ /poly/ /seq/ /len/ /ctx/ 
-- 
-- Sets @poly@ to a minimal generating polynomial for sequence @seq@ of
-- length @len@.
-- 
-- Assumes that the modulus is prime.
-- 
-- This version uses the HGCD algorithm, whose running time is
-- \(O(n \log^2 n)\) field operations, regardless of the actual size of the
-- minimal generator.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_minpoly_hgcd"
  fmpz_mod_poly_minpoly_hgcd :: Ptr CFmpzModPoly -> Ptr CFmpz -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_minpoly/ /poly/ /seq/ /len/ /p/ 
-- 
-- Sets @poly@ to the coefficients of a minimal generating polynomial for
-- sequence @(seq, len)@ modulo \(p\).
-- 
-- The return value equals the length of @poly@.
-- 
-- It is assumed that \(p\) is prime and @poly@ has space for at least
-- \(len+1\) coefficients. No aliasing between inputs and outputs is
-- allowed.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_minpoly"
  _fmpz_mod_poly_minpoly :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO CLong

-- | /fmpz_mod_poly_minpoly/ /poly/ /seq/ /len/ /ctx/ 
-- 
-- Sets @poly@ to a minimal generating polynomial for sequence @seq@ of
-- length @len@.
-- 
-- A minimal generating polynomial is a monic polynomial
-- \(f = x^d + c_{d-1}x^{d-1} + \cdots + c_1 x + c_0\), of minimal degree
-- \(d\), that annihilates any consecutive \(d+1\) terms in @seq@. That is,
-- for any \(i < len - d\),
-- 
-- \(seq_i = -\sum_{j=0}^{d-1} seq_{i+j}*f_j.\)
-- 
-- Assumes that the modulus is prime.
-- 
-- This version automatically chooses the fastest underlying implementation
-- based on @len@ and the size of the modulus.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_minpoly"
  fmpz_mod_poly_minpoly :: Ptr CFmpzModPoly -> Ptr CFmpz -> CLong -> Ptr CFmpzModCtx -> IO ()

-- Resultant -------------------------------------------------------------------

-- | /_fmpz_mod_poly_resultant_euclidean/ /res/ /poly1/ /len1/ /poly2/ /len2/ /mod/ 
-- 
-- Sets \(r\) to the resultant of @(poly1, len1)@ and @(poly2, len2)@ using
-- the Euclidean algorithm.
-- 
-- Assumes that @len1 >= len2 > 0@.
-- 
-- Assumes that the modulus is prime.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_resultant_euclidean"
  _fmpz_mod_poly_resultant_euclidean :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_resultant_euclidean/ /r/ /f/ /g/ /ctx/ 
-- 
-- Computes the resultant of \(f\) and \(g\) using the Euclidean algorithm.
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
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_resultant_euclidean"
  fmpz_mod_poly_resultant_euclidean :: Ptr CFmpz -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_resultant_hgcd/ /res/ /A/ /lenA/ /B/ /lenB/ /mod/ 
-- 
-- Sets @res@ to the resultant of @(A, lenA)@ and @(B, lenB)@ using the
-- half-gcd algorithm.
-- 
-- This algorithm computes the half-gcd as per @_fmpz_mod_poly_gcd_hgcd@
-- but additionally updates the resultant every time a division occurs. The
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
-- Assumes that @lenA >= lenB > 0@.
-- 
-- Assumes that the modulus is prime.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_resultant_hgcd"
  _fmpz_mod_poly_resultant_hgcd :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_resultant_hgcd/ /res/ /f/ /g/ /ctx/ 
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
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_resultant_hgcd"
  fmpz_mod_poly_resultant_hgcd :: Ptr CFmpz -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_resultant/ /res/ /poly1/ /len1/ /poly2/ /len2/ /mod/ 
-- 
-- Returns the resultant of @(poly1, len1)@ and @(poly2, len2)@.
-- 
-- Assumes that @len1 >= len2 > 0@.
-- 
-- Assumes that the modulus is prime.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_resultant"
  _fmpz_mod_poly_resultant :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_resultant/ /res/ /f/ /g/ /ctx/ 
-- 
-- Computes the resultant of $f$ and $g$.
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
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_resultant"
  fmpz_mod_poly_resultant :: Ptr CFmpz -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- Discriminant ----------------------------------------------------------------

-- | /_fmpz_mod_poly_discriminant/ /d/ /poly/ /len/ /mod/ 
-- 
-- Set \(d\) to the discriminant of @(poly, len)@. Assumes @len > 1@.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_discriminant"
  _fmpz_mod_poly_discriminant :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_discriminant/ /d/ /f/ /ctx/ 
-- 
-- Set \(d\) to the discriminant of \(f\). We normalise the discriminant so
-- that
-- \(\operatorname{disc}(f) = (-1)^(n(n-1)/2) \operatorname{res}(f, f') /
-- \operatorname{lc}(f)^(n - m - 2)\), where @n = len(f)@ and
-- @m = len(f\')@. Thus \(\operatorname{disc}(f) =
-- \operatorname{lc}(f)^(2n - 2) \prod_{i < j} (r_i - r_j)^2\), where
-- \(\operatorname{lc}(f)\) is the leading coefficient of \(f\) and \(r_i\)
-- are the roots of \(f\).
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_discriminant"
  fmpz_mod_poly_discriminant :: Ptr CFmpz -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- Derivative ------------------------------------------------------------------

-- | /_fmpz_mod_poly_derivative/ /res/ /poly/ /len/ /p/ 
-- 
-- Sets @(res, len - 1)@ to the derivative of @(poly, len)@. Also handles
-- the cases where @len@ is \(0\) or \(1\) correctly. Supports aliasing of
-- @res@ and @poly@.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_derivative"
  _fmpz_mod_poly_derivative :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_derivative/ /res/ /poly/ /ctx/ 
-- 
-- Sets @res@ to the derivative of @poly@.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_derivative"
  fmpz_mod_poly_derivative :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- Evaluation ------------------------------------------------------------------

-- | /_fmpz_mod_poly_evaluate_fmpz/ /res/ /poly/ /len/ /a/ /p/ 
-- 
-- Evaluates the polynomial @(poly, len)@ at the integer \(a\) and sets
-- @res@ to the result. Aliasing between @res@ and \(a\) or any of the
-- coefficients of @poly@ is not supported.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_evaluate_fmpz"
  _fmpz_mod_poly_evaluate_fmpz :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_evaluate_fmpz/ /res/ /poly/ /a/ /ctx/ 
-- 
-- Evaluates the polynomial @poly@ at the integer \(a\) and sets @res@ to
-- the result.
-- 
-- As expected, aliasing between @res@ and \(a\) is supported. However,
-- @res@ may not be aliased with a coefficient of @poly@.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_evaluate_fmpz"
  fmpz_mod_poly_evaluate_fmpz :: Ptr CFmpz -> Ptr CFmpzModPoly -> Ptr CFmpz -> Ptr CFmpzModCtx -> IO ()

-- Multipoint evaluation -------------------------------------------------------

-- | /_fmpz_mod_poly_evaluate_fmpz_vec_iter/ /ys/ /coeffs/ /len/ /xs/ /n/ /mod/ 
-- 
-- Evaluates (@coeffs@, @len@) at the @n@ values given in the vector @xs@,
-- writing the output values to @ys@. The values in @xs@ should be reduced
-- modulo the modulus.
-- 
-- Uses Horner\'s method iteratively.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_evaluate_fmpz_vec_iter"
  _fmpz_mod_poly_evaluate_fmpz_vec_iter :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_evaluate_fmpz_vec_iter/ /ys/ /poly/ /xs/ /n/ /ctx/ 
-- 
-- Evaluates @poly@ at the @n@ values given in the vector @xs@, writing the
-- output values to @ys@. The values in @xs@ should be reduced modulo the
-- modulus.
-- 
-- Uses Horner\'s method iteratively.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_evaluate_fmpz_vec_iter"
  fmpz_mod_poly_evaluate_fmpz_vec_iter :: Ptr CFmpz -> Ptr CFmpzModPoly -> Ptr CFmpz -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_evaluate_fmpz_vec_fast_precomp/ /vs/ /poly/ /plen/ /tree/ /len/ /mod/ 
-- 
-- Evaluates (@poly@, @plen@) at the @len@ values given by the precomputed
-- subproduct tree @tree@.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_evaluate_fmpz_vec_fast_precomp"
  _fmpz_mod_poly_evaluate_fmpz_vec_fast_precomp :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr (Ptr CFmpzPoly) -> CLong -> Ptr CFmpz -> IO ()

-- | /_fmpz_mod_poly_evaluate_fmpz_vec_fast/ /ys/ /poly/ /plen/ /xs/ /n/ /mod/ 
-- 
-- Evaluates (@coeffs@, @len@) at the @n@ values given in the vector @xs@,
-- writing the output values to @ys@. The values in @xs@ should be reduced
-- modulo the modulus.
-- 
-- Uses fast multipoint evaluation, building a temporary subproduct tree.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_evaluate_fmpz_vec_fast"
  _fmpz_mod_poly_evaluate_fmpz_vec_fast :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_evaluate_fmpz_vec_fast/ /ys/ /poly/ /xs/ /n/ /ctx/ 
-- 
-- Evaluates @poly@ at the @n@ values given in the vector @xs@, writing the
-- output values to @ys@. The values in @xs@ should be reduced modulo the
-- modulus.
-- 
-- Uses fast multipoint evaluation, building a temporary subproduct tree.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_evaluate_fmpz_vec_fast"
  fmpz_mod_poly_evaluate_fmpz_vec_fast :: Ptr CFmpz -> Ptr CFmpzModPoly -> Ptr CFmpz -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_evaluate_fmpz_vec/ /ys/ /coeffs/ /len/ /xs/ /n/ /mod/ 
-- 
-- Evaluates (@coeffs@, @len@) at the @n@ values given in the vector @xs@,
-- writing the output values to @ys@. The values in @xs@ should be reduced
-- modulo the modulus.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_evaluate_fmpz_vec"
  _fmpz_mod_poly_evaluate_fmpz_vec :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_evaluate_fmpz_vec/ /ys/ /poly/ /xs/ /n/ /ctx/ 
-- 
-- Evaluates @poly@ at the @n@ values given in the vector @xs@, writing the
-- output values to @ys@. The values in @xs@ should be reduced modulo the
-- modulus.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_evaluate_fmpz_vec"
  fmpz_mod_poly_evaluate_fmpz_vec :: Ptr CFmpz -> Ptr CFmpzModPoly -> Ptr CFmpz -> CLong -> Ptr CFmpzModCtx -> IO ()

-- Composition -----------------------------------------------------------------

-- -- | /_fmpz_mod_poly_compose_horner/ /res/ /poly1/ /len1/ /poly2/ /len2/ /p/ 
-- -- 
-- -- Sets @res@ to the composition of @(poly1, len1)@ and @(poly2, len2)@
-- -- using Horner\'s algorithm.
-- -- 
-- -- Assumes that @res@ has space for @(len1-1)*(len2-1) + 1@ coefficients,
-- -- although in \(\mathbf{Z}_p[X]\) this might not actually be the length of
-- -- the resulting polynomial when \(p\) is not a prime.
-- -- 
-- -- Assumes that @poly1@ and @poly2@ are non-zero polynomials. Does not
-- -- support aliasing between any of the inputs and the output.
-- foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_compose_horner"
--   _fmpz_mod_poly_compose_horner :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- -- | /fmpz_mod_poly_compose_horner/ /res/ /poly1/ /poly2/ /ctx/ 
-- -- 
-- -- Sets @res@ to the composition of @poly1@ and @poly2@ using Horner\'s
-- -- algorithm.
-- -- 
-- -- To be precise about the order of composition, denoting @res@, @poly1@,
-- -- and @poly2@ by \(f\), \(g\), and \(h\), respectively, sets
-- -- \(f(t) = g(h(t))\).
-- foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_compose_horner"
--   fmpz_mod_poly_compose_horner :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- -- | /_fmpz_mod_poly_compose_divconquer/ /res/ /poly1/ /len1/ /poly2/ /len2/ /p/ 
-- -- 
-- -- Sets @res@ to the composition of @(poly1, len1)@ and @(poly2, len2)@
-- -- using a divide and conquer algorithm which takes out factors of @poly2@
-- -- raised to \(2^i\) where possible.
-- -- 
-- -- Assumes that @res@ has space for @(len1-1)*(len2-1) + 1@ coefficients,
-- -- although in \(\mathbf{Z}_p[X]\) this might not actually be the length of
-- -- the resulting polynomial when \(p\) is not a prime.
-- -- 
-- -- Assumes that @poly1@ and @poly2@ are non-zero polynomials. Does not
-- -- support aliasing between any of the inputs and the output.
-- foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_compose_divconquer"
--   _fmpz_mod_poly_compose_divconquer :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- -- | /fmpz_mod_poly_compose_divconquer/ /res/ /poly1/ /poly2/ /ctx/ 
-- -- 
-- -- Sets @res@ to the composition of @poly1@ and @poly2@ using a divide and
-- -- conquer algorithm which takes out factors of @poly2@ raised to \(2^i\)
-- -- where possible.
-- -- 
-- -- To be precise about the order of composition, denoting @res@, @poly1@,
-- -- and @poly2@ by \(f\), \(g\), and \(h\), respectively, sets
-- -- \(f(t) = g(h(t))\).
-- foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_compose_divconquer"
--   fmpz_mod_poly_compose_divconquer :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_compose/ /res/ /poly1/ /len1/ /poly2/ /len2/ /p/ 
-- 
-- Sets @res@ to the composition of @(poly1, len1)@ and @(poly2, len2)@.
-- 
-- Assumes that @res@ has space for @(len1-1)*(len2-1) + 1@ coefficients,
-- although in \(\mathbf{Z}_p[X]\) this might not actually be the length of
-- the resulting polynomial when \(p\) is not a prime.
-- 
-- Assumes that @poly1@ and @poly2@ are non-zero polynomials. Does not
-- support aliasing between any of the inputs and the output.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_compose"
  _fmpz_mod_poly_compose :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_compose/ /res/ /poly1/ /poly2/ /ctx/ 
-- 
-- Sets @res@ to the composition of @poly1@ and @poly2@.
-- 
-- To be precise about the order of composition, denoting @res@, @poly1@,
-- and @poly2@ by \(f\), \(g\), and \(h\), respectively, sets
-- \(f(t) = g(h(t))\).
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_compose"
  fmpz_mod_poly_compose :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- Square roots ----------------------------------------------------------------

-- The series expansions for \(\sqrt{h}\) and \(1/\sqrt{h}\) are defined by
-- means of the generalised binomial theorem
-- @h^r = (1+y)^r = \\sum_{k=0}^{\\infty} {r \\choose k} y^k.@ It is
-- assumed that \(h\) has constant term \(1\) and that the coefficients
-- 2^{-k} exist in the coefficient ring (i.e. \(2\) must be invertible).
--
-- | /_fmpz_mod_poly_invsqrt_series/ /g/ /h/ /n/ /mod/ 
-- 
-- Set the first \(n\) terms of \(g\) to the series expansion of
-- \(1/\sqrt{h}\). It is assumed that \(n > 0\), that \(h\) has constant
-- term 1 and that \(h\) is zero-padded as necessary to length \(n\).
-- Aliasing is not permitted.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_invsqrt_series"
  _fmpz_mod_poly_invsqrt_series :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_invsqrt_series/ /g/ /h/ /n/ /ctx/ 
-- 
-- Set \(g\) to the series expansion of \(1/\sqrt{h}\) to order \(O(x^n)\).
-- It is assumed that \(h\) has constant term 1.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_invsqrt_series"
  fmpz_mod_poly_invsqrt_series :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_sqrt_series/ /g/ /h/ /n/ /ctx/ 
-- 
-- Set the first \(n\) terms of \(g\) to the series expansion of
-- \(\sqrt{h}\). It is assumed that \(n > 0\), that \(h\) has constant term
-- 1 and that \(h\) is zero-padded as necessary to length \(n\). Aliasing
-- is not permitted.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_sqrt_series"
  _fmpz_mod_poly_sqrt_series :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_sqrt_series/ /g/ /h/ /n/ /ctx/ 
-- 
-- Set \(g\) to the series expansion of \(\sqrt{h}\) to order \(O(x^n)\).
-- It is assumed that \(h\) has constant term 1.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_sqrt_series"
  fmpz_mod_poly_sqrt_series :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_sqrt/ /s/ /p/ /n/ /mod/ 
-- 
-- If @(p, n)@ is a perfect square, sets @(s, n \/ 2 + 1)@ to a square root
-- of \(p\) and returns 1. Otherwise returns 0.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_sqrt"
  _fmpz_mod_poly_sqrt :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpzModCtx -> IO CInt

-- | /fmpz_mod_poly_sqrt/ /s/ /p/ /mod/ 
-- 
-- If \(p\) is a perfect square, sets \(s\) to a square root of \(p\) and
-- returns 1. Otherwise returns 0.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_sqrt"
  fmpz_mod_poly_sqrt :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO CInt

-- Modular composition ---------------------------------------------------------

-- | /_fmpz_mod_poly_compose_mod/ /res/ /f/ /lenf/ /g/ /h/ /lenh/ /p/ 
-- 
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero and that the length of \(g\) is one less than the
-- length of \(h\) (possibly with zero padding). The output is not allowed
-- to be aliased with any of the inputs.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_compose_mod"
  _fmpz_mod_poly_compose_mod :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_compose_mod/ /res/ /f/ /g/ /h/ /ctx/ 
-- 
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_compose_mod"
  fmpz_mod_poly_compose_mod :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_compose_mod_horner/ /res/ /f/ /lenf/ /g/ /h/ /lenh/ /p/ 
-- 
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero and that the length of \(g\) is one less than the
-- length of \(h\) (possibly with zero padding). The output is not allowed
-- to be aliased with any of the inputs.
-- 
-- The algorithm used is Horner\'s rule.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_compose_mod_horner"
  _fmpz_mod_poly_compose_mod_horner :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_compose_mod_horner/ /res/ /f/ /g/ /h/ /ctx/ 
-- 
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero. The algorithm used is Horner\'s rule.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_compose_mod_horner"
  fmpz_mod_poly_compose_mod_horner :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_compose_mod_brent_kung/ /res/ /f/ /len1/ /g/ /h/ /len3/ /p/ 
-- 
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero and that the length of \(g\) is one less than the
-- length of \(h\) (possibly with zero padding). We also require that the
-- length of \(f\) is less than the length of \(h\). The output is not
-- allowed to be aliased with any of the inputs.
-- 
-- The algorithm used is the Brent-Kung matrix algorithm.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_compose_mod_brent_kung"
  _fmpz_mod_poly_compose_mod_brent_kung :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_compose_mod_brent_kung/ /res/ /f/ /g/ /h/ /ctx/ 
-- 
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero and that \(f\) has smaller degree than \(h\). The
-- algorithm used is the Brent-Kung matrix algorithm.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_compose_mod_brent_kung"
  fmpz_mod_poly_compose_mod_brent_kung :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_reduce_matrix_mod_poly/ /A/ /B/ /f/ /ctx/ 
-- 
-- Sets the ith row of @A@ to the reduction of the ith row of \(B\) modulo
-- \(f\) for \(i=1,\ldots,\sqrt{\deg(f)}\). We require \(B\) to be at least
-- a \(\sqrt{\deg(f)}\times \deg(f)\) matrix and \(f\) to be nonzero.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_reduce_matrix_mod_poly"
  _fmpz_mod_poly_reduce_matrix_mod_poly :: Ptr CFmpzMat -> Ptr CFmpzMat -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_precompute_matrix_worker/ /arg_ptr/ 
-- 
-- Worker function version of @_fmpz_mod_poly_precompute_matrix@.
-- Input\/output is stored in @fmpz_mod_poly_matrix_precompute_arg_t@.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_precompute_matrix_worker"
  _fmpz_mod_poly_precompute_matrix_worker :: Ptr () -> IO ()

-- | /_fmpz_mod_poly_precompute_matrix/ /A/ /f/ /g/ /leng/ /ginv/ /lenginv/ /p/ 
-- 
-- Sets the ith row of @A@ to \(f^i\) modulo \(g\) for
-- \(i=1,\ldots,\sqrt{\deg(g)}\). We require \(A\) to be a
-- \(\sqrt{\deg(g)}\times \deg(g)\) matrix. We require @ginv@ to be the
-- inverse of the reverse of @g@ and \(g\) to be nonzero. @f@ has to be
-- reduced modulo @g@ and of length one less than @leng@ (possibly with
-- zero padding).
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_precompute_matrix"
  _fmpz_mod_poly_precompute_matrix :: Ptr CFmpzMat -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_precompute_matrix/ /A/ /f/ /g/ /ginv/ /ctx/ 
-- 
-- Sets the ith row of @A@ to \(f^i\) modulo \(g\) for
-- \(i=1,\ldots,\sqrt{\deg(g)}\). We require \(A\) to be a
-- \(\sqrt{\deg(g)}\times \deg(g)\) matrix. We require @ginv@ to be the
-- inverse of the reverse of @g@.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_precompute_matrix"
  fmpz_mod_poly_precompute_matrix :: Ptr CFmpzMat -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_compose_mod_brent_kung_precomp_preinv_worker/ /arg_ptr/ 
-- 
-- Worker function version of
-- @_fmpz_mod_poly_compose_mod_brent_kung_precomp_preinv@. Input\/output is
-- stored in @fmpz_mod_poly_compose_mod_precomp_preinv_arg_t@.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_compose_mod_brent_kung_precomp_preinv_worker"
  _fmpz_mod_poly_compose_mod_brent_kung_precomp_preinv_worker :: Ptr () -> IO ()

-- | /_fmpz_mod_poly_compose_mod_brent_kung_precomp_preinv/ /res/ /f/ /lenf/ /A/ /h/ /lenh/ /hinv/ /lenhinv/ /p/ 
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
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_compose_mod_brent_kung_precomp_preinv"
  _fmpz_mod_poly_compose_mod_brent_kung_precomp_preinv :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpzMat -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_compose_mod_brent_kung_precomp_preinv/ /res/ /f/ /A/ /h/ /hinv/ /ctx/ 
-- 
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that the
-- ith row of \(A\) contains \(g^i\) for \(i=1,\ldots,\sqrt{\deg(h)}\),
-- i.e. \(A\) is a \(\sqrt{\deg(h)}\times \deg(h)\) matrix. We require that
-- \(h\) is nonzero and that \(f\) has smaller degree than \(h\).
-- Furthermore, we require @hinv@ to be the inverse of the reverse of @h@.
-- This version of Brent-Kung modular composition is particularly useful if
-- one has to perform several modular composition of the form \(f(g)\)
-- modulo \(h\) for fixed \(g\) and \(h\).
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_compose_mod_brent_kung_precomp_preinv"
  fmpz_mod_poly_compose_mod_brent_kung_precomp_preinv :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzMat -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_compose_mod_brent_kung_preinv/ /res/ /f/ /lenf/ /g/ /h/ /lenh/ /hinv/ /lenhinv/ /p/ 
-- 
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero and that the length of \(g\) is one less than the
-- length of \(h\) (possibly with zero padding). We also require that the
-- length of \(f\) is less than the length of \(h\). Furthermore, we
-- require @hinv@ to be the inverse of the reverse of @h@. The output is
-- not allowed to be aliased with any of the inputs.
-- 
-- The algorithm used is the Brent-Kung matrix algorithm.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_compose_mod_brent_kung_preinv"
  _fmpz_mod_poly_compose_mod_brent_kung_preinv :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_compose_mod_brent_kung_preinv/ /res/ /f/ /g/ /h/ /hinv/ /ctx/ 
-- 
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero and that \(f\) has smaller degree than \(h\).
-- Furthermore, we require @hinv@ to be the inverse of the reverse of @h@.
-- The algorithm used is the Brent-Kung matrix algorithm.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_compose_mod_brent_kung_preinv"
  fmpz_mod_poly_compose_mod_brent_kung_preinv :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_compose_mod_brent_kung_vec_preinv/ /res/ /polys/ /len1/ /l/ /g/ /glen/ /h/ /lenh/ /hinv/ /lenhinv/ /p/ 
-- 
-- Sets @res@ to the composition \(f_i(g)\) modulo \(h\) for
-- \(1\leq i \leq l\), where \(f_i\) are the @l@ elements of @polys@. We
-- require that \(h\) is nonzero and that the length of \(g\) is less than
-- the length of \(h\). We also require that the length of \(f_i\) is less
-- than the length of \(h\). We require @res@ to have enough memory
-- allocated to hold @l@ @fmpz_mod_poly_struct@\'s. The entries of @res@
-- need to be initialised and @l@ needs to be less than @len1@ Furthermore,
-- we require @hinv@ to be the inverse of the reverse of @h@. The output is
-- not allowed to be aliased with any of the inputs.
-- 
-- The algorithm used is the Brent-Kung matrix algorithm.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_compose_mod_brent_kung_vec_preinv"
  _fmpz_mod_poly_compose_mod_brent_kung_vec_preinv :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> CLong -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_compose_mod_brent_kung_vec_preinv/ /res/ /polys/ /len1/ /n/ /g/ /h/ /hinv/ /ctx/ 
-- 
-- Sets @res@ to the composition \(f_i(g)\) modulo \(h\) for
-- \(1\leq i \leq n\) where \(f_i\) are the @n@ elements of @polys@. We
-- require @res@ to have enough memory allocated to hold @n@
-- @fmpz_mod_poly_struct@\'s. The entries of @res@ need to be initialised
-- and @n@ needs to be less than @len1@. We require that \(h\) is nonzero
-- and that \(f_i\) and \(g\) have smaller degree than \(h\). Furthermore,
-- we require @hinv@ to be the inverse of the reverse of @h@. No aliasing
-- of @res@ and @polys@ is allowed. The algorithm used is the Brent-Kung
-- matrix algorithm.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_compose_mod_brent_kung_vec_preinv"
  fmpz_mod_poly_compose_mod_brent_kung_vec_preinv :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> CLong -> CLong -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_compose_mod_brent_kung_vec_preinv_threaded_pool/ /res/ /polys/ /lenpolys/ /l/ /g/ /glen/ /poly/ /len/ /polyinv/ /leninv/ /p/ /threads/ /num_threads/ 
-- 
-- Multithreaded version of
-- @_fmpz_mod_poly_compose_mod_brent_kung_vec_preinv@. Distributing the
-- Horner evaluations across @flint_get_num_threads@ threads.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_compose_mod_brent_kung_vec_preinv_threaded_pool"
  _fmpz_mod_poly_compose_mod_brent_kung_vec_preinv_threaded_pool :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> CLong -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CThreadPoolHandle -> CLong -> IO ()

-- | /fmpz_mod_poly_compose_mod_brent_kung_vec_preinv_threaded_pool/ /res/ /polys/ /len1/ /n/ /g/ /poly/ /polyinv/ /ctx/ /threads/ /num_threads/ 
-- 
-- Multithreaded version of
-- @fmpz_mod_poly_compose_mod_brent_kung_vec_preinv@. Distributing the
-- Horner evaluations across @flint_get_num_threads@ threads.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_compose_mod_brent_kung_vec_preinv_threaded_pool"
  fmpz_mod_poly_compose_mod_brent_kung_vec_preinv_threaded_pool :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> CLong -> CLong -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> Ptr CThreadPoolHandle -> CLong -> IO ()

-- | /fmpz_mod_poly_compose_mod_brent_kung_vec_preinv_threaded/ /res/ /polys/ /len1/ /n/ /g/ /poly/ /polyinv/ /ctx/ 
-- 
-- Multithreaded version of
-- @fmpz_mod_poly_compose_mod_brent_kung_vec_preinv@. Distributing the
-- Horner evaluations across @flint_get_num_threads@ threads.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_compose_mod_brent_kung_vec_preinv_threaded"
  fmpz_mod_poly_compose_mod_brent_kung_vec_preinv_threaded :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> CLong -> CLong -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- Subproduct trees ------------------------------------------------------------

-- | /_fmpz_mod_poly_tree_alloc/ /len/ 
-- 
-- Allocates space for a subproduct tree of the given length, having linear
-- factors at the lowest level.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_tree_alloc"
  _fmpz_mod_poly_tree_alloc :: CLong -> IO (Ptr (Ptr CFmpzPoly))

-- | /_fmpz_mod_poly_tree_free/ /tree/ /len/ 
-- 
-- Free the allocated space for the subproduct.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_tree_free"
  _fmpz_mod_poly_tree_free :: Ptr (Ptr CFmpzPoly) -> CLong -> IO ()

-- | /_fmpz_mod_poly_tree_build/ /tree/ /roots/ /len/ /mod/ 
-- 
-- Builds a subproduct tree in the preallocated space from the @len@ monic
-- linear factors \((x-r_i)\) where \(r_i\) are given by @roots@. The top
-- level product is not computed.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_tree_build"
  _fmpz_mod_poly_tree_build :: Ptr (Ptr CFmpzPoly) -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- Radix conversion ------------------------------------------------------------

-- The following functions provide the functionality to solve the radix
-- conversion problems for polynomials, which is to express a polynomial
-- \(f(X)\) with respect to a given radix \(r(X)\) as
--



-- where \(N = \lfloor\deg(f) / \deg(r)\rfloor\). The algorithm implemented
-- here is a recursive one, which performs Euclidean divisions by powers of
-- \(r\) of the form \(r^{2^i}\), and it has time complexity
-- \(\Theta(\deg(f) \log \deg(f))\). It facilitates the repeated use of
-- precomputed data, namely the powers of \(r\) and their power series
-- inverses. This data is stored in objects of type @fmpz_mod_poly_radix_t@
-- and it is computed using the function @fmpz_mod_poly_radix_init@, which
-- only depends on~\`r\` and an upper bound on the degree of~\`f\`.
--
-- | /_fmpz_mod_poly_radix_init/ /Rpow/ /Rinv/ /R/ /lenR/ /k/ /invL/ /p/ 
-- 
-- Computes powers of \(R\) of the form \(R^{2^i}\) and their Newton
-- inverses modulo \(x^{2^{i} \deg(R)}\) for \(i = 0, \dotsc, k-1\).
-- 
-- Assumes that the vectors @Rpow[i]@ and @Rinv[i]@ have space for
-- \(2^i \deg(R) + 1\) and \(2^i \deg(R)\) coefficients, respectively.
-- 
-- Assumes that the polynomial \(R\) is non-constant, i.e.
-- \(\deg(R) \geq 1\).
-- 
-- Assumes that the leading coefficient of \(R\) is a unit and that the
-- argument @invL@ is the inverse of the coefficient modulo~\`p\`.
-- 
-- The argument~\`p\` is the modulus, which in \(p\)-adic applications is
-- typically a prime power, although this is not necessary. Here, we only
-- assume that \(p \geq 2\).
-- 
-- Note that this precomputed data can be used for any \(F\) such that
-- \(\operatorname{len}(F) \leq 2^k \deg(R)\).
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_radix_init"
  _fmpz_mod_poly_radix_init :: Ptr (Ptr CFmpz) -> Ptr (Ptr CFmpz) -> Ptr CFmpz -> CLong -> CLong -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_radix_init/ /D/ /R/ /degF/ /ctx/ 
-- 
-- Carries out the precomputation necessary to perform radix conversion to
-- radix~\`R\` for polynomials~\`F\` of degree at most @degF@.
-- 
-- Assumes that \(R\) is non-constant, i.e. \(\deg(R) \geq 1\), and that
-- the leading coefficient is a unit.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_radix_init"
  fmpz_mod_poly_radix_init :: Ptr CFmpzModPolyRadix -> Ptr CFmpzModPoly -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_poly_radix/ /B/ /F/ /Rpow/ /Rinv/ /degR/ /k/ /i/ /W/ /p/ 
-- 
-- This is the main recursive function used by the function
-- @fmpz_mod_poly_radix@.
-- 
-- Assumes that, for all \(i = 0, \dotsc, N\), the vector @B[i]@ has space
-- for \(\deg(R)\) coefficients.
-- 
-- The variable \(k\) denotes the factors of \(r\) that have previously
-- been counted for the polynomial \(F\), which is assumed to have length
-- \(2^{i+1} \deg(R)\), possibly including zero-padding.
-- 
-- Assumes that \(W\) is a vector providing temporary space of length
-- \(\operatorname{len}(F) = 2^{i+1} \deg(R)\).
-- 
-- The entire computation takes place over \(\mathbf{Z} / p \mathbf{Z}\),
-- where \(p \geq 2\) is a natural number.
-- 
-- Thus, the top level call will have \(F\) as in the original problem, and
-- \(k = 0\).
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_radix"
  _fmpz_mod_poly_radix :: Ptr (Ptr CFmpz) -> Ptr CFmpz -> Ptr (Ptr CFmpz) -> Ptr (Ptr CFmpz) -> CLong -> CLong -> CLong -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_poly_radix/ /B/ /F/ /D/ /ctx/ 
-- 
-- Given a polynomial \(F\) and the precomputed data \(D\) for the radix
-- \(R\), computes polynomials \(B_0, \dotsc, B_N\) of degree less than
-- \(\deg(R)\) such that
-- 
-- \[`\]
-- \[F = B_0 + B_1 R + \dotsb + B_N R^N,\]
-- 
-- where necessarily \(N = \lfloor\deg(F) / \deg(R)\rfloor\).
-- 
-- Assumes that \(R\) is non-constant, i.e.\(\deg(R) \geq 1\), and that the
-- leading coefficient is a unit.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_radix"
  fmpz_mod_poly_radix :: Ptr (Ptr CFmpzModPoly) -> Ptr CFmpzModPoly -> Ptr CFmpzModPolyRadix -> Ptr CFmpzModCtx -> IO ()

-- Input and output ------------------------------------------------------------

-- The printing options supported by this module are very similar to what
-- can be found in the two related modules @fmpz_poly@ and @nmod_poly@.
-- Consider, for example, the polynomial \(f(x) = 5x^3 + 2x + 1\) in
-- (mathbf{Z}\/6mathbf{Z})[x]. Its simple string representation is
-- @\"4 6  1 2 0 5\"@, where the first two numbers denote the length of the
-- polynomial and the modulus. The pretty string representation is
-- @\"5*x^3+2*x+1\"@.
--
-- | /_fmpz_mod_poly_fprint/ /file/ /poly/ /len/ /p/ 
-- 
-- Prints the polynomial @(poly, len)@ to the stream @file@.
-- 
-- In case of success, returns a positive value. In case of failure,
-- returns a non-positive value.
foreign import ccall "fmpz_mod_poly.h _fmpz_mod_poly_fprint"
  _fmpz_mod_poly_fprint :: Ptr CFile -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO CInt

-- | /fmpz_mod_poly_fprint/ /file/ /poly/ /ctx/ 
-- 
-- Prints the polynomial to the stream @file@.
-- 
-- In case of success, returns a positive value. In case of failure,
-- returns a non-positive value.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_fprint"
  fmpz_mod_poly_fprint :: Ptr CFile -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO CInt

-- | /fmpz_mod_poly_fprint_pretty/ /file/ /poly/ /x/ /ctx/ 
-- 
-- Prints the pretty representation of @(poly, len)@ to the stream @file@,
-- using the string @x@ to represent the indeterminate.
-- 
-- In case of success, returns a positive value. In case of failure,
-- returns a non-positive value.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_fprint_pretty"
  fmpz_mod_poly_fprint_pretty :: Ptr CFile -> Ptr CFmpzModPoly -> CString -> Ptr CFmpzModCtx -> IO CInt

-- | /fmpz_mod_poly_print/ /poly/ /ctx/ 
-- 
-- Prints the polynomial to @stdout@.
-- 
-- In case of success, returns a positive value. In case of failure,
-- returns a non-positive value.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_print"
  fmpz_mod_poly_print :: Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO CInt

-- | /fmpz_mod_poly_print_pretty/ /poly/ /x/ /ctx/ 
-- 
-- Prints the pretty representation of @poly@ to @stdout@, using the string
-- @x@ to represent the indeterminate.
-- 
-- In case of success, returns a positive value. In case of failure,
-- returns a non-positive value.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_print_pretty"
  fmpz_mod_poly_print_pretty :: Ptr CFmpzModPoly -> CString -> Ptr CFmpzModCtx -> IO CInt

-- Inflation and deflation -----------------------------------------------------

-- | /fmpz_mod_poly_inflate/ /result/ /input/ /inflation/ /ctx/ 
-- 
-- Sets @result@ to the inflated polynomial \(p(x^n)\) where \(p\) is given
-- by @input@ and \(n\) is given by @inflation@.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_inflate"
  fmpz_mod_poly_inflate :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> CULong -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_deflate/ /result/ /input/ /deflation/ /ctx/ 
-- 
-- Sets @result@ to the deflated polynomial \(p(x^{1/n})\) where \(p\) is
-- given by @input@ and \(n\) is given by @deflation@. Requires \(n > 0\).
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_deflate"
  fmpz_mod_poly_deflate :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> CULong -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_deflation/ /input/ /ctx/ 
-- 
-- Returns the largest integer by which @input@ can be deflated. As special
-- cases, returns 0 if @input@ is the zero polynomial and 1 of @input@ is a
-- constant polynomial.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_poly_deflation"
  fmpz_mod_poly_deflation :: Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO CULong

-- Berlekamp-Massey Algorithm --------------------------------------------------




-- | /fmpz_mod_berlekamp_massey_init/ /B/ /ctx/ 
-- 
-- Initialize @B@ with an empty stream.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_berlekamp_massey_init"
  fmpz_mod_berlekamp_massey_init :: Ptr CFmpzModBerlekampMassey -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_berlekamp_massey_clear/ /B/ /ctx/ 
-- 
-- Free any space used by @B@.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_berlekamp_massey_clear"
  fmpz_mod_berlekamp_massey_clear :: Ptr CFmpzModBerlekampMassey -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_berlekamp_massey_start_over/ /B/ /ctx/ 
-- 
-- Empty the stream of points in @B@.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_berlekamp_massey_start_over"
  fmpz_mod_berlekamp_massey_start_over :: Ptr CFmpzModBerlekampMassey -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_berlekamp_massey_add_points/ /B/ /a/ /count/ /ctx/ 
-- 
-- Add point(s) to the stream processed by @B@. The addition of any number
-- of points will not update the \(V\) and \(R\) polynomial.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_berlekamp_massey_add_points"
  fmpz_mod_berlekamp_massey_add_points :: Ptr CFmpzModBerlekampMassey -> Ptr CFmpz -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_berlekamp_massey_reduce/ /B/ /ctx/ 
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
foreign import ccall "fmpz_mod_poly.h fmpz_mod_berlekamp_massey_reduce"
  fmpz_mod_berlekamp_massey_reduce :: Ptr CFmpzModBerlekampMassey -> Ptr CFmpzModCtx -> IO CInt

-- | /fmpz_mod_berlekamp_massey_point_count/ /B/ 
-- 
-- Return the number of points stored in @B@.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_berlekamp_massey_point_count"
  fmpz_mod_berlekamp_massey_point_count :: Ptr CFmpzModBerlekampMassey -> IO CLong

-- | /fmpz_mod_berlekamp_massey_points/ /B/ 
-- 
-- Return a pointer the array of points stored in @B@. This may be @NULL@
-- if func::fmpz_mod_berlekamp_massey_point_count returns @0@.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_berlekamp_massey_points"
  fmpz_mod_berlekamp_massey_points :: Ptr CFmpzModBerlekampMassey -> IO (Ptr CFmpz)

-- | /fmpz_mod_berlekamp_massey_V_poly/ /B/ 
-- 
-- Return the polynomial @V@ in @B@.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_berlekamp_massey_V_poly"
  fmpz_mod_berlekamp_massey_V_poly :: Ptr CFmpzModBerlekampMassey -> IO (Ptr CFmpzModPoly)

-- | /fmpz_mod_berlekamp_massey_R_poly/ /B/ 
-- 
-- Return the polynomial @R@ in @B@.
foreign import ccall "fmpz_mod_poly.h fmpz_mod_berlekamp_massey_R_poly"
  fmpz_mod_berlekamp_massey_R_poly :: Ptr CFmpzModBerlekampMassey -> IO (Ptr CFmpzModPoly)

-- Characteristic polynomial ---------------------------------------------------

-- | /fmpz_mod_mat_charpoly/ /p/ /M/ /ctx/ 
-- 
-- Compute the characteristic polynomial \(p\) of the matrix \(M\). The
-- matrix is required to be square, otherwise an exception is raised.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_charpoly"
  fmpz_mod_mat_charpoly :: Ptr CFmpzModPoly -> Ptr CFmpzModMat -> Ptr CFmpzModCtx -> IO ()

-- Minimal polynomial ----------------------------------------------------------

-- | /fmpz_mod_mat_minpoly/ /p/ /M/ /ctx/ 
-- 
-- Compute the minimal polynomial \(p\) of the matrix \(M\). The matrix is
-- required to be square, otherwise an exception is raised.
-- 
-- The modulus is assumed to be prime.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_minpoly"
  fmpz_mod_mat_minpoly :: Ptr CFmpzModPoly -> Ptr CFmpzModMat -> Ptr CFmpzModCtx -> IO ()
