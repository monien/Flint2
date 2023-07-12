
module Data.Number.Flint.Fq.Zech.Poly.FFI (
  -- * Univariate polynomials over finite fields (Zech logarithm representation)
    FqZechPoly (..)
  , CFqZechPoly (..)
  , newFqZechPoly
  , withFqZechPoly
  -- * Memory management
  , fq_zech_poly_init
  , fq_zech_poly_init2
  , fq_zech_poly_realloc
  , fq_zech_poly_fit_length
  , _fq_zech_poly_set_length
  , fq_zech_poly_clear
  , _fq_zech_poly_normalise
  , _fq_zech_poly_normalise2
  , fq_zech_poly_truncate
  , fq_zech_poly_set_trunc
  , _fq_zech_poly_reverse
  , fq_zech_poly_reverse
  -- * Polynomial parameters
  , fq_zech_poly_degree
  , fq_zech_poly_length
  , fq_zech_poly_lead
  -- * Randomisation
  , fq_zech_poly_randtest
  , fq_zech_poly_randtest_not_zero
  , fq_zech_poly_randtest_monic
  , fq_zech_poly_randtest_irreducible
  -- * Assignment and basic manipulation
  , _fq_zech_poly_set
  , fq_zech_poly_set
  , fq_zech_poly_set_fq_zech
  , fq_zech_poly_set_fmpz_mod_poly
  , fq_zech_poly_set_nmod_poly
  , fq_zech_poly_swap
  , _fq_zech_poly_zero
  , fq_zech_poly_zero
  , fq_zech_poly_one
  , fq_zech_poly_gen
  , fq_zech_poly_make_monic
  , _fq_zech_poly_make_monic
  -- * Getting and setting coefficients
  , fq_zech_poly_get_coeff
  , fq_zech_poly_set_coeff
  , fq_zech_poly_set_coeff_fmpz
  -- * Comparison
  , fq_zech_poly_equal
  , fq_zech_poly_equal_trunc
  , fq_zech_poly_is_zero
  , fq_zech_poly_is_one
  , fq_zech_poly_is_gen
  , fq_zech_poly_is_unit
  , fq_zech_poly_equal_fq_zech
  -- * Addition and subtraction
  , _fq_zech_poly_add
  , fq_zech_poly_add
  , fq_zech_poly_add_si
  , fq_zech_poly_add_series
  , _fq_zech_poly_sub
  , fq_zech_poly_sub
  , fq_zech_poly_sub_series
  , _fq_zech_poly_neg
  , fq_zech_poly_neg
  -- * Scalar multiplication and division
  , _fq_zech_poly_scalar_mul_fq_zech
  , fq_zech_poly_scalar_mul_fq_zech
  , _fq_zech_poly_scalar_addmul_fq_zech
  , fq_zech_poly_scalar_addmul_fq_zech
  , _fq_zech_poly_scalar_submul_fq_zech
  , fq_zech_poly_scalar_submul_fq_zech
  --, _fq_zech_poly_scalar_div_fq
  --, fq_zech_poly_scalar_div_fq
  -- * Multiplication
  , _fq_zech_poly_mul_classical
  , fq_zech_poly_mul_classical
  --, _fq_zech_poly_mul_reorder
  --, fq_zech_poly_mul_reorder
  , _fq_zech_poly_mul_KS
  , fq_zech_poly_mul_KS
  , _fq_zech_poly_mul
  , fq_zech_poly_mul
  , _fq_zech_poly_mullow_classical
  , fq_zech_poly_mullow_classical
  , _fq_zech_poly_mullow_KS
  , fq_zech_poly_mullow_KS
  , _fq_zech_poly_mullow
  , fq_zech_poly_mullow
  , _fq_zech_poly_mulhigh_classical
  , fq_zech_poly_mulhigh_classical
  , _fq_zech_poly_mulhigh
  , fq_zech_poly_mulhigh
  , _fq_zech_poly_mulmod
  , fq_zech_poly_mulmod
  , _fq_zech_poly_mulmod_preinv
  , fq_zech_poly_mulmod_preinv
  -- * Squaring
  , _fq_zech_poly_sqr_classical
  , fq_zech_poly_sqr_classical
  , _fq_zech_poly_sqr_KS
  , fq_zech_poly_sqr_KS
  , _fq_zech_poly_sqr
  , fq_zech_poly_sqr
  -- * Powering
  , _fq_zech_poly_pow
  , fq_zech_poly_pow
  , _fq_zech_poly_powmod_ui_binexp
  , fq_zech_poly_powmod_ui_binexp
  , _fq_zech_poly_powmod_ui_binexp_preinv
  , fq_zech_poly_powmod_ui_binexp_preinv
  , _fq_zech_poly_powmod_fmpz_binexp
  , fq_zech_poly_powmod_fmpz_binexp
  , _fq_zech_poly_powmod_fmpz_binexp_preinv
  , fq_zech_poly_powmod_fmpz_binexp_preinv
  , _fq_zech_poly_powmod_fmpz_sliding_preinv
  , fq_zech_poly_powmod_fmpz_sliding_preinv
  , _fq_zech_poly_powmod_x_fmpz_preinv
  , fq_zech_poly_powmod_x_fmpz_preinv
  , _fq_zech_poly_pow_trunc_binexp
  , fq_zech_poly_pow_trunc_binexp
  , _fq_zech_poly_pow_trunc
  , fq_zech_poly_pow_trunc
  -- * Shifting
  , _fq_zech_poly_shift_left
  , fq_zech_poly_shift_left
  , _fq_zech_poly_shift_right
  , fq_zech_poly_shift_right
  -- * Norms
  , _fq_zech_poly_hamming_weight
  , fq_zech_poly_hamming_weight
  -- * Euclidean division
  , _fq_zech_poly_divrem
  , fq_zech_poly_divrem
  , fq_zech_poly_divrem_f
  , _fq_zech_poly_rem
  , fq_zech_poly_rem
  , _fq_zech_poly_div
  , fq_zech_poly_div
  , _fq_zech_poly_div_newton_n_preinv
  , fq_zech_poly_div_newton_n_preinv
  , _fq_zech_poly_divrem_newton_n_preinv
  , fq_zech_poly_divrem_newton_n_preinv
  , _fq_zech_poly_inv_series_newton
  , fq_zech_poly_inv_series_newton
  , _fq_zech_poly_inv_series
  , fq_zech_poly_inv_series
  , _fq_zech_poly_div_series
  , fq_zech_poly_div_series
  -- * Greatest common divisor
  , fq_zech_poly_gcd
  , _fq_zech_poly_gcd
  , _fq_zech_poly_gcd_euclidean_f
  , fq_zech_poly_gcd_euclidean_f
  , _fq_zech_poly_xgcd
  , fq_zech_poly_xgcd
  , _fq_zech_poly_xgcd_euclidean_f
  , fq_zech_poly_xgcd_euclidean_f
  -- * Divisibility testing
  , _fq_zech_poly_divides
  , fq_zech_poly_divides
  -- * Derivative
  , _fq_zech_poly_derivative
  , fq_zech_poly_derivative
  -- * Square root
  , _fq_zech_poly_invsqrt_series
  , fq_zech_poly_invsqrt_series
  , _fq_zech_poly_sqrt_series
  , fq_zech_poly_sqrt_series
  , _fq_zech_poly_sqrt
  , fq_zech_poly_sqrt
  -- * Evaluation
  , _fq_zech_poly_evaluate_fq_zech
  , fq_zech_poly_evaluate_fq_zech
  -- * Composition
  , _fq_zech_poly_compose
  , fq_zech_poly_compose
  , _fq_zech_poly_compose_mod_horner
  , fq_zech_poly_compose_mod_horner
  , _fq_zech_poly_compose_mod_horner_preinv
  , fq_zech_poly_compose_mod_horner_preinv
  , _fq_zech_poly_compose_mod_brent_kung
  , fq_zech_poly_compose_mod_brent_kung
  , _fq_zech_poly_compose_mod_brent_kung_preinv
  , fq_zech_poly_compose_mod_brent_kung_preinv
  , _fq_zech_poly_compose_mod
  , fq_zech_poly_compose_mod
  , _fq_zech_poly_compose_mod_preinv
  , fq_zech_poly_compose_mod_preinv
  , _fq_zech_poly_reduce_matrix_mod_poly
  , _fq_zech_poly_precompute_matrix
  , fq_zech_poly_precompute_matrix
  , _fq_zech_poly_compose_mod_brent_kung_precomp_preinv
  , fq_zech_poly_compose_mod_brent_kung_precomp_preinv
  -- * Output
  , _fq_zech_poly_fprint_pretty
  , fq_zech_poly_fprint_pretty
  , _fq_zech_poly_print_pretty
  , fq_zech_poly_print_pretty
  , _fq_zech_poly_fprint
  , fq_zech_poly_fprint
  , _fq_zech_poly_print
  , fq_zech_poly_print
  , _fq_zech_poly_get_str
  , fq_zech_poly_get_str
  , _fq_zech_poly_get_str_pretty
  , fq_zech_poly_get_str_pretty
  -- * Inflation and deflation
  , fq_zech_poly_inflate
  , fq_zech_poly_deflate
  , fq_zech_poly_deflation
) where 

-- Univariate polynomials over finite fields (Zech logarithm representation)

import Foreign.C.String
import Foreign.C.Types
import qualified Foreign.Concurrent
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr )
import Foreign.Storable
import Foreign.Marshal ( free )

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Mod.Poly
import Data.Number.Flint.NMod.Poly
import Data.Number.Flint.NMod.Mat
import Data.Number.Flint.Fq
import Data.Number.Flint.Fq.Poly
import Data.Number.Flint.Fq.NMod
import Data.Number.Flint.Fq.NMod.Mat

import Data.Number.Flint.Fq.Zech
import Data.Number.Flint.Fq.Zech.Types

#include <flint/flint.h>
#include <flint/fq_zech_poly.h>

-- fq_zech_poly_t --------------------------------------------------------------

instance Storable CFqZechPoly where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fq_zech_poly_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fq_zech_poly_t}
  peek = undefined
  poke = undefined

newFqZechPoly ctx@(FqZechCtx ftx) = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> do
    withFqZechCtx ctx $ \ctx -> do
      fq_zech_poly_init x ctx
    addForeignPtrFinalizerEnv p_fq_zech_poly_clear x ftx
  return $ FqZechPoly x

{-# INLINE withFqZechPoly #-}
withFqZechPoly (FqZechPoly x) f = do
  withForeignPtr x $ \px -> f px >>= return . (FqZechPoly x,)
  

-- Memory management -----------------------------------------------------------

-- | /fq_zech_poly_init/ /poly/ /ctx/ 
--
-- Initialises @poly@ for use, with context ctx, and setting its length to
-- zero. A corresponding call to @fq_zech_poly_clear@ must be made after
-- finishing with the @fq_zech_poly_t@ to free the memory used by the
-- polynomial.
foreign import ccall "fq_zech_poly.h fq_zech_poly_init"
  fq_zech_poly_init :: Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_init2/ /poly/ /alloc/ /ctx/ 
--
-- Initialises @poly@ with space for at least @alloc@ coefficients and sets
-- the length to zero. The allocated coefficients are all set to zero. A
-- corresponding call to @fq_zech_poly_clear@ must be made after finishing
-- with the @fq_zech_poly_t@ to free the memory used by the polynomial.
foreign import ccall "fq_zech_poly.h fq_zech_poly_init2"
  fq_zech_poly_init2 :: Ptr CFqZechPoly -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_realloc/ /poly/ /alloc/ /ctx/ 
--
-- Reallocates the given polynomial to have space for @alloc@ coefficients.
-- If @alloc@ is zero the polynomial is cleared and then reinitialised. If
-- the current length is greater than @alloc@ the polynomial is first
-- truncated to length @alloc@.
foreign import ccall "fq_zech_poly.h fq_zech_poly_realloc"
  fq_zech_poly_realloc :: Ptr CFqZechPoly -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_fit_length/ /poly/ /len/ /ctx/ 
--
-- If @len@ is greater than the number of coefficients currently allocated,
-- then the polynomial is reallocated to have space for at least @len@
-- coefficients. No data is lost when calling this function.
-- 
-- The function efficiently deals with the case where @fit_length@ is
-- called many times in small increments by at least doubling the number of
-- allocated coefficients when length is larger than the number of
-- coefficients currently allocated.
foreign import ccall "fq_zech_poly.h fq_zech_poly_fit_length"
  fq_zech_poly_fit_length :: Ptr CFqZechPoly -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_set_length/ /poly/ /newlen/ /ctx/ 
--
-- Sets the coefficients of @poly@ beyond @len@ to zero and sets the length
-- of @poly@ to @len@.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_set_length"
  _fq_zech_poly_set_length :: Ptr CFqZechPoly -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_clear/ /poly/ /ctx/ 
--
-- Clears the given polynomial, releasing any memory used. It must be
-- reinitialised in order to be used again.
foreign import ccall "fq_zech_poly.h fq_zech_poly_clear"
  fq_zech_poly_clear :: Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

foreign import ccall "fq_zech_poly.h &fq_zech_poly_clear"
  p_fq_zech_poly_clear :: FunPtr (Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ())

-- | /_fq_zech_poly_normalise/ /poly/ /ctx/ 
--
-- Sets the length of @poly@ so that the top coefficient is non-zero. If
-- all coefficients are zero, the length is set to zero. This function is
-- mainly used internally, as all functions guarantee normalisation.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_normalise"
  _fq_zech_poly_normalise :: Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_normalise2/ /poly/ /length/ /ctx/ 
--
-- Sets the length @length@ of @(poly,length)@ so that the top coefficient
-- is non-zero. If all coefficients are zero, the length is set to zero.
-- This function is mainly used internally, as all functions guarantee
-- normalisation.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_normalise2"
  _fq_zech_poly_normalise2 :: Ptr CFqZech -> Ptr CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_truncate/ /poly/ /newlen/ /ctx/ 
--
-- Truncates the polynomial to length at most \(n\).
foreign import ccall "fq_zech_poly.h fq_zech_poly_truncate"
  fq_zech_poly_truncate :: Ptr CFqZechPoly -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_set_trunc/ /poly1/ /poly2/ /newlen/ /ctx/ 
--
-- Sets @poly1@ to @poly2@ truncated to length \(n\).
foreign import ccall "fq_zech_poly.h fq_zech_poly_set_trunc"
  fq_zech_poly_set_trunc :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> CLong -> Ptr CFqCtx -> IO ()

-- | /_fq_zech_poly_reverse/ /output/ /input/ /len/ /m/ /ctx/ 
--
-- Sets @output@ to the reverse of @input@, which is of length @len@, but
-- thinking of it as a polynomial of length @m@, notionally zero-padded if
-- necessary. The length @m@ must be non-negative, but there are no other
-- restrictions. The polynomial @output@ must have space for @m@
-- coefficients.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_reverse"
  _fq_zech_poly_reverse :: Ptr CFqZech -> Ptr CFqZech -> CLong -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_reverse/ /output/ /input/ /m/ /ctx/ 
--
-- Sets @output@ to the reverse of @input@, thinking of it as a polynomial
-- of length @m@, notionally zero-padded if necessary). The length @m@ must
-- be non-negative, but there are no other restrictions. The output
-- polynomial will be set to length @m@ and then normalised.
foreign import ccall "fq_zech_poly.h fq_zech_poly_reverse"
  fq_zech_poly_reverse :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> CLong -> Ptr CFqZechCtx -> IO ()

-- Polynomial parameters -------------------------------------------------------

-- | /fq_zech_poly_degree/ /poly/ /ctx/ 
--
-- Returns the degree of the polynomial @poly@.
foreign import ccall "fq_zech_poly.h fq_zech_poly_degree"
  fq_zech_poly_degree :: Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO CLong

-- | /fq_zech_poly_length/ /poly/ /ctx/ 
--
-- Returns the length of the polynomial @poly@.
foreign import ccall "fq_zech_poly.h fq_zech_poly_length"
  fq_zech_poly_length :: Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO CLong

-- | /fq_zech_poly_lead/ /poly/ /ctx/ 
--
-- Returns a pointer to the leading coefficient of @poly@, or @NULL@ if
-- @poly@ is the zero polynomial.
foreign import ccall "fq_zech_poly.h fq_zech_poly_lead"
  fq_zech_poly_lead :: Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO (Ptr CFqZech)

-- Randomisation ---------------------------------------------------------------

-- | /fq_zech_poly_randtest/ /f/ /state/ /len/ /ctx/ 
--
-- Sets \(f\) to a random polynomial of length at most @len@ with entries
-- in the field described by @ctx@.
foreign import ccall "fq_zech_poly.h fq_zech_poly_randtest"
  fq_zech_poly_randtest :: Ptr CFqZechPoly -> Ptr CFRandState -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_randtest_not_zero/ /f/ /state/ /len/ /ctx/ 
--
-- Same as @fq_zech_poly_randtest@ but guarantees that the polynomial is
-- not zero.
foreign import ccall "fq_zech_poly.h fq_zech_poly_randtest_not_zero"
  fq_zech_poly_randtest_not_zero :: Ptr CFqZechPoly -> Ptr CFRandState -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_randtest_monic/ /f/ /state/ /len/ /ctx/ 
--
-- Sets \(f\) to a random monic polynomial of length @len@ with entries in
-- the field described by @ctx@.
foreign import ccall "fq_zech_poly.h fq_zech_poly_randtest_monic"
  fq_zech_poly_randtest_monic :: Ptr CFqZechPoly -> Ptr CFRandState -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_randtest_irreducible/ /f/ /state/ /len/ /ctx/ 
--
-- Sets \(f\) to a random monic, irreducible polynomial of length @len@
-- with entries in the field described by @ctx@.
foreign import ccall "fq_zech_poly.h fq_zech_poly_randtest_irreducible"
  fq_zech_poly_randtest_irreducible :: Ptr CFqZechPoly -> Ptr CFRandState -> CLong -> Ptr CFqZechCtx -> IO ()

-- Assignment and basic manipulation -------------------------------------------

-- | /_fq_zech_poly_set/ /rop/ /op/ /len/ /ctx/ 
--
-- Sets @(rop, len@) to @(op, len)@.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_set"
  _fq_zech_poly_set :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_set/ /poly1/ /poly2/ /ctx/ 
--
-- Sets the polynomial @poly1@ to the polynomial @poly2@.
foreign import ccall "fq_zech_poly.h fq_zech_poly_set"
  fq_zech_poly_set :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_set_fq_zech/ /poly/ /c/ /ctx/ 
--
-- Sets the polynomial @poly@ to @c@.
foreign import ccall "fq_zech_poly.h fq_zech_poly_set_fq_zech"
  fq_zech_poly_set_fq_zech :: Ptr CFqZechPoly -> Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_set_fmpz_mod_poly/ /rop/ /op/ /ctx/ 
--
-- Sets the polynomial @rop@ to the polynomial @op@
foreign import ccall "fq_zech_poly.h fq_zech_poly_set_fmpz_mod_poly"
  fq_zech_poly_set_fmpz_mod_poly :: Ptr CFqZechPoly -> Ptr CFmpzModPoly -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_set_nmod_poly/ /rop/ /op/ /ctx/ 
--
-- Sets the polynomial @rop@ to the polynomial @op@
foreign import ccall "fq_zech_poly.h fq_zech_poly_set_nmod_poly"
  fq_zech_poly_set_nmod_poly :: Ptr CFqZechPoly -> Ptr CNModPoly -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_swap/ /op1/ /op2/ /ctx/ 
--
-- Swaps the two polynomials @op1@ and @op2@.
foreign import ccall "fq_zech_poly.h fq_zech_poly_swap"
  fq_zech_poly_swap :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_zero/ /rop/ /len/ /ctx/ 
--
-- Sets @(rop, len)@ to the zero polynomial.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_zero"
  _fq_zech_poly_zero :: Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_zero/ /poly/ /ctx/ 
--
-- Sets @poly@ to the zero polynomial.
foreign import ccall "fq_zech_poly.h fq_zech_poly_zero"
  fq_zech_poly_zero :: Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_one/ /poly/ /ctx/ 
--
-- Sets @poly@ to the constant polynomial \(1\).
foreign import ccall "fq_zech_poly.h fq_zech_poly_one"
  fq_zech_poly_one :: Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_gen/ /poly/ /ctx/ 
--
-- Sets @poly@ to the polynomial \(x\).
foreign import ccall "fq_zech_poly.h fq_zech_poly_gen"
  fq_zech_poly_gen :: Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_make_monic/ /rop/ /op/ /ctx/ 
--
-- Sets @rop@ to @op@, normed to have leading coefficient 1.
foreign import ccall "fq_zech_poly.h fq_zech_poly_make_monic"
  fq_zech_poly_make_monic :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_make_monic/ /rop/ /op/ /length/ /ctx/ 
--
-- Sets @rop@ to @(op,length)@, normed to have leading coefficient 1.
-- Assumes that @rop@ has enough space for the polynomial, assumes that
-- @op@ is not zero (and thus has an invertible leading coefficient).
foreign import ccall "fq_zech_poly.h _fq_zech_poly_make_monic"
  _fq_zech_poly_make_monic :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO ()

-- Getting and setting coefficients --------------------------------------------

-- | /fq_zech_poly_get_coeff/ /x/ /poly/ /n/ /ctx/ 
--
-- Sets \(x\) to the coefficient of \(X^n\) in @poly@.
foreign import ccall "fq_zech_poly.h fq_zech_poly_get_coeff"
  fq_zech_poly_get_coeff :: Ptr CFqZech -> Ptr CFqZechPoly -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_set_coeff/ /poly/ /n/ /x/ /ctx/ 
--
-- Sets the coefficient of \(X^n\) in @poly@ to \(x\).
foreign import ccall "fq_zech_poly.h fq_zech_poly_set_coeff"
  fq_zech_poly_set_coeff :: Ptr CFqZechPoly -> CLong -> Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_set_coeff_fmpz/ /poly/ /n/ /x/ /ctx/ 
--
-- Sets the coefficient of \(X^n\) in the polynomial to \(x\), assuming
-- \(n \geq 0\).
foreign import ccall "fq_zech_poly.h fq_zech_poly_set_coeff_fmpz"
  fq_zech_poly_set_coeff_fmpz :: Ptr CFqZechPoly -> CLong -> Ptr CFmpz -> Ptr CFqZechCtx -> IO ()

-- Comparison ------------------------------------------------------------------

-- | /fq_zech_poly_equal/ /poly1/ /poly2/ /ctx/ 
--
-- Returns nonzero if the two polynomials @poly1@ and @poly2@ are equal,
-- otherwise return zero.
foreign import ccall "fq_zech_poly.h fq_zech_poly_equal"
  fq_zech_poly_equal :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO CInt

-- | /fq_zech_poly_equal_trunc/ /poly1/ /poly2/ /n/ /ctx/ 
--
-- Notionally truncate @poly1@ and @poly2@ to length \(n\) and return
-- nonzero if they are equal, otherwise return zero.
foreign import ccall "fq_zech_poly.h fq_zech_poly_equal_trunc"
  fq_zech_poly_equal_trunc :: Ptr CFqPoly -> Ptr CFqPoly -> CLong -> Ptr CFqCtx -> IO CInt

-- | /fq_zech_poly_is_zero/ /poly/ /ctx/ 
--
-- Returns whether the polynomial @poly@ is the zero polynomial.
foreign import ccall "fq_zech_poly.h fq_zech_poly_is_zero"
  fq_zech_poly_is_zero :: Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO CInt

-- | /fq_zech_poly_is_one/ /op/ 
--
-- Returns whether the polynomial @poly@ is equal to the constant
-- polynomial \(1\).
foreign import ccall "fq_zech_poly.h fq_zech_poly_is_one"
  fq_zech_poly_is_one :: Ptr CFqZechPoly -> IO CInt

-- | /fq_zech_poly_is_gen/ /op/ /ctx/ 
--
-- Returns whether the polynomial @poly@ is equal to the polynomial \(x\).
foreign import ccall "fq_zech_poly.h fq_zech_poly_is_gen"
  fq_zech_poly_is_gen :: Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO CInt

-- | /fq_zech_poly_is_unit/ /op/ /ctx/ 
--
-- Returns whether the polynomial @poly@ is a unit in the polynomial ring
-- \(\mathbf{F}_q[X]\), i.e. if it has degree \(0\) and is non-zero.
foreign import ccall "fq_zech_poly.h fq_zech_poly_is_unit"
  fq_zech_poly_is_unit :: Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO CInt

-- | /fq_zech_poly_equal_fq_zech/ /poly/ /c/ /ctx/ 
--
-- Returns whether the polynomial @poly@ is equal the (constant)
-- \(\mathbf{F}_q\) element @c@
foreign import ccall "fq_zech_poly.h fq_zech_poly_equal_fq_zech"
  fq_zech_poly_equal_fq_zech :: Ptr CFqZechPoly -> Ptr CFqZech -> Ptr CFqZechCtx -> IO CInt

-- Addition and subtraction ----------------------------------------------------

-- | /_fq_zech_poly_add/ /res/ /poly1/ /len1/ /poly2/ /len2/ /ctx/ 
--
-- Sets @res@ to the sum of @(poly1,len1)@ and @(poly2,len2)@.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_add"
  _fq_zech_poly_add :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_add/ /res/ /poly1/ /poly2/ /ctx/ 
--
-- Sets @res@ to the sum of @poly1@ and @poly2@.
foreign import ccall "fq_zech_poly.h fq_zech_poly_add"
  fq_zech_poly_add :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_add_si/ /res/ /poly1/ /c/ /ctx/ 
--
-- Sets @res@ to the sum of @poly1@ and @c@.
foreign import ccall "fq_zech_poly.h fq_zech_poly_add_si"
  fq_zech_poly_add_si :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_add_series/ /res/ /poly1/ /poly2/ /n/ /ctx/ 
--
-- Notionally truncate @poly1@ and @poly2@ to length @n@ and set @res@ to
-- the sum.
foreign import ccall "fq_zech_poly.h fq_zech_poly_add_series"
  fq_zech_poly_add_series :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> CLong -> Ptr CFqCtx -> IO ()

-- | /_fq_zech_poly_sub/ /res/ /poly1/ /len1/ /poly2/ /len2/ /ctx/ 
--
-- Sets @res@ to the difference of @(poly1,len1)@ and @(poly2,len2)@.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_sub"
  _fq_zech_poly_sub :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_sub/ /res/ /poly1/ /poly2/ /ctx/ 
--
-- Sets @res@ to the difference of @poly1@ and @poly2@.
foreign import ccall "fq_zech_poly.h fq_zech_poly_sub"
  fq_zech_poly_sub :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_sub_series/ /res/ /poly1/ /poly2/ /n/ /ctx/ 
--
-- Notionally truncate @poly1@ and @poly2@ to length @n@ and set @res@ to
-- the difference.
foreign import ccall "fq_zech_poly.h fq_zech_poly_sub_series"
  fq_zech_poly_sub_series :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> CLong -> Ptr CFqCtx -> IO ()

-- | /_fq_zech_poly_neg/ /rop/ /op/ /len/ /ctx/ 
--
-- Sets @rop@ to the additive inverse of @(op,len)@.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_neg"
  _fq_zech_poly_neg :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_neg/ /res/ /poly/ /ctx/ 
--
-- Sets @res@ to the additive inverse of @poly@.
foreign import ccall "fq_zech_poly.h fq_zech_poly_neg"
  fq_zech_poly_neg :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- Scalar multiplication and division ------------------------------------------

-- | /_fq_zech_poly_scalar_mul_fq_zech/ /rop/ /op/ /len/ /x/ /ctx/ 
--
-- Sets @(rop,len)@ to the product of @(op,len)@ by the scalar @x@, in the
-- context defined by @ctx@.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_scalar_mul_fq_zech"
  _fq_zech_poly_scalar_mul_fq_zech :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_scalar_mul_fq_zech/ /rop/ /op/ /x/ /ctx/ 
--
-- Sets @rop@ to the product of @op@ by the scalar @x@, in the context
-- defined by @ctx@.
foreign import ccall "fq_zech_poly.h fq_zech_poly_scalar_mul_fq_zech"
  fq_zech_poly_scalar_mul_fq_zech :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_scalar_addmul_fq_zech/ /rop/ /op/ /len/ /x/ /ctx/ 
--
-- Adds to @(rop,len)@ the product of @(op,len)@ by the scalar @x@, in the
-- context defined by @ctx@. In particular, assumes the same length for
-- @op@ and @rop@.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_scalar_addmul_fq_zech"
  _fq_zech_poly_scalar_addmul_fq_zech :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_scalar_addmul_fq_zech/ /rop/ /op/ /x/ /ctx/ 
--
-- Adds to @rop@ the product of @op@ by the scalar @x@, in the context
-- defined by @ctx@.
foreign import ccall "fq_zech_poly.h fq_zech_poly_scalar_addmul_fq_zech"
  fq_zech_poly_scalar_addmul_fq_zech :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_scalar_submul_fq_zech/ /rop/ /op/ /len/ /x/ /ctx/ 
--
-- Subtracts from @(rop,len)@ the product of @(op,len)@ by the scalar @x@,
-- in the context defined by @ctx@. In particular, assumes the same length
-- for @op@ and @rop@.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_scalar_submul_fq_zech"
  _fq_zech_poly_scalar_submul_fq_zech :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_scalar_submul_fq_zech/ /rop/ /op/ /x/ /ctx/ 
--
-- Subtracts from @rop@ the product of @op@ by the scalar @x@, in the
-- context defined by @ctx@.
foreign import ccall "fq_zech_poly.h fq_zech_poly_scalar_submul_fq_zech"
  fq_zech_poly_scalar_submul_fq_zech :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- -- | /_fq_zech_poly_scalar_div_fq/ /rop/ /op/ /len/ /x/ /ctx/ 
-- --
-- -- Sets @(rop,len)@ to the quotient of @(op,len)@ by the scalar @x@, in the
-- -- context defined by @ctx@. An exception is raised if @x@ is zero.
-- foreign import ccall "fq_zech_poly.h _fq_zech_poly_scalar_div_fq"
--   _fq_zech_poly_scalar_div_fq :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- -- | /fq_zech_poly_scalar_div_fq/ /rop/ /op/ /x/ /ctx/ 
-- --
-- -- Sets @rop@ to the quotient of @op@ by the scalar @x@, in the context
-- -- defined by @ctx@. An exception is raised if @x@ is zero.
-- foreign import ccall "fq_zech_poly.h fq_zech_poly_scalar_div_fq"
--   fq_zech_poly_scalar_div_fq :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- Multiplication --------------------------------------------------------------

-- | /_fq_zech_poly_mul_classical/ /rop/ /op1/ /len1/ /op2/ /len2/ /ctx/ 
--
-- Sets @(rop, len1 + len2 - 1)@ to the product of @(op1, len1)@ and
-- @(op2, len2)@, assuming that @len1@ is at least @len2@ and neither is
-- zero.
-- 
-- Permits zero padding. Does not support aliasing of @rop@ with either
-- @op1@ or @op2@.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_mul_classical"
  _fq_zech_poly_mul_classical :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_mul_classical/ /rop/ /op1/ /op2/ /ctx/ 
--
-- Sets @rop@ to the product of @op1@ and @op2@ using classical polynomial
-- multiplication.
foreign import ccall "fq_zech_poly.h fq_zech_poly_mul_classical"
  fq_zech_poly_mul_classical :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- -- | /_fq_zech_poly_mul_reorder/ /rop/ /op1/ /len1/ /op2/ /len2/ /ctx/ 
-- --
-- -- Sets @(rop, len1 + len2 - 1)@ to the product of @(op1, len1)@ and
-- -- @(op2, len2)@, assuming that @len1@ and @len2@ are non-zero.
-- -- 
-- -- Permits zero padding. Supports aliasing.
-- foreign import ccall "fq_zech_poly.h _fq_zech_poly_mul_reorder"
--   _fq_zech_poly_mul_reorder :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO ()

-- -- | /fq_zech_poly_mul_reorder/ /rop/ /op1/ /op2/ /ctx/ 
-- --
-- -- Sets @rop@ to the product of @op1@ and @op2@, reordering the two
-- -- indeterminates \(X\) and \(Y\) when viewing the polynomials as elements
-- -- of \(\mathbf{F}_p[X,Y]\).
-- -- 
-- -- Suppose \(\mathbf{F}_q = \mathbf{F}_p[X]/ (f(X))\) and recall that
-- -- elements of \(\mathbf{F}_q\) are internally represented by elements of
-- -- type @fmpz_poly@. For small degree extensions but polynomials in
-- -- \(\mathbf{F}_q[Y]\) of large degree \(n\), we change the representation
-- -- to
-- -- 
-- -- \[`\]
-- -- \[\begin{aligned}
-- -- \begin{split}
-- -- g(Y) & = \sum_{i=0}^{n} a_i(X) Y^i \\
-- --      & = \sum_{j=0}^{d} \sum_{i=0}^{n} \text{Coeff}(a_i(X), j) Y^i.
-- -- \end{split}
-- -- \end{aligned}\]
-- -- 
-- -- This allows us to use a poor algorithm (such as classical
-- -- multiplication) in the \(X\)-direction and leverage the existing fast
-- -- integer multiplication routines in the \(Y\)-direction where the
-- -- polynomial degree \(n\) is large.
-- foreign import ccall "fq_zech_poly.h fq_zech_poly_mul_reorder"
--   fq_zech_poly_mul_reorder :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_mul_KS/ /rop/ /op1/ /len1/ /op2/ /len2/ /ctx/ 
--
-- Sets @(rop, len1 + len2 - 1)@ to the product of @(op1, len1)@ and
-- @(op2, len2)@.
-- 
-- Permits zero padding and places no assumptions on the lengths @len1@ and
-- @len2@. Supports aliasing.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_mul_KS"
  _fq_zech_poly_mul_KS :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_mul_KS/ /rop/ /op1/ /op2/ /ctx/ 
--
-- Sets @rop@ to the product of @op1@ and @op2@ using Kronecker
-- substitution, that is, by encoding each coefficient in
-- \(\mathbf{F}_{q}\) as an integer and reducing this problem to
-- multiplying two polynomials over the integers.
foreign import ccall "fq_zech_poly.h fq_zech_poly_mul_KS"
  fq_zech_poly_mul_KS :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_mul/ /rop/ /op1/ /len1/ /op2/ /len2/ /ctx/ 
--
-- Sets @(rop, len1 + len2 - 1)@ to the product of @(op1, len1)@ and
-- @(op2, len2)@, choosing an appropriate algorithm.
-- 
-- Permits zero padding. Does not support aliasing.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_mul"
  _fq_zech_poly_mul :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_mul/ /rop/ /op1/ /op2/ /ctx/ 
--
-- Sets @rop@ to the product of @op1@ and @op2@, choosing an appropriate
-- algorithm.
foreign import ccall "fq_zech_poly.h fq_zech_poly_mul"
  fq_zech_poly_mul :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_mullow_classical/ /rop/ /op1/ /len1/ /op2/ /len2/ /n/ /ctx/ 
--
-- Sets @(rop, n)@ to the first \(n\) coefficients of @(op1, len1)@
-- multiplied by @(op2, len2)@.
-- 
-- Assumes @0 \< n \<= len1 + len2 - 1@. Assumes neither @len1@ nor @len2@
-- is zero.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_mullow_classical"
  _fq_zech_poly_mullow_classical :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZech -> CLong -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_mullow_classical/ /rop/ /op1/ /op2/ /n/ /ctx/ 
--
-- Sets @rop@ to the product of @op1@ and @op2@, computed using the
-- classical or schoolbook method.
foreign import ccall "fq_zech_poly.h fq_zech_poly_mullow_classical"
  fq_zech_poly_mullow_classical :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_mullow_KS/ /rop/ /op1/ /len1/ /op2/ /len2/ /n/ /ctx/ 
--
-- Sets @(rop, n)@ to the lowest \(n\) coefficients of the product of
-- @(op1, len1)@ and @(op2, len2)@.
-- 
-- Assumes that @len1@ and @len2@ are positive, but does allow for the
-- polynomials to be zero-padded. The polynomials may be zero, too. Assumes
-- \(n\) is positive. Supports aliasing between @rop@, @op1@ and @op2@.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_mullow_KS"
  _fq_zech_poly_mullow_KS :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZech -> CLong -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_mullow_KS/ /rop/ /op1/ /op2/ /n/ /ctx/ 
--
-- Sets @rop@ to the product of @op1@ and @op2@.
foreign import ccall "fq_zech_poly.h fq_zech_poly_mullow_KS"
  fq_zech_poly_mullow_KS :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_mullow/ /rop/ /op1/ /len1/ /op2/ /len2/ /n/ /ctx/ 
--
-- Sets @(rop, n)@ to the lowest \(n\) coefficients of the product of
-- @(op1, len1)@ and @(op2, len2)@.
-- 
-- Assumes @0 \< n \<= len1 + len2 - 1@. Allows for zero-padding in the
-- inputs. Does not support aliasing between the inputs and the output.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_mullow"
  _fq_zech_poly_mullow :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZech -> CLong -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_mullow/ /rop/ /op1/ /op2/ /n/ /ctx/ 
--
-- Sets @rop@ to the lowest \(n\) coefficients of the product of @op1@ and
-- @op2@.
foreign import ccall "fq_zech_poly.h fq_zech_poly_mullow"
  fq_zech_poly_mullow :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_mulhigh_classical/ /res/ /poly1/ /len1/ /poly2/ /len2/ /start/ /ctx/ 
--
-- Computes the product of @(poly1, len1)@ and @(poly2, len2)@ and writes
-- the coefficients from @start@ onwards into the high coefficients of
-- @res@, the remaining coefficients being arbitrary but reduced. Assumes
-- that @len1 >= len2 > 0@. Aliasing of inputs and output is not permitted.
-- Algorithm is classical multiplication.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_mulhigh_classical"
  _fq_zech_poly_mulhigh_classical :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZech -> CLong -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_mulhigh_classical/ /res/ /poly1/ /poly2/ /start/ /ctx/ 
--
-- Computes the product of @poly1@ and @poly2@ and writes the coefficients
-- from @start@ onwards into the high coefficients of @res@, the remaining
-- coefficients being arbitrary but reduced. Algorithm is classical
-- multiplication.
foreign import ccall "fq_zech_poly.h fq_zech_poly_mulhigh_classical"
  fq_zech_poly_mulhigh_classical :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_mulhigh/ /res/ /poly1/ /len1/ /poly2/ /len2/ /start/ /ctx/ 
--
-- Computes the product of @(poly1, len1)@ and @(poly2, len2)@ and writes
-- the coefficients from @start@ onwards into the high coefficients of
-- @res@, the remaining coefficients being arbitrary but reduced. Assumes
-- that @len1 >= len2 > 0@. Aliasing of inputs and output is not permitted.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_mulhigh"
  _fq_zech_poly_mulhigh :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZech -> CLong -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_mulhigh/ /res/ /poly1/ /poly2/ /start/ /ctx/ 
--
-- Computes the product of @poly1@ and @poly2@ and writes the coefficients
-- from @start@ onwards into the high coefficients of @res@, the remaining
-- coefficients being arbitrary but reduced.
foreign import ccall "fq_zech_poly.h fq_zech_poly_mulhigh"
  fq_zech_poly_mulhigh :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_mulmod/ /res/ /poly1/ /len1/ /poly2/ /len2/ /f/ /lenf/ /ctx/ 
--
-- Sets @res@ to the remainder of the product of @poly1@ and @poly2@ upon
-- polynomial division by @f@.
-- 
-- It is required that @len1 + len2 - lenf > 0@, which is equivalent to
-- requiring that the result will actually be reduced. Otherwise, simply
-- use @_fq_zech_poly_mul@ instead.
-- 
-- Aliasing of @f@ and @res@ is not permitted.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_mulmod"
  _fq_zech_poly_mulmod :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZech -> CLong -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_mulmod/ /res/ /poly1/ /poly2/ /f/ /ctx/ 
--
-- Sets @res@ to the remainder of the product of @poly1@ and @poly2@ upon
-- polynomial division by @f@.
foreign import ccall "fq_zech_poly.h fq_zech_poly_mulmod"
  fq_zech_poly_mulmod :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_mulmod_preinv/ /res/ /poly1/ /len1/ /poly2/ /len2/ /f/ /lenf/ /finv/ /lenfinv/ /ctx/ 
--
-- Sets @res@ to the remainder of the product of @poly1@ and @poly2@ upon
-- polynomial division by @f@.
-- 
-- It is required that @finv@ is the inverse of the reverse of @f@ mod
-- @x^lenf@.
-- 
-- Aliasing of @res@ with any of the inputs is not permitted.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_mulmod_preinv"
  _fq_zech_poly_mulmod_preinv :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZech -> CLong -> Ptr CFqZech -> CLong -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_mulmod_preinv/ /res/ /poly1/ /poly2/ /f/ /finv/ /ctx/ 
--
-- Sets @res@ to the remainder of the product of @poly1@ and @poly2@ upon
-- polynomial division by @f@. @finv@ is the inverse of the reverse of @f@.
foreign import ccall "fq_zech_poly.h fq_zech_poly_mulmod_preinv"
  fq_zech_poly_mulmod_preinv :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- Squaring --------------------------------------------------------------------

-- | /_fq_zech_poly_sqr_classical/ /rop/ /op/ /len/ /ctx/ 
--
-- Sets @(rop, 2*len - 1)@ to the square of @(op, len)@, assuming that
-- @(op,len)@ is not zero and using classical polynomial multiplication.
-- 
-- Permits zero padding. Does not support aliasing of @rop@ with either
-- @op1@ or @op2@.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_sqr_classical"
  _fq_zech_poly_sqr_classical :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_sqr_classical/ /rop/ /op/ /ctx/ 
--
-- Sets @rop@ to the square of @op@ using classical polynomial
-- multiplication.
foreign import ccall "fq_zech_poly.h fq_zech_poly_sqr_classical"
  fq_zech_poly_sqr_classical :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_sqr_KS/ /rop/ /op/ /len/ /ctx/ 
--
-- Sets @(rop, 2*len - 1)@ to the square of @(op, len)@.
-- 
-- Permits zero padding and places no assumptions on the lengths @len1@ and
-- @len2@. Supports aliasing.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_sqr_KS"
  _fq_zech_poly_sqr_KS :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_sqr_KS/ /rop/ /op/ /ctx/ 
--
-- Sets @rop@ to the square @op@ using Kronecker substitution, that is, by
-- encoding each coefficient in \(\mathbf{F}_{q}\) as an integer and
-- reducing this problem to multiplying two polynomials over the integers.
foreign import ccall "fq_zech_poly.h fq_zech_poly_sqr_KS"
  fq_zech_poly_sqr_KS :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_sqr/ /rop/ /op/ /len/ /ctx/ 
--
-- Sets @(rop, 2* len - 1)@ to the square of @(op, len)@, choosing an
-- appropriate algorithm.
-- 
-- Permits zero padding. Does not support aliasing.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_sqr"
  _fq_zech_poly_sqr :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_sqr/ /rop/ /op/ /ctx/ 
--
-- Sets @rop@ to the square of @op@, choosing an appropriate algorithm.
foreign import ccall "fq_zech_poly.h fq_zech_poly_sqr"
  fq_zech_poly_sqr :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- Powering --------------------------------------------------------------------

-- | /_fq_zech_poly_pow/ /rop/ /op/ /len/ /e/ /ctx/ 
--
-- Sets @rop = op^e@, assuming that @e, len > 0@ and that @res@ has space
-- for @e*(len - 1) + 1@ coefficients. Does not support aliasing.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_pow"
  _fq_zech_poly_pow :: Ptr CFqZech -> Ptr CFqZech -> CLong -> CULong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_pow/ /rop/ /op/ /e/ /ctx/ 
--
-- Computes @rop = op^e@. If \(e\) is zero, returns one, so that in
-- particular @0^0 = 1@.
foreign import ccall "fq_zech_poly.h fq_zech_poly_pow"
  fq_zech_poly_pow :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> CULong -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_powmod_ui_binexp/ /res/ /poly/ /e/ /f/ /lenf/ /ctx/ 
--
-- Sets @res@ to @poly@ raised to the power @e@ modulo @f@, using binary
-- exponentiation. We require @e > 0@.
-- 
-- We require @lenf > 1@. It is assumed that @poly@ is already reduced
-- modulo @f@ and zero-padded as necessary to have length exactly
-- @lenf - 1@. The output @res@ must have room for @lenf - 1@ coefficients.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_powmod_ui_binexp"
  _fq_zech_poly_powmod_ui_binexp :: Ptr CFqZech -> Ptr CFqZech -> CULong -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_powmod_ui_binexp/ /res/ /poly/ /e/ /f/ /ctx/ 
--
-- Sets @res@ to @poly@ raised to the power @e@ modulo @f@, using binary
-- exponentiation. We require @e >= 0@.
foreign import ccall "fq_zech_poly.h fq_zech_poly_powmod_ui_binexp"
  fq_zech_poly_powmod_ui_binexp :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> CULong -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_powmod_ui_binexp_preinv/ /res/ /poly/ /e/ /f/ /lenf/ /finv/ /lenfinv/ /ctx/ 
--
-- Sets @res@ to @poly@ raised to the power @e@ modulo @f@, using binary
-- exponentiation. We require @e > 0@. We require @finv@ to be the inverse
-- of the reverse of @f@.
-- 
-- We require @lenf > 1@. It is assumed that @poly@ is already reduced
-- modulo @f@ and zero-padded as necessary to have length exactly
-- @lenf - 1@. The output @res@ must have room for @lenf - 1@ coefficients.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_powmod_ui_binexp_preinv"
  _fq_zech_poly_powmod_ui_binexp_preinv :: Ptr CFqZech -> Ptr CFqZech -> CULong -> Ptr CFqZech -> CLong -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_powmod_ui_binexp_preinv/ /res/ /poly/ /e/ /f/ /finv/ /ctx/ 
--
-- Sets @res@ to @poly@ raised to the power @e@ modulo @f@, using binary
-- exponentiation. We require @e >= 0@. We require @finv@ to be the inverse
-- of the reverse of @f@.
foreign import ccall "fq_zech_poly.h fq_zech_poly_powmod_ui_binexp_preinv"
  fq_zech_poly_powmod_ui_binexp_preinv :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> CULong -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_powmod_fmpz_binexp/ /res/ /poly/ /e/ /f/ /lenf/ /ctx/ 
--
-- Sets @res@ to @poly@ raised to the power @e@ modulo @f@, using binary
-- exponentiation. We require @e > 0@.
-- 
-- We require @lenf > 1@. It is assumed that @poly@ is already reduced
-- modulo @f@ and zero-padded as necessary to have length exactly
-- @lenf - 1@. The output @res@ must have room for @lenf - 1@ coefficients.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_powmod_fmpz_binexp"
  _fq_zech_poly_powmod_fmpz_binexp :: Ptr CFqZech -> Ptr CFqZech -> Ptr CFmpz -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_powmod_fmpz_binexp/ /res/ /poly/ /e/ /f/ /ctx/ 
--
-- Sets @res@ to @poly@ raised to the power @e@ modulo @f@, using binary
-- exponentiation. We require @e >= 0@.
foreign import ccall "fq_zech_poly.h fq_zech_poly_powmod_fmpz_binexp"
  fq_zech_poly_powmod_fmpz_binexp :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFmpz -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_powmod_fmpz_binexp_preinv/ /res/ /poly/ /e/ /f/ /lenf/ /finv/ /lenfinv/ /ctx/ 
--
-- Sets @res@ to @poly@ raised to the power @e@ modulo @f@, using binary
-- exponentiation. We require @e > 0@. We require @finv@ to be the inverse
-- of the reverse of @f@.
-- 
-- We require @lenf > 1@. It is assumed that @poly@ is already reduced
-- modulo @f@ and zero-padded as necessary to have length exactly
-- @lenf - 1@. The output @res@ must have room for @lenf - 1@ coefficients.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_powmod_fmpz_binexp_preinv"
  _fq_zech_poly_powmod_fmpz_binexp_preinv :: Ptr CFqZech -> Ptr CFqZech -> Ptr CFmpz -> Ptr CFqZech -> CLong -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_powmod_fmpz_binexp_preinv/ /res/ /poly/ /e/ /f/ /finv/ /ctx/ 
--
-- Sets @res@ to @poly@ raised to the power @e@ modulo @f@, using binary
-- exponentiation. We require @e >= 0@. We require @finv@ to be the inverse
-- of the reverse of @f@.
foreign import ccall "fq_zech_poly.h fq_zech_poly_powmod_fmpz_binexp_preinv"
  fq_zech_poly_powmod_fmpz_binexp_preinv :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFmpz -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_powmod_fmpz_sliding_preinv/ /res/ /poly/ /e/ /k/ /f/ /lenf/ /finv/ /lenfinv/ /ctx/ 
--
-- Sets @res@ to @poly@ raised to the power @e@ modulo @f@, using
-- sliding-window exponentiation with window size @k@. We require @e > 0@.
-- We require @finv@ to be the inverse of the reverse of @f@. If @k@ is set
-- to zero, then an \"optimum\" size will be selected automatically base on
-- @e@.
-- 
-- We require @lenf > 1@. It is assumed that @poly@ is already reduced
-- modulo @f@ and zero-padded as necessary to have length exactly
-- @lenf - 1@. The output @res@ must have room for @lenf - 1@ coefficients.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_powmod_fmpz_sliding_preinv"
  _fq_zech_poly_powmod_fmpz_sliding_preinv :: Ptr CFqZech -> Ptr CFqZech -> Ptr CFmpz -> CULong -> Ptr CFqZech -> CLong -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_powmod_fmpz_sliding_preinv/ /res/ /poly/ /e/ /k/ /f/ /finv/ /ctx/ 
--
-- Sets @res@ to @poly@ raised to the power @e@ modulo @f@, using
-- sliding-window exponentiation with window size @k@. We require @e >= 0@.
-- We require @finv@ to be the inverse of the reverse of @f@. If @k@ is set
-- to zero, then an \"optimum\" size will be selected automatically base on
-- @e@.
foreign import ccall "fq_zech_poly.h fq_zech_poly_powmod_fmpz_sliding_preinv"
  fq_zech_poly_powmod_fmpz_sliding_preinv :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFmpz -> CULong -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_powmod_x_fmpz_preinv/ /res/ /e/ /f/ /lenf/ /finv/ /lenfinv/ /ctx/ 
--
-- Sets @res@ to @x@ raised to the power @e@ modulo @f@, using sliding
-- window exponentiation. We require @e > 0@. We require @finv@ to be the
-- inverse of the reverse of @f@.
-- 
-- We require @lenf > 2@. The output @res@ must have room for @lenf - 1@
-- coefficients.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_powmod_x_fmpz_preinv"
  _fq_zech_poly_powmod_x_fmpz_preinv :: Ptr CFqZech -> Ptr CFmpz -> Ptr CFqZech -> CLong -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_powmod_x_fmpz_preinv/ /res/ /e/ /f/ /finv/ /ctx/ 
--
-- Sets @res@ to @x@ raised to the power @e@ modulo @f@, using sliding
-- window exponentiation. We require @e >= 0@. We require @finv@ to be the
-- inverse of the reverse of @f@.
foreign import ccall "fq_zech_poly.h fq_zech_poly_powmod_x_fmpz_preinv"
  fq_zech_poly_powmod_x_fmpz_preinv :: Ptr CFqZechPoly -> Ptr CFmpz -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_pow_trunc_binexp/ /res/ /poly/ /e/ /trunc/ /ctx/ 
--
-- Sets @res@ to the low @trunc@ coefficients of @poly@ (assumed to be zero
-- padded if necessary to length @trunc@) to the power @e@. This is
-- equivalent to doing a powering followed by a truncation. We require that
-- @res@ has enough space for @trunc@ coefficients, that @trunc > 0@ and
-- that @e > 1@. Aliasing is not permitted. Uses the binary exponentiation
-- method.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_pow_trunc_binexp"
  _fq_zech_poly_pow_trunc_binexp :: Ptr CFqZech -> Ptr CFqZech -> CULong -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_pow_trunc_binexp/ /res/ /poly/ /e/ /trunc/ /ctx/ 
--
-- Sets @res@ to the low @trunc@ coefficients of @poly@ to the power @e@.
-- This is equivalent to doing a powering followed by a truncation. Uses
-- the binary exponentiation method.
foreign import ccall "fq_zech_poly.h fq_zech_poly_pow_trunc_binexp"
  fq_zech_poly_pow_trunc_binexp :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> CULong -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_pow_trunc/ /res/ /poly/ /e/ /trunc/ /mod/ 
--
-- Sets @res@ to the low @trunc@ coefficients of @poly@ (assumed to be zero
-- padded if necessary to length @trunc@) to the power @e@. This is
-- equivalent to doing a powering followed by a truncation. We require that
-- @res@ has enough space for @trunc@ coefficients, that @trunc > 0@ and
-- that @e > 1@. Aliasing is not permitted.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_pow_trunc"
  _fq_zech_poly_pow_trunc :: Ptr CFqZech -> Ptr CFqZech -> CULong -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_pow_trunc/ /res/ /poly/ /e/ /trunc/ /ctx/ 
--
-- Sets @res@ to the low @trunc@ coefficients of @poly@ to the power @e@.
-- This is equivalent to doing a powering followed by a truncation.
foreign import ccall "fq_zech_poly.h fq_zech_poly_pow_trunc"
  fq_zech_poly_pow_trunc :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> CULong -> CLong -> Ptr CFqZechCtx -> IO ()

-- Shifting --------------------------------------------------------------------

-- | /_fq_zech_poly_shift_left/ /rop/ /op/ /len/ /n/ /ctx/ 
--
-- Sets @(rop, len + n)@ to @(op, len)@ shifted left by \(n\) coefficients.
-- 
-- Inserts zero coefficients at the lower end. Assumes that @len@ and \(n\)
-- are positive, and that @rop@ fits @len + n@ elements. Supports aliasing
-- between @rop@ and @op@.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_shift_left"
  _fq_zech_poly_shift_left :: Ptr CFqZech -> Ptr CFqZech -> CLong -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_shift_left/ /rop/ /op/ /n/ /ctx/ 
--
-- Sets @rop@ to @op@ shifted left by \(n\) coeffs. Zero coefficients are
-- inserted.
foreign import ccall "fq_zech_poly.h fq_zech_poly_shift_left"
  fq_zech_poly_shift_left :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_shift_right/ /rop/ /op/ /len/ /n/ /ctx/ 
--
-- Sets @(rop, len - n)@ to @(op, len)@ shifted right by \(n\)
-- coefficients.
-- 
-- Assumes that @len@ and \(n\) are positive, that @len > n@, and that
-- @rop@ fits @len - n@ elements. Supports aliasing between @rop@ and @op@,
-- although in this case the top coefficients of @op@ are not set to zero.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_shift_right"
  _fq_zech_poly_shift_right :: Ptr CFqZech -> Ptr CFqZech -> CLong -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_shift_right/ /rop/ /op/ /n/ /ctx/ 
--
-- Sets @rop@ to @op@ shifted right by \(n\) coefficients. If \(n\) is
-- equal to or greater than the current length of @op@, @rop@ is set to the
-- zero polynomial.
foreign import ccall "fq_zech_poly.h fq_zech_poly_shift_right"
  fq_zech_poly_shift_right :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> CLong -> Ptr CFqZechCtx -> IO ()

-- Norms -----------------------------------------------------------------------

-- | /_fq_zech_poly_hamming_weight/ /op/ /len/ /ctx/ 
--
-- Returns the number of non-zero entries in @(op, len)@.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_hamming_weight"
  _fq_zech_poly_hamming_weight :: Ptr CFqZechPoly -> CLong -> Ptr CFqZechCtx -> IO CLong

-- | /fq_zech_poly_hamming_weight/ /op/ /ctx/ 
--
-- Returns the number of non-zero entries in the polynomial @op@.
foreign import ccall "fq_zech_poly.h fq_zech_poly_hamming_weight"
  fq_zech_poly_hamming_weight :: Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO CLong

-- Euclidean division ----------------------------------------------------------

-- | /_fq_zech_poly_divrem/ /Q/ /R/ /A/ /lenA/ /B/ /lenB/ /invB/ /ctx/ 
--
-- Computes @(Q, lenA - lenB + 1)@, @(R, lenA)@ such that \(A = B Q + R\)
-- with \(0 \leq \operatorname{len}(R) < \operatorname{len}(B)\).
-- 
-- Assumes that the leading coefficient of \(B\) is invertible and that
-- @invB@ is its inverse.
-- 
-- Assumes that \(\operatorname{len}(A), \operatorname{len}(B) > 0\).
-- Allows zero-padding in @(A, lenA)@. \(R\) and \(A\) may be aliased, but
-- apart from this no aliasing of input and output operands is allowed.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_divrem"
  _fq_zech_poly_divrem :: Ptr CFqZech -> Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZech -> CLong -> Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_divrem/ /Q/ /R/ /A/ /B/ /ctx/ 
--
-- Computes \(Q\), \(R\) such that \(A = B Q + R\) with
-- \(0 \leq \operatorname{len}(R) < \operatorname{len}(B)\).
-- 
-- Assumes that the leading coefficient of \(B\) is invertible. This can be
-- taken for granted the context is for a finite field, that is, when \(p\)
-- is prime and \(f(X)\) is irreducible.
foreign import ccall "fq_zech_poly.h fq_zech_poly_divrem"
  fq_zech_poly_divrem :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_divrem_f/ /f/ /Q/ /R/ /A/ /B/ /ctx/ 
--
-- Either finds a non-trivial factor \(f\) of the modulus of @ctx@, or
-- computes \(Q\), \(R\) such that \(A = B Q + R\) and
-- \(0 \leq \operatorname{len}(R) < \operatorname{len}(B)\).
-- 
-- If the leading coefficient of \(B\) is invertible, the division with
-- remainder operation is carried out, \(Q\) and \(R\) are computed
-- correctly, and \(f\) is set to \(1\). Otherwise, \(f\) is set to a
-- non-trivial factor of the modulus and \(Q\) and \(R\) are not touched.
-- 
-- Assumes that \(B\) is non-zero.
foreign import ccall "fq_zech_poly.h fq_zech_poly_divrem_f"
  fq_zech_poly_divrem_f :: Ptr CFqZech -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_rem/ /R/ /A/ /lenA/ /B/ /lenB/ /invB/ /ctx/ 
--
-- Sets @R@ to the remainder of the division of @(A,lenA)@ by @(B,lenB)@.
-- Assumes that the leading coefficient of @(B,lenB)@ is invertible and
-- that @invB@ is its inverse.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_rem"
  _fq_zech_poly_rem :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZech -> CLong -> Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_rem/ /R/ /A/ /B/ /ctx/ 
--
-- Sets @R@ to the remainder of the division of @A@ by @B@ in the context
-- described by @ctx@.
foreign import ccall "fq_zech_poly.h fq_zech_poly_rem"
  fq_zech_poly_rem :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_div/ /Q/ /A/ /lenA/ /B/ /lenB/ /invB/ /ctx/ 
--
-- Notationally, computes \(Q\), \(R\) such that \(A = B Q + R\) with \(0
-- \leq \operatorname{len}(R) < \operatorname{len}(B)\) but only sets
-- @(Q, lenA - lenB + 1)@.
-- 
-- Allows zero-padding in \(A\) but not in \(B\). Assumes that the leading
-- coefficient of \(B\) is a unit.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_div"
  _fq_zech_poly_div :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZech -> CLong -> Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_div/ /Q/ /A/ /B/ /ctx/ 
--
-- Notionally finds polynomials \(Q\) and \(R\) such that \(A = B Q + R\)
-- with \(\operatorname{len}(R) < \operatorname{len}(B)\), but returns only
-- @Q@. If \(\operatorname{len}(B) = 0\) an exception is raised.
foreign import ccall "fq_zech_poly.h fq_zech_poly_div"
  fq_zech_poly_div :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_div_newton_n_preinv/ /Q/ /A/ /lenA/ /B/ /lenB/ /Binv/ /lenBinv/ /ctx_t/ 
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
foreign import ccall "fq_zech_poly.h _fq_zech_poly_div_newton_n_preinv"
  _fq_zech_poly_div_newton_n_preinv :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZech -> CLong -> Ptr CFqZech -> CLong -> Ptr CFqZech -> IO ()

-- | /fq_zech_poly_div_newton_n_preinv/ /Q/ /A/ /B/ /Binv/ /ctx/ 
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
foreign import ccall "fq_zech_poly.h fq_zech_poly_div_newton_n_preinv"
  fq_zech_poly_div_newton_n_preinv :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_divrem_newton_n_preinv/ /Q/ /R/ /A/ /lenA/ /B/ /lenB/ /Binv/ /lenBinv/ /ctx/ 
--
-- Computes \(Q\) and \(R\) such that \(A = BQ + R\) with
-- \(\operatorname{len}(R)\) less than @lenB@, where \(A\) is of length
-- @lenA@ and \(B\) is of length @lenB@. We require that \(Q\) have space
-- for @lenA - lenB + 1@ coefficients. Furthermore, we assume that \(Binv\)
-- is the inverse of the reverse of \(B\) mod
-- \(x^{\operatorname{len}(B)}\). The algorithm used is to call
-- @div_newton_preinv@ and then multiply out and compute the remainder.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_divrem_newton_n_preinv"
  _fq_zech_poly_divrem_newton_n_preinv :: Ptr CFqZech -> Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZech -> CLong -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_divrem_newton_n_preinv/ /Q/ /R/ /A/ /B/ /Binv/ /ctx/ 
--
-- Computes \(Q\) and \(R\) such that \(A = BQ + R\) with
-- \(\operatorname{len}(R) <
-- \operatorname{len}(B)\). We assume \(Binv\) is the inverse of the
-- reverse of \(B\) mod \(x^{\operatorname{len}(B)}\).
-- 
-- It is required that the length of \(A\) is less than or equal to 2*the
-- length of \(B\) - 2.
-- 
-- The algorithm used is to call @div_newton@ and then multiply out and
-- compute the remainder.
foreign import ccall "fq_zech_poly.h fq_zech_poly_divrem_newton_n_preinv"
  fq_zech_poly_divrem_newton_n_preinv :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_inv_series_newton/ /Qinv/ /Q/ /n/ /ctx/ 
--
-- Given @Q@ of length @n@ whose constant coefficient is invertible modulo
-- the given modulus, find a polynomial @Qinv@ of length @n@ such that
-- @Q * Qinv@ is @1@ modulo \(x^n\). Requires @n > 0@. This function can be
-- viewed as inverting a power series via Newton iteration.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_inv_series_newton"
  _fq_zech_poly_inv_series_newton :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_inv_series_newton/ /Qinv/ /Q/ /n/ /ctx/ 
--
-- Given @Q@ find @Qinv@ such that @Q * Qinv@ is @1@ modulo \(x^n\). The
-- constant coefficient of @Q@ must be invertible modulo the modulus of
-- @Q@. An exception is raised if this is not the case or if @n = 0@. This
-- function can be viewed as inverting a power series via Newton iteration.
foreign import ccall "fq_zech_poly.h fq_zech_poly_inv_series_newton"
  fq_zech_poly_inv_series_newton :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_inv_series/ /Qinv/ /Q/ /n/ /ctx/ 
--
-- Given @Q@ of length @n@ whose constant coefficient is invertible modulo
-- the given modulus, find a polynomial @Qinv@ of length @n@ such that
-- @Q * Qinv@ is @1@ modulo \(x^n\). Requires @n > 0@.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_inv_series"
  _fq_zech_poly_inv_series :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_inv_series/ /Qinv/ /Q/ /n/ /ctx/ 
--
-- Given @Q@ find @Qinv@ such that @Q * Qinv@ is @1@ modulo \(x^n\). The
-- constant coefficient of @Q@ must be invertible modulo the modulus of
-- @Q@. An exception is raised if this is not the case or if @n = 0@.
foreign import ccall "fq_zech_poly.h fq_zech_poly_inv_series"
  fq_zech_poly_inv_series :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_div_series/ /Q/ /A/ /Alen/ /B/ /Blen/ /n/ /ctx/ 
--
-- Set @(Q, n)@ to the quotient of the series @(A, Alen@) and @(B, Blen)@
-- assuming @Alen, Blen \<= n@. We assume the bottom coefficient of @B@ is
-- invertible.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_div_series"
  _fq_zech_poly_div_series :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_zech_poly_div_series/ /Q/ /A/ /B/ /n/ /ctx/ 
--
-- Set \(Q\) to the quotient of the series \(A\) by \(B\), thinking of the
-- series as though they were of length \(n\). We assume that the bottom
-- coefficient of \(B\) is invertible.
foreign import ccall "fq_zech_poly.h fq_zech_poly_div_series"
  fq_zech_poly_div_series :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> CLong -> Ptr CFqCtx -> IO ()

-- Greatest common divisor -----------------------------------------------------

-- | /fq_zech_poly_gcd/ /rop/ /op1/ /op2/ /ctx/ 
--
-- Sets @rop@ to the greatest common divisor of @op1@ and @op2@, using the
-- either the Euclidean or HGCD algorithm. The GCD of zero polynomials is
-- defined to be zero, whereas the GCD of the zero polynomial and some
-- other polynomial \(P\) is defined to be \(P\). Except in the case where
-- the GCD is zero, the GCD \(G\) is made monic.
foreign import ccall "fq_zech_poly.h fq_zech_poly_gcd"
  fq_zech_poly_gcd :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_gcd/ /G/ /A/ /lenA/ /B/ /lenB/ /ctx/ 
--
-- Computes the GCD of \(A\) of length @lenA@ and \(B\) of length @lenB@,
-- where @lenA >= lenB > 0@ and sets \(G\) to it. The length of the GCD
-- \(G\) is returned by the function. No attempt is made to make the GCD
-- monic. It is required that \(G\) have space for @lenB@ coefficients.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_gcd"
  _fq_zech_poly_gcd :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO CLong

-- | /_fq_zech_poly_gcd_euclidean_f/ /f/ /G/ /A/ /lenA/ /B/ /lenB/ /ctx/ 
--
-- Either sets \(f = 1\) and \(G\) to the greatest common divisor of
-- \((A,\operatorname{len}(A))\) and \((B, \operatorname{len}(B))\) and
-- returns its length, or sets \(f\) to a non-trivial factor of the modulus
-- of @ctx@ and leaves the contents of the vector \((G, lenB)\) undefined.
-- 
-- Assumes that \(\operatorname{len}(A) \geq \operatorname{len}(B) > 0\)
-- and that the vector \(G\) has space for sufficiently many coefficients.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_gcd_euclidean_f"
  _fq_zech_poly_gcd_euclidean_f :: Ptr CFqZech -> Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO CLong

-- | /fq_zech_poly_gcd_euclidean_f/ /f/ /G/ /A/ /B/ /ctx/ 
--
-- Either sets \(f = 1\) and \(G\) to the greatest common divisor of \(A\)
-- and \(B\) or sets \(f\) to a factor of the modulus of @ctx@.
foreign import ccall "fq_zech_poly.h fq_zech_poly_gcd_euclidean_f"
  fq_zech_poly_gcd_euclidean_f :: Ptr CFqZech -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_xgcd/ /G/ /S/ /T/ /A/ /lenA/ /B/ /lenB/ /invB/ /ctx/ 
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
foreign import ccall "fq_zech_poly.h _fq_zech_poly_xgcd"
  _fq_zech_poly_xgcd :: Ptr CFqZech -> Ptr CFqZech -> Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZech -> CLong -> Ptr CFmpz -> Ptr CFqZechCtx -> IO CLong

-- | /fq_zech_poly_xgcd/ /G/ /S/ /T/ /A/ /B/ /ctx/ 
--
-- Computes the GCD of \(A\) and \(B\). The GCD of zero polynomials is
-- defined to be zero, whereas the GCD of the zero polynomial and some
-- other polynomial \(P\) is defined to be \(P\). Except in the case where
-- the GCD is zero, the GCD \(G\) is made monic.
-- 
-- Polynomials @S@ and @T@ are computed such that @S*A + T*B = G@. The
-- length of @S@ will be at most @lenB@ and the length of @T@ will be at
-- most @lenA@.
foreign import ccall "fq_zech_poly.h fq_zech_poly_xgcd"
  fq_zech_poly_xgcd :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_xgcd_euclidean_f/ /f/ /G/ /S/ /T/ /A/ /lenA/ /B/ /lenB/ /invB/ /ctx/ 
--
-- Either sets \(f = 1\) and computes the GCD of \(A\) and \(B\) together
-- with cofactors \(S\) and \(T\) such that \(S A + T B = G\); otherwise,
-- sets \(f\) to a non-trivial factor of the modulus of @ctx@ and leaves
-- \(G\), \(S\), and \(T\) undefined. Returns the length of \(G\).
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
foreign import ccall "fq_zech_poly.h _fq_zech_poly_xgcd_euclidean_f"
  _fq_zech_poly_xgcd_euclidean_f :: Ptr CFqZech -> Ptr CFqZech -> Ptr CFqZech -> Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZech -> CLong -> Ptr CFmpz -> Ptr CFqZechCtx -> IO CLong

-- | /fq_zech_poly_xgcd_euclidean_f/ /f/ /G/ /S/ /T/ /A/ /B/ /ctx/ 
--
-- Either sets \(f = 1\) and computes the GCD of \(A\) and \(B\) or sets
-- \(f\) to a non-trivial factor of the modulus of @ctx@.
-- 
-- If the GCD is computed, polynomials @S@ and @T@ are computed such that
-- @S*A + T*B = G@; otherwise, they are undefined. The length of @S@ will
-- be at most @lenB@ and the length of @T@ will be at most @lenA@.
-- 
-- The GCD of zero polynomials is defined to be zero, whereas the GCD of
-- the zero polynomial and some other polynomial \(P\) is defined to be
-- \(P\). Except in the case where the GCD is zero, the GCD \(G\) is made
-- monic.
foreign import ccall "fq_zech_poly.h fq_zech_poly_xgcd_euclidean_f"
  fq_zech_poly_xgcd_euclidean_f :: Ptr CFqZech -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- Divisibility testing --------------------------------------------------------

-- | /_fq_zech_poly_divides/ /Q/ /A/ /lenA/ /B/ /lenB/ /invB/ /ctx/ 
--
-- Returns \(1\) if @(B, lenB)@ divides @(A, lenA)@ exactly and sets \(Q\)
-- to the quotient, otherwise returns \(0\).
-- 
-- It is assumed that
-- \(\operatorname{len}(A) \geq \operatorname{len}(B) > 0\) and that \(Q\)
-- has space for \(\operatorname{len}(A) - \operatorname{len}(B) + 1\)
-- coefficients.
-- 
-- Aliasing of \(Q\) with either of the inputs is not permitted.
-- 
-- This function is currently unoptimised and provided for convenience
-- only.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_divides"
  _fq_zech_poly_divides :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZech -> CLong -> Ptr CFqZech -> Ptr CFqZechCtx -> IO CInt

-- | /fq_zech_poly_divides/ /Q/ /A/ /B/ /ctx/ 
--
-- Returns \(1\) if \(B\) divides \(A\) exactly and sets \(Q\) to the
-- quotient, otherwise returns \(0\).
-- 
-- This function is currently unoptimised and provided for convenience
-- only.
foreign import ccall "fq_zech_poly.h fq_zech_poly_divides"
  fq_zech_poly_divides :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO CInt

-- Derivative ------------------------------------------------------------------

-- | /_fq_zech_poly_derivative/ /rop/ /op/ /len/ /ctx/ 
--
-- Sets @(rop, len - 1)@ to the derivative of @(op, len)@. Also handles the
-- cases where @len@ is \(0\) or \(1\) correctly. Supports aliasing of
-- @rop@ and @op@.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_derivative"
  _fq_zech_poly_derivative :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_derivative/ /rop/ /op/ /ctx/ 
--
-- Sets @rop@ to the derivative of @op@.
foreign import ccall "fq_zech_poly.h fq_zech_poly_derivative"
  fq_zech_poly_derivative :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- Square root -----------------------------------------------------------------

-- | /_fq_zech_poly_invsqrt_series/ /g/ /h/ /n/ /mod/ 
--
-- Set the first \(n\) terms of \(g\) to the series expansion of
-- \(1/\sqrt{h}\). It is assumed that \(n > 0\), that \(h\) has constant
-- term 1 and that \(h\) is zero-padded as necessary to length \(n\).
-- Aliasing is not permitted.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_invsqrt_series"
  _fq_zech_poly_invsqrt_series :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_invsqrt_series/ /g/ /h/ /n/ /ctx/ 
--
-- Set \(g\) to the series expansion of \(1/\sqrt{h}\) to order \(O(x^n)\).
-- It is assumed that \(h\) has constant term 1.
foreign import ccall "fq_zech_poly.h fq_zech_poly_invsqrt_series"
  fq_zech_poly_invsqrt_series :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_sqrt_series/ /g/ /h/ /n/ /ctx/ 
--
-- Set the first \(n\) terms of \(g\) to the series expansion of
-- \(\sqrt{h}\). It is assumed that \(n > 0\), that \(h\) has constant term
-- 1 and that \(h\) is zero-padded as necessary to length \(n\). Aliasing
-- is not permitted.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_sqrt_series"
  _fq_zech_poly_sqrt_series :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_sqrt_series/ /g/ /h/ /n/ /ctx/ 
--
-- Set \(g\) to the series expansion of \(\sqrt{h}\) to order \(O(x^n)\).
-- It is assumed that \(h\) has constant term 1.
foreign import ccall "fq_zech_poly.h fq_zech_poly_sqrt_series"
  fq_zech_poly_sqrt_series :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_sqrt/ /s/ /p/ /n/ /mod/ 
--
-- If @(p, n)@ is a perfect square, sets @(s, n \/ 2 + 1)@ to a square root
-- of \(p\) and returns 1. Otherwise returns 0.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_sqrt"
  _fq_zech_poly_sqrt :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO CInt

-- | /fq_zech_poly_sqrt/ /s/ /p/ /mod/ 
--
-- If \(p\) is a perfect square, sets \(s\) to a square root of \(p\) and
-- returns 1. Otherwise returns 0.
foreign import ccall "fq_zech_poly.h fq_zech_poly_sqrt"
  fq_zech_poly_sqrt :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO CInt

-- Evaluation ------------------------------------------------------------------

-- | /_fq_zech_poly_evaluate_fq_zech/ /rop/ /op/ /len/ /a/ /ctx/ 
--
-- Sets @rop@ to @(op, len)@ evaluated at \(a\).
-- 
-- Supports zero padding. There are no restrictions on @len@, that is,
-- @len@ is allowed to be zero, too.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_evaluate_fq_zech"
  _fq_zech_poly_evaluate_fq_zech :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_evaluate_fq_zech/ /rop/ /f/ /a/ /ctx/ 
--
-- Sets @rop@ to the value of \(f(a)\).
-- 
-- As the coefficient ring \(\mathbf{F}_q\) is finite, Horner\'s method is
-- sufficient.
foreign import ccall "fq_zech_poly.h fq_zech_poly_evaluate_fq_zech"
  fq_zech_poly_evaluate_fq_zech :: Ptr CFqZech -> Ptr CFqZechPoly -> Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- Composition -----------------------------------------------------------------

-- | /_fq_zech_poly_compose/ /rop/ /op1/ /len1/ /op2/ /len2/ /ctx/ 
--
-- Sets @rop@ to the composition of @(op1, len1)@ and @(op2, len2)@.
-- 
-- Assumes that @rop@ has space for @(len1-1)*(len2-1) + 1@ coefficients.
-- Assumes that @op1@ and @op2@ are non-zero polynomials. Does not support
-- aliasing between any of the inputs and the output.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_compose"
  _fq_zech_poly_compose :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_compose/ /rop/ /op1/ /op2/ /ctx/ 
--
-- Sets @rop@ to the composition of @op1@ and @op2@. To be precise about
-- the order of composition, denoting @rop@, @op1@, and @op2@ by \(f\),
-- \(g\), and \(h\), respectively, sets \(f(t) = g(h(t))\).
foreign import ccall "fq_zech_poly.h fq_zech_poly_compose"
  fq_zech_poly_compose :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_compose_mod_horner/ /res/ /f/ /lenf/ /g/ /h/ /lenh/ /ctx/ 
--
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero and that the length of \(g\) is one less than the
-- length of \(h\) (possibly with zero padding). The output is not allowed
-- to be aliased with any of the inputs.
-- 
-- The algorithm used is Horner\'s rule.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_compose_mod_horner"
  _fq_zech_poly_compose_mod_horner :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_compose_mod_horner/ /res/ /f/ /g/ /h/ /ctx/ 
--
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero. The algorithm used is Horner\'s rule.
foreign import ccall "fq_zech_poly.h fq_zech_poly_compose_mod_horner"
  fq_zech_poly_compose_mod_horner :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_compose_mod_horner_preinv/ /res/ /f/ /lenf/ /g/ /h/ /lenh/ /hinv/ /lenhiv/ /ctx/ 
--
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero and that the length of \(g\) is one less than the
-- length of \(h\) (possibly with zero padding). We also require that the
-- length of \(f\) is less than the length of \(h\). Furthermore, we
-- require @hinv@ to be the inverse of the reverse of @h@. The output is
-- not allowed to be aliased with any of the inputs.
-- 
-- The algorithm used is Horner\'s rule.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_compose_mod_horner_preinv"
  _fq_zech_poly_compose_mod_horner_preinv :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_compose_mod_horner_preinv/ /res/ /f/ /g/ /h/ /hinv/ /ctx/ 
--
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero and that \(f\) has smaller degree than \(h\).
-- Furthermore, we require @hinv@ to be the inverse of the reverse of @h@.
-- The algorithm used is Horner\'s rule.
foreign import ccall "fq_zech_poly.h fq_zech_poly_compose_mod_horner_preinv"
  fq_zech_poly_compose_mod_horner_preinv :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_compose_mod_brent_kung/ /res/ /f/ /lenf/ /g/ /h/ /lenh/ /ctx/ 
--
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero and that the length of \(g\) is one less than the
-- length of \(h\) (possibly with zero padding). We also require that the
-- length of \(f\) is less than the length of \(h\). The output is not
-- allowed to be aliased with any of the inputs.
-- 
-- The algorithm used is the Brent-Kung matrix algorithm.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_compose_mod_brent_kung"
  _fq_zech_poly_compose_mod_brent_kung :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_compose_mod_brent_kung/ /res/ /f/ /g/ /h/ /ctx/ 
--
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero and that \(f\) has smaller degree than \(h\). The
-- algorithm used is the Brent-Kung matrix algorithm.
foreign import ccall "fq_zech_poly.h fq_zech_poly_compose_mod_brent_kung"
  fq_zech_poly_compose_mod_brent_kung :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_compose_mod_brent_kung_preinv/ /res/ /f/ /lenf/ /g/ /h/ /lenh/ /hinv/ /lenhiv/ /ctx/ 
--
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero and that the length of \(g\) is one less than the
-- length of \(h\) (possibly with zero padding). We also require that the
-- length of \(f\) is less than the length of \(h\). Furthermore, we
-- require @hinv@ to be the inverse of the reverse of @h@. The output is
-- not allowed to be aliased with any of the inputs.
-- 
-- The algorithm used is the Brent-Kung matrix algorithm.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_compose_mod_brent_kung_preinv"
  _fq_zech_poly_compose_mod_brent_kung_preinv :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_compose_mod_brent_kung_preinv/ /res/ /f/ /g/ /h/ /hinv/ /ctx/ 
--
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero and that \(f\) has smaller degree than \(h\).
-- Furthermore, we require @hinv@ to be the inverse of the reverse of @h@.
-- The algorithm used is the Brent-Kung matrix algorithm.
foreign import ccall "fq_zech_poly.h fq_zech_poly_compose_mod_brent_kung_preinv"
  fq_zech_poly_compose_mod_brent_kung_preinv :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_compose_mod/ /res/ /f/ /lenf/ /g/ /h/ /lenh/ /ctx/ 
--
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero and that the length of \(g\) is one less than the
-- length of \(h\) (possibly with zero padding). The output is not allowed
-- to be aliased with any of the inputs.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_compose_mod"
  _fq_zech_poly_compose_mod :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_compose_mod/ /res/ /f/ /g/ /h/ /ctx/ 
--
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero.
foreign import ccall "fq_zech_poly.h fq_zech_poly_compose_mod"
  fq_zech_poly_compose_mod :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_compose_mod_preinv/ /res/ /f/ /lenf/ /g/ /h/ /lenh/ /hinv/ /lenhiv/ /ctx/ 
--
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero and that the length of \(g\) is one less than the
-- length of \(h\) (possibly with zero padding). We also require that the
-- length of \(f\) is less than the length of \(h\). Furthermore, we
-- require @hinv@ to be the inverse of the reverse of @h@. The output is
-- not allowed to be aliased with any of the inputs.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_compose_mod_preinv"
  _fq_zech_poly_compose_mod_preinv :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_compose_mod_preinv/ /res/ /f/ /g/ /h/ /hinv/ /ctx/ 
--
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero and that \(f\) has smaller degree than \(h\).
-- Furthermore, we require @hinv@ to be the inverse of the reverse of @h@.
foreign import ccall "fq_zech_poly.h fq_zech_poly_compose_mod_preinv"
  fq_zech_poly_compose_mod_preinv :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_reduce_matrix_mod_poly/ /A/ /B/ /f/ /ctx/ 
--
-- Sets the ith row of @A@ to the reduction of the ith row of \(B\) modulo
-- \(f\) for \(i=1,\ldots,\sqrt{\deg(f)}\). We require \(B\) to be at least
-- a \(\sqrt{\deg(f)}\times \deg(f)\) matrix and \(f\) to be nonzero.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_reduce_matrix_mod_poly"
  _fq_zech_poly_reduce_matrix_mod_poly :: Ptr CFqZechMat -> Ptr CFqZechMat -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_precompute_matrix/ /A/ /f/ /g/ /leng/ /ginv/ /lenginv/ /ctx/ 
--
-- Sets the ith row of @A@ to \(f^i\) modulo \(g\) for
-- \(i=1,\ldots,\sqrt{\deg(g)}\). We require \(A\) to be a
-- \(\sqrt{\deg(g)}\times \deg(g)\) matrix. We require @ginv@ to be the
-- inverse of the reverse of @g@ and \(g\) to be nonzero.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_precompute_matrix"
  _fq_zech_poly_precompute_matrix :: Ptr CFqZechMat -> Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_precompute_matrix/ /A/ /f/ /g/ /ginv/ /ctx/ 
--
-- Sets the ith row of @A@ to \(f^i\) modulo \(g\) for
-- \(i=1,\ldots,\sqrt{\deg(g)}\). We require \(A\) to be a
-- \(\sqrt{\deg(g)}\times \deg(g)\) matrix. We require @ginv@ to be the
-- inverse of the reverse of @g@.
foreign import ccall "fq_zech_poly.h fq_zech_poly_precompute_matrix"
  fq_zech_poly_precompute_matrix :: Ptr CFqZechMat -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- | /_fq_zech_poly_compose_mod_brent_kung_precomp_preinv/ /res/ /f/ /lenf/ /A/ /h/ /lenh/ /hinv/ /lenhinv/ /ctx/ 
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
foreign import ccall "fq_zech_poly.h _fq_zech_poly_compose_mod_brent_kung_precomp_preinv"
  _fq_zech_poly_compose_mod_brent_kung_precomp_preinv :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZechMat -> Ptr CFqZech -> CLong -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_compose_mod_brent_kung_precomp_preinv/ /res/ /f/ /A/ /h/ /hinv/ /ctx/ 
--
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that the
-- ith row of \(A\) contains \(g^i\) for \(i=1,\ldots,\sqrt{\deg(h)}\),
-- i.e. \(A\) is a \(\sqrt{\deg(h)}\times
-- \deg(h)\) matrix. We require that \(h\) is nonzero and that \(f\) has
-- smaller degree than \(h\). Furthermore, we require @hinv@ to be the
-- inverse of the reverse of @h@. This version of Brent-Kung modular
-- composition is particularly useful if one has to perform several modular
-- composition of the form \(f(g)\) modulo \(h\) for fixed \(g\) and \(h\).
foreign import ccall "fq_zech_poly.h fq_zech_poly_compose_mod_brent_kung_precomp_preinv"
  fq_zech_poly_compose_mod_brent_kung_precomp_preinv :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechMat -> Ptr CFqZechPoly -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO ()

-- Output ----------------------------------------------------------------------

-- | /_fq_zech_poly_fprint_pretty/ /file/ /poly/ /len/ /x/ /ctx/ 
--
-- Prints the pretty representation of @(poly, len)@ to the stream @file@,
-- using the string @x@ to represent the indeterminate.
-- 
-- In case of success, returns a positive value. In case of failure,
-- returns a non-positive value.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_fprint_pretty"
  _fq_zech_poly_fprint_pretty :: Ptr CFile -> Ptr CFqZech -> CLong -> CString -> Ptr CFqZechCtx -> IO CInt

-- | /fq_zech_poly_fprint_pretty/ /file/ /poly/ /x/ /ctx/ 
--
-- Prints the pretty representation of @poly@ to the stream @file@, using
-- the string @x@ to represent the indeterminate.
-- 
-- In case of success, returns a positive value. In case of failure,
-- returns a non-positive value.
foreign import ccall "fq_zech_poly.h fq_zech_poly_fprint_pretty"
  fq_zech_poly_fprint_pretty :: Ptr CFile -> Ptr CFqZechPoly -> CString -> Ptr CFqZechCtx -> IO CInt

-- | /_fq_zech_poly_print_pretty/ /poly/ /len/ /x/ /ctx/ 
--
-- Prints the pretty representation of @(poly, len)@ to @stdout@, using the
-- string @x@ to represent the indeterminate.
-- 
-- In case of success, returns a positive value. In case of failure,
-- returns a non-positive value.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_print_pretty"
  _fq_zech_poly_print_pretty :: Ptr CFqZech -> CLong -> CString -> Ptr CFqZechCtx -> IO CInt

-- | /fq_zech_poly_print_pretty/ /poly/ /x/ /ctx/ 
--
-- Prints the pretty representation of @poly@ to @stdout@, using the string
-- @x@ to represent the indeterminate.
-- 
-- In case of success, returns a positive value. In case of failure,
-- returns a non-positive value.
fq_zech_poly_print_pretty :: Ptr CFqZechPoly -> CString -> Ptr CFqZechCtx -> IO CInt
fq_zech_poly_print_pretty poly x ctx = do
  printCStr (\poly -> fq_zech_poly_get_str_pretty poly x ctx) poly


-- | /_fq_zech_poly_fprint/ /file/ /poly/ /len/ /ctx/ 
--
-- Prints the pretty representation of @(poly, len)@ to the stream @file@.
-- 
-- In case of success, returns a positive value. In case of failure,
-- returns a non-positive value.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_fprint"
  _fq_zech_poly_fprint :: Ptr CFile -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO CInt

-- | /fq_zech_poly_fprint/ /file/ /poly/ /ctx/ 
--
-- Prints the pretty representation of @poly@ to the stream @file@.
-- 
-- In case of success, returns a positive value. In case of failure,
-- returns a non-positive value.
foreign import ccall "fq_zech_poly.h fq_zech_poly_fprint"
  fq_zech_poly_fprint :: Ptr CFile -> Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO CInt

-- | /_fq_zech_poly_print/ /poly/ /len/ /ctx/ 
--
-- Prints the pretty representation of @(poly, len)@ to @stdout@.
-- 
-- In case of success, returns a positive value. In case of failure,
-- returns a non-positive value.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_print"
  _fq_zech_poly_print :: Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO CInt

-- | /fq_zech_poly_print/ /poly/ /ctx/ 
--
-- Prints the representation of @poly@ to @stdout@.
-- 
-- In case of success, returns a positive value. In case of failure,
-- returns a non-positive value.
fq_zech_poly_print :: Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO CInt
fq_zech_poly_print poly ctx = do
  printCStr (\poly -> fq_zech_poly_get_str poly ctx) poly
  
-- | /_fq_zech_poly_get_str/ /poly/ /len/ /ctx/ 
--
-- Returns the plain FLINT string representation of the polynomial
-- @(poly, len)@.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_get_str"
  _fq_zech_poly_get_str :: Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO CString

-- | /fq_zech_poly_get_str/ /poly/ /ctx/ 
--
-- Returns the plain FLINT string representation of the polynomial @poly@.
foreign import ccall "fq_zech_poly.h fq_zech_poly_get_str"
  fq_zech_poly_get_str :: Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO CString

-- | /_fq_zech_poly_get_str_pretty/ /poly/ /len/ /x/ /ctx/ 
--
-- Returns a pretty representation of the polynomial @(poly, len)@ using
-- the null-terminated string @x@ as the variable name.
foreign import ccall "fq_zech_poly.h _fq_zech_poly_get_str_pretty"
  _fq_zech_poly_get_str_pretty :: Ptr CFqZech -> CLong -> CString -> Ptr CFqZechCtx -> IO CString

-- | /fq_zech_poly_get_str_pretty/ /poly/ /x/ /ctx/ 
--
-- Returns a pretty representation of the polynomial @poly@ using the
-- null-terminated string @x@ as the variable name
foreign import ccall "fq_zech_poly.h fq_zech_poly_get_str_pretty"
  fq_zech_poly_get_str_pretty :: Ptr CFqZechPoly -> CString -> Ptr CFqZechCtx -> IO CString

-- Inflation and deflation -----------------------------------------------------

-- | /fq_zech_poly_inflate/ /result/ /input/ /inflation/ /ctx/ 
--
-- Sets @result@ to the inflated polynomial \(p(x^n)\) where \(p\) is given
-- by @input@ and \(n\) is given by @inflation@.
foreign import ccall "fq_zech_poly.h fq_zech_poly_inflate"
  fq_zech_poly_inflate :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> CULong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_deflate/ /result/ /input/ /deflation/ /ctx/ 
--
-- Sets @result@ to the deflated polynomial \(p(x^{1/n})\) where \(p\) is
-- given by @input@ and \(n\) is given by @deflation@. Requires \(n > 0\).
foreign import ccall "fq_zech_poly.h fq_zech_poly_deflate"
  fq_zech_poly_deflate :: Ptr CFqZechPoly -> Ptr CFqZechPoly -> CULong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_poly_deflation/ /input/ /ctx/ 
--
-- Returns the largest integer by which @input@ can be deflated. As special
-- cases, returns 0 if @input@ is the zero polynomial and 1 of @input@ is a
-- constant polynomial.
foreign import ccall "fq_zech_poly.h fq_zech_poly_deflation"
  fq_zech_poly_deflation :: Ptr CFqZechPoly -> Ptr CFqZechCtx -> IO CULong

