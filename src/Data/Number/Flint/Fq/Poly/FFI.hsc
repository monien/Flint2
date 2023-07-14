module Data.Number.Flint.Fq.Poly.FFI (
  -- * Univariate polynomials over finite fields
  -- * Types
    FqPoly (..)
  , CFqPoly (..)
  , newFqPoly
  , withFqPoly
  , withNewFqPoly
  -- * Memory management
  , fq_poly_init
  , fq_poly_init2
  , fq_poly_realloc
  , fq_poly_fit_length
  , _fq_poly_set_length
  , fq_poly_clear
  , _fq_poly_normalise
  , _fq_poly_normalise2
  , fq_poly_truncate
  , fq_poly_set_trunc
  , _fq_poly_reverse
  , fq_poly_reverse
  -- * Polynomial parameters
  , fq_poly_degree
  , fq_poly_length
  , fq_poly_lead
  -- * Randomisation
  , fq_poly_randtest
  , fq_poly_randtest_not_zero
  , fq_poly_randtest_monic
  , fq_poly_randtest_irreducible
  -- * Assignment and basic manipulation
  , _fq_poly_set
  , fq_poly_set
  , fq_poly_set_fq
  , fq_poly_set_fmpz_mod_poly
  , fq_poly_set_nmod_poly
  , fq_poly_swap
  , _fq_poly_zero
  , fq_poly_zero
  , fq_poly_one
  , fq_poly_gen
  , fq_poly_make_monic
  , _fq_poly_make_monic
  -- * Getting and setting coefficients
  , fq_poly_get_coeff
  , fq_poly_set_coeff
  , fq_poly_set_coeff_fmpz
  -- * Comparison
  , fq_poly_equal
  , fq_poly_equal_trunc
  , fq_poly_is_zero
  , fq_poly_is_one
  , fq_poly_is_gen
  , fq_poly_is_unit
  , fq_poly_equal_fq
  -- * Addition and subtraction
  , _fq_poly_add
  , fq_poly_add
  , fq_poly_add_si
  , fq_poly_add_series
  , _fq_poly_sub
  , fq_poly_sub
  , fq_poly_sub_series
  , _fq_poly_neg
  , fq_poly_neg
  -- * Scalar multiplication and division
  , _fq_poly_scalar_mul_fq
  , fq_poly_scalar_mul_fq
  , _fq_poly_scalar_addmul_fq
  , fq_poly_scalar_addmul_fq
  , _fq_poly_scalar_submul_fq
  , fq_poly_scalar_submul_fq
  , _fq_poly_scalar_div_fq
  , fq_poly_scalar_div_fq
  -- * Multiplication
  , _fq_poly_mul_classical
  , fq_poly_mul_classical
  , _fq_poly_mul_reorder
  , fq_poly_mul_reorder
  , _fq_poly_mul_univariate
  , fq_poly_mul_univariate
  , _fq_poly_mul_KS
  , fq_poly_mul_KS
  , _fq_poly_mul
  , fq_poly_mul
  , _fq_poly_mullow_classical
  , fq_poly_mullow_classical
  , _fq_poly_mullow_univariate
  , fq_poly_mullow_univariate
  , _fq_poly_mullow_KS
  , fq_poly_mullow_KS
  , _fq_poly_mullow
  , fq_poly_mullow
  , _fq_poly_mulhigh_classical
  , fq_poly_mulhigh_classical
  , _fq_poly_mulhigh
  , fq_poly_mulhigh
  , _fq_poly_mulmod
  , fq_poly_mulmod
  , _fq_poly_mulmod_preinv
  , fq_poly_mulmod_preinv
  -- * Squaring
  , _fq_poly_sqr_classical
  , fq_poly_sqr_classical
  , _fq_poly_sqr_reorder
  , fq_poly_sqr_reorder
  , _fq_poly_sqr_KS
  , fq_poly_sqr_KS
  , _fq_poly_sqr
  , fq_poly_sqr
  -- * Powering
  , _fq_poly_pow
  , fq_poly_pow
  , _fq_poly_powmod_ui_binexp
  , fq_poly_powmod_ui_binexp
  , _fq_poly_powmod_ui_binexp_preinv
  , fq_poly_powmod_ui_binexp_preinv
  , _fq_poly_powmod_fmpz_binexp
  , fq_poly_powmod_fmpz_binexp
  , _fq_poly_powmod_fmpz_binexp_preinv
  , fq_poly_powmod_fmpz_binexp_preinv
  , _fq_poly_powmod_fmpz_sliding_preinv
  , fq_poly_powmod_fmpz_sliding_preinv
  , _fq_poly_powmod_x_fmpz_preinv
  , fq_poly_powmod_x_fmpz_preinv
  , _fq_poly_pow_trunc_binexp
  , fq_poly_pow_trunc_binexp
  , _fq_poly_pow_trunc
  , fq_poly_pow_trunc
  -- * Shifting
  , _fq_poly_shift_left
  , fq_poly_shift_left
  , _fq_poly_shift_right
  , fq_poly_shift_right
  -- * Norms
  , fq_poly_hamming_weight
  -- * Euclidean division
  , _fq_poly_divrem
  , fq_poly_divrem
  , fq_poly_divrem_f
  , _fq_poly_rem
  , fq_poly_rem
  , _fq_poly_div
  , fq_poly_div
  , _fq_poly_div_newton_n_preinv
  , fq_poly_div_newton_n_preinv
  , _fq_poly_divrem_newton_n_preinv
  --, fq_poly_divrem_newton_preinv
  , _fq_poly_inv_series_newton
  , fq_poly_inv_series_newton
  , _fq_poly_inv_series
  , fq_poly_inv_series
  , _fq_poly_div_series
  , fq_poly_div_series
  -- * Greatest common divisor
  , fq_poly_gcd
  , _fq_poly_gcd
  , _fq_poly_gcd_euclidean_f
  , fq_poly_gcd_euclidean_f
  , _fq_poly_xgcd
  , fq_poly_xgcd
  , _fq_poly_xgcd_euclidean_f
  , fq_poly_xgcd_euclidean_f
  -- * Divisibility testing
  , _fq_poly_divides
  , fq_poly_divides
  -- * Derivative
  , _fq_poly_derivative
  , fq_poly_derivative
  -- * Square root
  , _fq_poly_invsqrt_series
  , fq_poly_invsqrt_series
  , _fq_poly_sqrt_series
  , fq_poly_sqrt_series
  , _fq_poly_sqrt
  , fq_poly_sqrt
  -- * Evaluation
  , _fq_poly_evaluate_fq
  , fq_poly_evaluate_fq
  -- * Composition
  , _fq_poly_compose
  , fq_poly_compose
  , _fq_poly_compose_mod_horner
  , fq_poly_compose_mod_horner
  , _fq_poly_compose_mod_horner_preinv
  , fq_poly_compose_mod_horner_preinv
  , _fq_poly_compose_mod_brent_kung
  , fq_poly_compose_mod_brent_kung
  , _fq_poly_compose_mod_brent_kung_preinv
  , fq_poly_compose_mod_brent_kung_preinv
  , _fq_poly_compose_mod
  , fq_poly_compose_mod
  , _fq_poly_compose_mod_preinv
  , fq_poly_compose_mod_preinv
  , _fq_poly_reduce_matrix_mod_poly
  , _fq_poly_precompute_matrix
  , fq_poly_precompute_matrix
  , _fq_poly_compose_mod_brent_kung_precomp_preinv
  , fq_poly_compose_mod_brent_kung_precomp_preinv
  -- * Output
  , _fq_poly_fprint_pretty
  , fq_poly_fprint_pretty
  , _fq_poly_print_pretty
  , fq_poly_print_pretty
  , _fq_poly_fprint
  , fq_poly_fprint
  , _fq_poly_print
  , fq_poly_print
  , _fq_poly_get_str
  , fq_poly_get_str
  , _fq_poly_get_str_pretty
  , fq_poly_get_str_pretty
  -- * Inflation and deflation
  , fq_poly_inflate
  , fq_poly_deflate
  , fq_poly_deflation
) where

-- Univariate polynomials over finite fields -----------------------------------

import System.IO.Unsafe
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
import Data.Number.Flint.Fmpz.Mod.Poly

import Data.Number.Flint.Fmpq

import Data.Number.Flint.NMod.Types

import Data.Number.Flint.Fq
import Data.Number.Flint.Fq.Mat

#include <flint/flint.h>
#include <flint/fq_poly.h>

-- fq_poly_t -------------------------------------------------------------------

data FqPoly = FqPoly {-# UNPACK #-} !(ForeignPtr CFqPoly)
data CFqPoly = CFqPoly (Ptr CFq) CLong CLong

-- data CFqPoly = CFqPoly {
--   -- | pointer to the coefficients of the polynomial
--   coeffs :: Ptr CFq,
--   -- | number of allocated coefficients
--   alloc :: CLong,
--   -- | number of coefficients
--   num :: CLong
--   }

instance Storable CFqPoly where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fq_poly_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fq_poly_t}
  peek ptr = CFqPoly
    <$> #{peek fq_poly_struct, coeffs} ptr
    <*> #{peek fq_poly_struct, alloc } ptr
    <*> #{peek fq_poly_struct, length} ptr
  poke = undefined
     
-- | Create a new `FqPoly` structure with context `ctx`.
newFqPoly ctx@(FqCtx fctx) = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> do
    withFqCtx ctx $ \ctx -> do
      fq_poly_init x ctx
    addForeignPtrFinalizerEnv p_fq_poly_clear x fctx
  return $ FqPoly x

-- | Use `FqPoly` structure.
{-# INLINE withFqPoly #-}
withFqPoly (FqPoly x) f = do
  withForeignPtr x $ \px -> f px >>= return . (FqPoly x,)

-- | Use new `FqPoly` structure.
{-# INLINE withNewFqPoly #-}
withNewFqPoly ctx f = do
  x <- newFqPoly ctx
  withFqPoly x $ \x -> f x

-- Memory management -----------------------------------------------------------

-- | /fq_poly_init/ /poly/ /ctx/ 
--
-- Initialises @poly@ for use, with context ctx, and setting its length to
-- zero. A corresponding call to @fq_poly_clear@ must be made after
-- finishing with the @fq_poly_t@ to free the memory used by the
-- polynomial.
foreign import ccall "fq_poly.h fq_poly_init"
  fq_poly_init :: Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /fq_poly_init2/ /poly/ /alloc/ /ctx/ 
--
-- Initialises @poly@ with space for at least @alloc@ coefficients and sets
-- the length to zero. The allocated coefficients are all set to zero. A
-- corresponding call to @fq_poly_clear@ must be made after finishing with
-- the @fq_poly_t@ to free the memory used by the polynomial.
foreign import ccall "fq_poly.h fq_poly_init2"
  fq_poly_init2 :: Ptr CFqPoly -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_realloc/ /poly/ /alloc/ /ctx/ 
--
-- Reallocates the given polynomial to have space for @alloc@ coefficients.
-- If @alloc@ is zero the polynomial is cleared and then reinitialised. If
-- the current length is greater than @alloc@ the polynomial is first
-- truncated to length @alloc@.
foreign import ccall "fq_poly.h fq_poly_realloc"
  fq_poly_realloc :: Ptr CFqPoly -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_fit_length/ /poly/ /len/ /ctx/ 
--
-- If @len@ is greater than the number of coefficients currently allocated,
-- then the polynomial is reallocated to have space for at least @len@
-- coefficients. No data is lost when calling this function.
-- 
-- The function efficiently deals with the case where @fit_length@ is
-- called many times in small increments by at least doubling the number of
-- allocated coefficients when length is larger than the number of
-- coefficients currently allocated.
foreign import ccall "fq_poly.h fq_poly_fit_length"
  fq_poly_fit_length :: Ptr CFqPoly -> CLong -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_set_length/ /poly/ /newlen/ /ctx/ 
--
-- Sets the coefficients of @poly@ beyond @len@ to zero and sets the length
-- of @poly@ to @len@.
foreign import ccall "fq_poly.h _fq_poly_set_length"
  _fq_poly_set_length :: Ptr CFqPoly -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_clear/ /poly/ /ctx/ 
--
-- Clears the given polynomial, releasing any memory used. It must be
-- reinitialised in order to be used again.
foreign import ccall "fq_poly.h fq_poly_clear"
  fq_poly_clear :: Ptr CFqPoly -> Ptr CFqCtx -> IO ()

foreign import ccall "fq_poly.h &fq_poly_clear"
  p_fq_poly_clear :: FunPtr (Ptr CFqPoly -> Ptr CFqCtx -> IO ())

-- | /_fq_poly_normalise/ /poly/ /ctx/ 
--
-- Sets the length of @poly@ so that the top coefficient is non-zero. If
-- all coefficients are zero, the length is set to zero. This function is
-- mainly used internally, as all functions guarantee normalisation.
foreign import ccall "fq_poly.h _fq_poly_normalise"
  _fq_poly_normalise :: Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_normalise2/ /poly/ /length/ /ctx/ 
--
-- Sets the length @length@ of @(poly,length)@ so that the top coefficient
-- is non-zero. If all coefficients are zero, the length is set to zero.
-- This function is mainly used internally, as all functions guarantee
-- normalisation.
foreign import ccall "fq_poly.h _fq_poly_normalise2"
  _fq_poly_normalise2 :: Ptr (Ptr CFq) -> Ptr CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_truncate/ /poly/ /newlen/ /ctx/ 
--
-- Truncates the polynomial to length at most \(n\).
foreign import ccall "fq_poly.h fq_poly_truncate"
  fq_poly_truncate :: Ptr CFqPoly -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_set_trunc/ /poly1/ /poly2/ /newlen/ /ctx/ 
--
-- Sets @poly1@ to @poly2@ truncated to length \(n\).
foreign import ccall "fq_poly.h fq_poly_set_trunc"
  fq_poly_set_trunc :: Ptr CFqPoly -> Ptr CFqPoly -> CLong -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_reverse/ /output/ /input/ /len/ /m/ /ctx/ 
--
-- Sets @output@ to the reverse of @input@, which is of length @len@, but
-- thinking of it as a polynomial of length @m@, notionally zero-padded if
-- necessary. The length @m@ must be non-negative, but there are no other
-- restrictions. The polynomial @output@ must have space for @m@
-- coefficients.
foreign import ccall "fq_poly.h _fq_poly_reverse"
  _fq_poly_reverse :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_reverse/ /output/ /input/ /m/ /ctx/ 
--
-- Sets @output@ to the reverse of @input@, thinking of it as a polynomial
-- of length @m@, notionally zero-padded if necessary). The length @m@ must
-- be non-negative, but there are no other restrictions. The output
-- polynomial will be set to length @m@ and then normalised.
foreign import ccall "fq_poly.h fq_poly_reverse"
  fq_poly_reverse :: Ptr CFqPoly -> Ptr CFqPoly -> CLong -> Ptr CFqCtx -> IO ()

-- Polynomial parameters -------------------------------------------------------

-- | /fq_poly_degree/ /poly/ /ctx/ 
--
-- Returns the degree of the polynomial @poly@.
foreign import ccall "fq_poly.h fq_poly_degree"
  fq_poly_degree :: Ptr CFqPoly -> Ptr CFqCtx -> IO CLong

-- | /fq_poly_length/ /poly/ /ctx/ 
--
-- Returns the length of the polynomial @poly@.
foreign import ccall "fq_poly.h fq_poly_length"
  fq_poly_length :: Ptr CFqPoly -> Ptr CFqCtx -> IO CLong

-- | /fq_poly_lead/ /poly/ /ctx/ 
--
-- Returns a pointer to the leading coefficient of @poly@, or @NULL@ if
-- @poly@ is the zero polynomial.
foreign import ccall "fq_poly.h fq_poly_lead"
  fq_poly_lead :: Ptr CFqPoly -> Ptr CFqCtx -> IO (Ptr (Ptr CFq))

-- Randomisation ---------------------------------------------------------------

-- | /fq_poly_randtest/ /f/ /state/ /len/ /ctx/ 
--
-- Sets \(f\) to a random polynomial of length at most @len@ with entries
-- in the field described by @ctx@.
foreign import ccall "fq_poly.h fq_poly_randtest"
  fq_poly_randtest :: Ptr CFqPoly -> Ptr CFRandState -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_randtest_not_zero/ /f/ /state/ /len/ /ctx/ 
--
-- Same as @fq_poly_randtest@ but guarantees that the polynomial is not
-- zero.
foreign import ccall "fq_poly.h fq_poly_randtest_not_zero"
  fq_poly_randtest_not_zero :: Ptr CFqPoly -> Ptr CFRandState -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_randtest_monic/ /f/ /state/ /len/ /ctx/ 
--
-- Sets \(f\) to a random monic polynomial of length @len@ with entries in
-- the field described by @ctx@.
foreign import ccall "fq_poly.h fq_poly_randtest_monic"
  fq_poly_randtest_monic :: Ptr CFqPoly -> Ptr CFRandState -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_randtest_irreducible/ /f/ /state/ /len/ /ctx/ 
--
-- Sets \(f\) to a random monic, irreducible polynomial of length @len@
-- with entries in the field described by @ctx@.
foreign import ccall "fq_poly.h fq_poly_randtest_irreducible"
  fq_poly_randtest_irreducible :: Ptr CFqPoly -> Ptr CFRandState -> CLong -> Ptr CFqCtx -> IO ()

-- Assignment and basic manipulation -------------------------------------------

-- | /_fq_poly_set/ /rop/ /op/ /len/ /ctx/ 
--
-- Sets @(rop, len@) to @(op, len)@.
foreign import ccall "fq_poly.h _fq_poly_set"
  _fq_poly_set :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_set/ /poly1/ /poly2/ /ctx/ 
--
-- Sets the polynomial @poly1@ to the polynomial @poly2@.
foreign import ccall "fq_poly.h fq_poly_set"
  fq_poly_set :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /fq_poly_set_fq/ /poly/ /c/ /ctx/ 
--
-- Sets the polynomial @poly@ to @c@.
foreign import ccall "fq_poly.h fq_poly_set_fq"
  fq_poly_set_fq :: Ptr CFqPoly -> Ptr CFq -> Ptr CFqCtx -> IO ()

-- | /fq_poly_set_fmpz_mod_poly/ /rop/ /op/ /ctx/ 
--
-- Sets the polynomial @rop@ to the polynomial @op@
foreign import ccall "fq_poly.h fq_poly_set_fmpz_mod_poly"
  fq_poly_set_fmpz_mod_poly :: Ptr CFqPoly -> Ptr CFmpzModPoly -> Ptr CFqCtx -> IO ()

-- | /fq_poly_set_nmod_poly/ /rop/ /op/ /ctx/ 
--
-- Sets the polynomial @rop@ to the polynomial @op@
foreign import ccall "fq_poly.h fq_poly_set_nmod_poly"
  fq_poly_set_nmod_poly :: Ptr CFqPoly -> Ptr CNModPoly -> Ptr CFqCtx -> IO ()

-- | /fq_poly_swap/ /op1/ /op2/ /ctx/ 
--
-- Swaps the two polynomials @op1@ and @op2@.
foreign import ccall "fq_poly.h fq_poly_swap"
  fq_poly_swap :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_zero/ /rop/ /len/ /ctx/ 
--
-- Sets @(rop, len)@ to the zero polynomial.
foreign import ccall "fq_poly.h _fq_poly_zero"
  _fq_poly_zero :: Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_zero/ /poly/ /ctx/ 
--
-- Sets @poly@ to the zero polynomial.
foreign import ccall "fq_poly.h fq_poly_zero"
  fq_poly_zero :: Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /fq_poly_one/ /poly/ /ctx/ 
--
-- Sets @poly@ to the constant polynomial \(1\).
foreign import ccall "fq_poly.h fq_poly_one"
  fq_poly_one :: Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /fq_poly_gen/ /poly/ /ctx/ 
--
-- Sets @poly@ to the polynomial \(x\).
foreign import ccall "fq_poly.h fq_poly_gen"
  fq_poly_gen :: Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /fq_poly_make_monic/ /rop/ /op/ /ctx/ 
--
-- Sets @rop@ to @op@, normed to have leading coefficient 1.
foreign import ccall "fq_poly.h fq_poly_make_monic"
  fq_poly_make_monic :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_make_monic/ /rop/ /op/ /length/ /ctx/ 
--
-- Sets @rop@ to @(op,length)@, normed to have leading coefficient 1.
-- Assumes that @rop@ has enough space for the polynomial, assumes that
-- @op@ is not zero (and thus has an invertible leading coefficient).
foreign import ccall "fq_poly.h _fq_poly_make_monic"
  _fq_poly_make_monic :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO ()

-- Getting and setting coefficients --------------------------------------------

-- | /fq_poly_get_coeff/ /x/ /poly/ /n/ /ctx/ 
--
-- Sets \(x\) to the coefficient of \(X^n\) in @poly@.
foreign import ccall "fq_poly.h fq_poly_get_coeff"
  fq_poly_get_coeff :: Ptr CFq -> Ptr CFqPoly -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_set_coeff/ /poly/ /n/ /x/ /ctx/ 
--
-- Sets the coefficient of \(X^n\) in @poly@ to \(x\).
foreign import ccall "fq_poly.h fq_poly_set_coeff"
  fq_poly_set_coeff :: Ptr CFqPoly -> CLong -> Ptr CFq -> Ptr CFqCtx -> IO ()

-- | /fq_poly_set_coeff_fmpz/ /poly/ /n/ /x/ /ctx/ 
--
-- Sets the coefficient of \(X^n\) in the polynomial to \(x\), assuming
-- \(n \geq 0\).
foreign import ccall "fq_poly.h fq_poly_set_coeff_fmpz"
  fq_poly_set_coeff_fmpz :: Ptr CFqPoly -> CLong -> Ptr CFmpz -> Ptr CFqCtx -> IO ()

-- Comparison ------------------------------------------------------------------

-- | /fq_poly_equal/ /poly1/ /poly2/ /ctx/ 
--
-- Returns nonzero if the two polynomials @poly1@ and @poly2@ are equal,
-- otherwise returns zero.
foreign import ccall "fq_poly.h fq_poly_equal"
  fq_poly_equal :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO CInt

-- | /fq_poly_equal_trunc/ /poly1/ /poly2/ /n/ /ctx/ 
--
-- Notionally truncate @poly1@ and @poly2@ to length \(n\) and return
-- nonzero if they are equal, otherwise return zero.
foreign import ccall "fq_poly.h fq_poly_equal_trunc"
  fq_poly_equal_trunc :: Ptr CFqPoly -> Ptr CFqPoly -> CLong -> Ptr CFqCtx -> IO CInt

-- | /fq_poly_is_zero/ /poly/ /ctx/ 
--
-- Returns whether the polynomial @poly@ is the zero polynomial.
foreign import ccall "fq_poly.h fq_poly_is_zero"
  fq_poly_is_zero :: Ptr CFqPoly -> Ptr CFqCtx -> IO CInt

-- | /fq_poly_is_one/ /op/ 
--
-- Returns whether the polynomial @poly@ is equal to the constant
-- polynomial \(1\).
foreign import ccall "fq_poly.h fq_poly_is_one"
  fq_poly_is_one :: Ptr CFqPoly -> IO CInt

-- | /fq_poly_is_gen/ /op/ /ctx/ 
--
-- Returns whether the polynomial @poly@ is equal to the polynomial \(x\).
foreign import ccall "fq_poly.h fq_poly_is_gen"
  fq_poly_is_gen :: Ptr CFqPoly -> Ptr CFqCtx -> IO CInt

-- | /fq_poly_is_unit/ /op/ /ctx/ 
--
-- Returns whether the polynomial @poly@ is a unit in the polynomial ring
-- \(\mathbf{F}_q[X]\), i.e. if it has degree \(0\) and is non-zero.
foreign import ccall "fq_poly.h fq_poly_is_unit"
  fq_poly_is_unit :: Ptr CFqPoly -> Ptr CFqCtx -> IO CInt

-- | /fq_poly_equal_fq/ /poly/ /c/ /ctx/ 
--
-- Returns whether the polynomial @poly@ is equal the (constant)
-- \(\mathbf{F}_q\) element @c@
foreign import ccall "fq_poly.h fq_poly_equal_fq"
  fq_poly_equal_fq :: Ptr CFqPoly -> Ptr CFq -> Ptr CFqCtx -> IO CInt

-- Addition and subtraction ----------------------------------------------------

-- | /_fq_poly_add/ /res/ /poly1/ /len1/ /poly2/ /len2/ /ctx/ 
--
-- Sets @res@ to the sum of @(poly1,len1)@ and @(poly2,len2)@.
foreign import ccall "fq_poly.h _fq_poly_add"
  _fq_poly_add :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_add/ /res/ /poly1/ /poly2/ /ctx/ 
--
-- Sets @res@ to the sum of @poly1@ and @poly2@.
foreign import ccall "fq_poly.h fq_poly_add"
  fq_poly_add :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /fq_poly_add_si/ /res/ /poly1/ /c/ /ctx/ 
--
-- Sets @res@ to the sum of @poly1@ and @c@.
foreign import ccall "fq_poly.h fq_poly_add_si"
  fq_poly_add_si :: Ptr CFqPoly -> Ptr CFqPoly -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_add_series/ /res/ /poly1/ /poly2/ /n/ /ctx/ 
--
-- Notionally truncate @poly1@ and @poly2@ to length @n@ and set @res@ to
-- the sum.
foreign import ccall "fq_poly.h fq_poly_add_series"
  fq_poly_add_series :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> CLong -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_sub/ /res/ /poly1/ /len1/ /poly2/ /len2/ /ctx/ 
--
-- Sets @res@ to the difference of @(poly1,len1)@ and @(poly2,len2)@.
foreign import ccall "fq_poly.h _fq_poly_sub"
  _fq_poly_sub :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_sub/ /res/ /poly1/ /poly2/ /ctx/ 
--
-- Sets @res@ to the difference of @poly1@ and @poly2@.
foreign import ccall "fq_poly.h fq_poly_sub"
  fq_poly_sub :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /fq_poly_sub_series/ /res/ /poly1/ /poly2/ /n/ /ctx/ 
--
-- Notionally truncate @poly1@ and @poly2@ to length @n@ and set @res@ to
-- the difference.
foreign import ccall "fq_poly.h fq_poly_sub_series"
  fq_poly_sub_series :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> CLong -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_neg/ /rop/ /op/ /len/ /ctx/ 
--
-- Sets @rop@ to the additive inverse of @(poly,len)@.
foreign import ccall "fq_poly.h _fq_poly_neg"
  _fq_poly_neg :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_neg/ /res/ /poly/ /ctx/ 
--
-- Sets @res@ to the additive inverse of @poly@.
foreign import ccall "fq_poly.h fq_poly_neg"
  fq_poly_neg :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- Scalar multiplication and division ------------------------------------------

-- | /_fq_poly_scalar_mul_fq/ /rop/ /op/ /len/ /x/ /ctx/ 
--
-- Sets @(rop,len)@ to the product of @(op,len)@ by the scalar @x@, in the
-- context defined by @ctx@.
foreign import ccall "fq_poly.h _fq_poly_scalar_mul_fq"
  _fq_poly_scalar_mul_fq :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr CFq -> Ptr CFqCtx -> IO ()

-- | /fq_poly_scalar_mul_fq/ /rop/ /op/ /x/ /ctx/ 
--
-- Sets @rop@ to the product of @op@ by the scalar @x@, in the context
-- defined by @ctx@.
foreign import ccall "fq_poly.h fq_poly_scalar_mul_fq"
  fq_poly_scalar_mul_fq :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFq -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_scalar_addmul_fq/ /rop/ /op/ /len/ /x/ /ctx/ 
--
-- Adds to @(rop,len)@ the product of @(op,len)@ by the scalar @x@, in the
-- context defined by @ctx@. In particular, assumes the same length for
-- @op@ and @rop@.
foreign import ccall "fq_poly.h _fq_poly_scalar_addmul_fq"
  _fq_poly_scalar_addmul_fq :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr CFq -> Ptr CFqCtx -> IO ()

-- | /fq_poly_scalar_addmul_fq/ /rop/ /op/ /x/ /ctx/ 
--
-- Adds to @rop@ the product of @op@ by the scalar @x@, in the context
-- defined by @ctx@.
foreign import ccall "fq_poly.h fq_poly_scalar_addmul_fq"
  fq_poly_scalar_addmul_fq :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFq -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_scalar_submul_fq/ /rop/ /op/ /len/ /x/ /ctx/ 
--
-- Subtracts from @(rop,len)@ the product of @(op,len)@ by the scalar @x@,
-- in the context defined by @ctx@. In particular, assumes the same length
-- for @op@ and @rop@.
foreign import ccall "fq_poly.h _fq_poly_scalar_submul_fq"
  _fq_poly_scalar_submul_fq :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr CFq -> Ptr CFqCtx -> IO ()

-- | /fq_poly_scalar_submul_fq/ /rop/ /op/ /x/ /ctx/ 
--
-- Subtracts from @rop@ the product of @op@ by the scalar @x@, in the
-- context defined by @ctx@.
foreign import ccall "fq_poly.h fq_poly_scalar_submul_fq"
  fq_poly_scalar_submul_fq :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFq -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_scalar_div_fq/ /rop/ /op/ /len/ /x/ /ctx/ 
--
-- Sets @(rop,len)@ to the quotient of @(op,len)@ by the scalar @x@, in the
-- context defined by @ctx@. An exception is raised if @x@ is zero.
foreign import ccall "fq_poly.h _fq_poly_scalar_div_fq"
  _fq_poly_scalar_div_fq :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr CFq -> Ptr CFqCtx -> IO ()

-- | /fq_poly_scalar_div_fq/ /rop/ /op/ /x/ /ctx/ 
--
-- Sets @rop@ to the quotient of @op@ by the scalar @x@, in the context
-- defined by @ctx@. An exception is raised if @x@ is zero.
foreign import ccall "fq_poly.h fq_poly_scalar_div_fq"
  fq_poly_scalar_div_fq :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFq -> Ptr CFqCtx -> IO ()

-- Multiplication --------------------------------------------------------------

-- | /_fq_poly_mul_classical/ /rop/ /op1/ /len1/ /op2/ /len2/ /ctx/ 
--
-- Sets @(rop, len1 + len2 - 1)@ to the product of @(op1, len1)@ and
-- @(op2, len2)@, assuming that @len1@ is at least @len2@ and neither is
-- zero.
-- 
-- Permits zero padding. Does not support aliasing of @rop@ with either
-- @op1@ or @op2@.
foreign import ccall "fq_poly.h _fq_poly_mul_classical"
  _fq_poly_mul_classical :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_mul_classical/ /rop/ /op1/ /op2/ /ctx/ 
--
-- Sets @rop@ to the product of @op1@ and @op2@ using classical polynomial
-- multiplication.
foreign import ccall "fq_poly.h fq_poly_mul_classical"
  fq_poly_mul_classical :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_mul_reorder/ /rop/ /op1/ /len1/ /op2/ /len2/ /ctx/ 
--
-- Sets @(rop, len1 + len2 - 1)@ to the product of @(op1, len1)@ and
-- @(op2, len2)@, assuming that @len1@ and @len2@ are non-zero.
-- 
-- Permits zero padding. Supports aliasing.
foreign import ccall "fq_poly.h _fq_poly_mul_reorder"
  _fq_poly_mul_reorder :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_mul_reorder/ /rop/ /op1/ /op2/ /ctx/ 
--
-- Sets @rop@ to the product of @op1@ and @op2@, reordering the two
-- indeterminates \(X\) and \(Y\) when viewing the polynomials as elements
-- of \(\mathbf{F}_p[X,Y]\).
-- 
-- Suppose \(\mathbf{F}_q = \mathbf{F}_p[X]/ (f(X))\) and recall that
-- elements of \(\mathbf{F}_q\) are internally represented by elements of
-- type @fmpz_poly@. For small degree extensions but polynomials in
-- \(\mathbf{F}_q[Y]\) of large degree \(n\), we change the representation
-- to
-- 
-- \[`\]
-- \[\begin{aligned}
-- \begin{split}
-- g(Y) & = \sum_{i=0}^{n} a_i(X) Y^i \\
--      & = \sum_{j=0}^{d} \sum_{i=0}^{n} \text{Coeff}(a_i(X), j) Y^i.
-- \end{split}
-- \end{aligned}\]
-- 
-- This allows us to use a poor algorithm (such as classical
-- multiplication) in the \(X\)-direction and leverage the existing fast
-- integer multiplication routines in the \(Y\)-direction where the
-- polynomial degree \(n\) is large.
foreign import ccall "fq_poly.h fq_poly_mul_reorder"
  fq_poly_mul_reorder :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_mul_univariate/ /rop/ /op1/ /len1/ /op2/ /len2/ /ctx/ 
--
-- Sets @(rop, len1 + len2 - 1)@ to the product of @(op1, len1)@ and
-- @(op2, len2)@.
-- 
-- Permits zero padding and places no assumptions on the lengths @len1@ and
-- @len2@. Supports aliasing.
foreign import ccall "fq_poly.h _fq_poly_mul_univariate"
  _fq_poly_mul_univariate :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_mul_univariate/ /rop/ /op1/ /op2/ /ctx/ 
--
-- Sets @rop@ to the product of @op1@ and @op2@ using a bivariate to
-- univariate transformation and reducing this problem to multiplying two
-- univariate polynomials.
foreign import ccall "fq_poly.h fq_poly_mul_univariate"
  fq_poly_mul_univariate :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_mul_KS/ /rop/ /op1/ /len1/ /op2/ /len2/ /ctx/ 
--
-- Sets @(rop, len1 + len2 - 1)@ to the product of @(op1, len1)@ and
-- @(op2, len2)@.
-- 
-- Permits zero padding and places no assumptions on the lengths @len1@ and
-- @len2@. Supports aliasing.
foreign import ccall "fq_poly.h _fq_poly_mul_KS"
  _fq_poly_mul_KS :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_mul_KS/ /rop/ /op1/ /op2/ /ctx/ 
--
-- Sets @rop@ to the product of @op1@ and @op2@ using Kronecker
-- substitution, that is, by encoding each coefficient in
-- \(\mathbf{F}_{q}\) as an integer and reducing this problem to
-- multiplying two polynomials over the integers.
foreign import ccall "fq_poly.h fq_poly_mul_KS"
  fq_poly_mul_KS :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_mul/ /rop/ /op1/ /len1/ /op2/ /len2/ /ctx/ 
--
-- Sets @(rop, len1 + len2 - 1)@ to the product of @(op1, len1)@ and
-- @(op2, len2)@, choosing an appropriate algorithm.
-- 
-- Permits zero padding. Does not support aliasing.
foreign import ccall "fq_poly.h _fq_poly_mul"
  _fq_poly_mul :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_mul/ /rop/ /op1/ /op2/ /ctx/ 
--
-- Sets @rop@ to the product of @op1@ and @op2@, choosing an appropriate
-- algorithm.
foreign import ccall "fq_poly.h fq_poly_mul"
  fq_poly_mul :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_mullow_classical/ /rop/ /op1/ /len1/ /op2/ /len2/ /n/ /ctx/ 
--
-- Sets @(rop, n)@ to the first \(n\) coefficients of @(op1, len1)@
-- multiplied by @(op2, len2)@.
-- 
-- Assumes @0 \< n \<= len1 + len2 - 1@. Assumes neither @len1@ nor @len2@
-- is zero.
foreign import ccall "fq_poly.h _fq_poly_mullow_classical"
  _fq_poly_mullow_classical :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> CLong -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_mullow_classical/ /rop/ /op1/ /op2/ /n/ /ctx/ 
--
-- Sets @rop@ to the product of @poly1@ and @poly2@, computed using the
-- classical or schoolbook method.
foreign import ccall "fq_poly.h fq_poly_mullow_classical"
  fq_poly_mullow_classical :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> CLong -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_mullow_univariate/ /rop/ /op1/ /len1/ /op2/ /len2/ /n/ /ctx/ 
--
-- Sets @(rop, n)@ to the lowest \(n\) coefficients of the product of
-- @(op1, len1)@ and @(op2, len2)@, computed using a bivariate to
-- univariate transformation.
-- 
-- Assumes that @len1@ and @len2@ are positive, but does allow for the
-- polynomials to be zero-padded. The polynomials may be zero, too. Assumes
-- \(n\) is positive. Supports aliasing between @res@, @poly1@ and @poly2@.
foreign import ccall "fq_poly.h _fq_poly_mullow_univariate"
  _fq_poly_mullow_univariate :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> CLong -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_mullow_univariate/ /rop/ /op1/ /op2/ /n/ /ctx/ 
--
-- Sets @rop@ to the lowest \(n\) coefficients of the product of @op1@ and
-- @op2@, computed using a bivariate to univariate transformation.
foreign import ccall "fq_poly.h fq_poly_mullow_univariate"
  fq_poly_mullow_univariate :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> CLong -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_mullow_KS/ /rop/ /op1/ /len1/ /op2/ /len2/ /n/ /ctx/ 
--
-- Sets @(rop, n)@ to the lowest \(n\) coefficients of the product of
-- @(op1, len1)@ and @(op2, len2)@.
-- 
-- Assumes that @len1@ and @len2@ are positive, but does allow for the
-- polynomials to be zero-padded. The polynomials may be zero, too. Assumes
-- \(n\) is positive. Supports aliasing between @rop@, @op1@ and @op2@.
foreign import ccall "fq_poly.h _fq_poly_mullow_KS"
  _fq_poly_mullow_KS :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> CLong -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_mullow_KS/ /rop/ /op1/ /op2/ /n/ /ctx/ 
--
-- Sets @rop@ to the lowest \(n\) coefficients of the product of @op1@ and
-- @op2@.
foreign import ccall "fq_poly.h fq_poly_mullow_KS"
  fq_poly_mullow_KS :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> CLong -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_mullow/ /rop/ /op1/ /len1/ /op2/ /len2/ /n/ /ctx/ 
--
-- Sets @(rop, n)@ to the lowest \(n\) coefficients of the product of
-- @(op1, len1)@ and @(op2, len2)@.
-- 
-- Assumes @0 \< n \<= len1 + len2 - 1@. Allows for zero-padding in the
-- inputs. Does not support aliasing between the inputs and the output.
foreign import ccall "fq_poly.h _fq_poly_mullow"
  _fq_poly_mullow :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> CLong -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_mullow/ /rop/ /op1/ /op2/ /n/ /ctx/ 
--
-- Sets @rop@ to the lowest \(n\) coefficients of the product of @op1@ and
-- @op2@.
foreign import ccall "fq_poly.h fq_poly_mullow"
  fq_poly_mullow :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> CLong -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_mulhigh_classical/ /res/ /poly1/ /len1/ /poly2/ /len2/ /start/ /ctx/ 
--
-- Computes the product of @(poly1, len1)@ and @(poly2, len2)@ and writes
-- the coefficients from @start@ onwards into the high coefficients of
-- @res@, the remaining coefficients being arbitrary but reduced. Assumes
-- that @len1 >= len2 > 0@. Aliasing of inputs and output is not permitted.
-- Algorithm is classical multiplication.
foreign import ccall "fq_poly.h _fq_poly_mulhigh_classical"
  _fq_poly_mulhigh_classical :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> CLong -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_mulhigh_classical/ /res/ /poly1/ /poly2/ /start/ /ctx/ 
--
-- Computes the product of @poly1@ and @poly2@ and writes the coefficients
-- from @start@ onwards into the high coefficients of @res@, the remaining
-- coefficients being arbitrary but reduced. Algorithm is classical
-- multiplication.
foreign import ccall "fq_poly.h fq_poly_mulhigh_classical"
  fq_poly_mulhigh_classical :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> CLong -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_mulhigh/ /res/ /poly1/ /len1/ /poly2/ /len2/ /start/ /ctx/ 
--
-- Computes the product of @(poly1, len1)@ and @(poly2, len2)@ and writes
-- the coefficients from @start@ onwards into the high coefficients of
-- @res@, the remaining coefficients being arbitrary but reduced. Assumes
-- that @len1 >= len2 > 0@. Aliasing of inputs and output is not permitted.
foreign import ccall "fq_poly.h _fq_poly_mulhigh"
  _fq_poly_mulhigh :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> CLong -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_mulhigh/ /res/ /poly1/ /poly2/ /start/ /ctx/ 
--
-- Computes the product of @poly1@ and @poly2@ and writes the coefficients
-- from @start@ onwards into the high coefficients of @res@, the remaining
-- coefficients being arbitrary but reduced.
foreign import ccall "fq_poly.h fq_poly_mulhigh"
  fq_poly_mulhigh :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> CLong -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_mulmod/ /res/ /poly1/ /len1/ /poly2/ /len2/ /f/ /lenf/ /ctx/ 
--
-- Sets @res@ to the remainder of the product of @poly1@ and @poly2@ upon
-- polynomial division by @f@.
-- 
-- It is required that @len1 + len2 - lenf > 0@, which is equivalent to
-- requiring that the result will actually be reduced. Otherwise, simply
-- use @_fq_poly_mul@ instead.
-- 
-- Aliasing of @f@ and @res@ is not permitted.
foreign import ccall "fq_poly.h _fq_poly_mulmod"
  _fq_poly_mulmod :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_mulmod/ /res/ /poly1/ /poly2/ /f/ /ctx/ 
--
-- Sets @res@ to the remainder of the product of @poly1@ and @poly2@ upon
-- polynomial division by @f@.
foreign import ccall "fq_poly.h fq_poly_mulmod"
  fq_poly_mulmod :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_mulmod_preinv/ /res/ /poly1/ /len1/ /poly2/ /len2/ /f/ /lenf/ /finv/ /lenfinv/ /ctx/ 
--
-- Sets @res@ to the remainder of the product of @poly1@ and @poly2@ upon
-- polynomial division by @f@.
-- 
-- It is required that @finv@ is the inverse of the reverse of @f@ mod
-- @x^lenf@.
-- 
-- Aliasing of @res@ with any of the inputs is not permitted.
foreign import ccall "fq_poly.h _fq_poly_mulmod_preinv"
  _fq_poly_mulmod_preinv :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_mulmod_preinv/ /res/ /poly1/ /poly2/ /f/ /finv/ /ctx/ 
--
-- Sets @res@ to the remainder of the product of @poly1@ and @poly2@ upon
-- polynomial division by @f@. @finv@ is the inverse of the reverse of @f@.
foreign import ccall "fq_poly.h fq_poly_mulmod_preinv"
  fq_poly_mulmod_preinv :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- Squaring --------------------------------------------------------------------

-- | /_fq_poly_sqr_classical/ /rop/ /op/ /len/ /ctx/ 
--
-- Sets @(rop, 2*len - 1)@ to the square of @(op, len)@, assuming that
-- @(op,len)@ is not zero and using classical polynomial multiplication.
-- 
-- Permits zero padding. Does not support aliasing of @rop@ with either
-- @op1@ or @op2@.
foreign import ccall "fq_poly.h _fq_poly_sqr_classical"
  _fq_poly_sqr_classical :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_sqr_classical/ /rop/ /op/ /ctx/ 
--
-- [Sets @rop@ to the square of @op@ using classical]
--     polynomial multiplication.
foreign import ccall "fq_poly.h fq_poly_sqr_classical"
  fq_poly_sqr_classical :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_sqr_reorder/ /rop/ /op/ /len/ /ctx/ 
--
-- Sets @(rop, 2*len- 1)@ to the square of @(op, len)@, assuming that @len@
-- is not zero reordering the two indeterminates \(X\) and \(Y\) when
-- viewing the polynomials as elements of \(\mathbf{F}_p[X,Y]\).
-- 
-- Permits zero padding. Supports aliasing.
foreign import ccall "fq_poly.h _fq_poly_sqr_reorder"
  _fq_poly_sqr_reorder :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_sqr_reorder/ /rop/ /op/ /ctx/ 
--
-- Sets @rop@ to the square of @op@, assuming that @len@ is not zero
-- reordering the two indeterminates \(X\) and \(Y\) when viewing the
-- polynomials as elements of \(\mathbf{F}_p[X,Y]\). See
-- @fq_poly_mul_reorder@.
foreign import ccall "fq_poly.h fq_poly_sqr_reorder"
  fq_poly_sqr_reorder :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_sqr_KS/ /rop/ /op/ /len/ /ctx/ 
--
-- Sets @(rop, 2*len - 1)@ to the square of @(op, len)@.
-- 
-- Permits zero padding and places no assumptions on the lengths @len1@ and
-- @len2@. Supports aliasing.
foreign import ccall "fq_poly.h _fq_poly_sqr_KS"
  _fq_poly_sqr_KS :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_sqr_KS/ /rop/ /op/ /ctx/ 
--
-- Sets @rop@ to the square @op@ using Kronecker substitution, that is, by
-- encoding each coefficient in \(\mathbf{F}_{q}\) as an integer and
-- reducing this problem to multiplying two polynomials over the integers.
foreign import ccall "fq_poly.h fq_poly_sqr_KS"
  fq_poly_sqr_KS :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_sqr/ /rop/ /op/ /len/ /ctx/ 
--
-- Sets @(rop, 2* len - 1)@ to the square of @(op, len)@, choosing an
-- appropriate algorithm.
-- 
-- Permits zero padding. Does not support aliasing.
foreign import ccall "fq_poly.h _fq_poly_sqr"
  _fq_poly_sqr :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_sqr/ /rop/ /op/ /ctx/ 
--
-- Sets @rop@ to the square of @op@, choosing an appropriate algorithm.
foreign import ccall "fq_poly.h fq_poly_sqr"
  fq_poly_sqr :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- Powering --------------------------------------------------------------------

-- | /_fq_poly_pow/ /rop/ /op/ /len/ /e/ /ctx/ 
--
-- Sets @rop = op^e@, assuming that @e, len > 0@ and that @rop@ has space
-- for @e*(len - 1) + 1@ coefficients. Does not support aliasing.
foreign import ccall "fq_poly.h _fq_poly_pow"
  _fq_poly_pow :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> CULong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_pow/ /rop/ /op/ /e/ /ctx/ 
--
-- Computes @rop = op^e@. If \(e\) is zero, returns one, so that in
-- particular @0^0 = 1@.
foreign import ccall "fq_poly.h fq_poly_pow"
  fq_poly_pow :: Ptr CFqPoly -> Ptr CFqPoly -> CULong -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_powmod_ui_binexp/ /res/ /poly/ /e/ /f/ /lenf/ /ctx/ 
--
-- Sets @res@ to @poly@ raised to the power @e@ modulo @f@, using binary
-- exponentiation. We require @e > 0@.
-- 
-- We require @lenf > 1@. It is assumed that @poly@ is already reduced
-- modulo @f@ and zero-padded as necessary to have length exactly
-- @lenf - 1@. The output @res@ must have room for @lenf - 1@ coefficients.
foreign import ccall "fq_poly.h _fq_poly_powmod_ui_binexp"
  _fq_poly_powmod_ui_binexp :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CULong -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_powmod_ui_binexp/ /res/ /poly/ /e/ /f/ /ctx/ 
--
-- Sets @res@ to @poly@ raised to the power @e@ modulo @f@, using binary
-- exponentiation. We require @e >= 0@.
foreign import ccall "fq_poly.h fq_poly_powmod_ui_binexp"
  fq_poly_powmod_ui_binexp :: Ptr CFqPoly -> Ptr CFqPoly -> CULong -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_powmod_ui_binexp_preinv/ /res/ /poly/ /e/ /f/ /lenf/ /finv/ /lenfinv/ /ctx/ 
--
-- Sets @res@ to @poly@ raised to the power @e@ modulo @f@, using binary
-- exponentiation. We require @e > 0@. We require @finv@ to be the inverse
-- of the reverse of @f@.
-- 
-- We require @lenf > 1@. It is assumed that @poly@ is already reduced
-- modulo @f@ and zero-padded as necessary to have length exactly
-- @lenf - 1@. The output @res@ must have room for @lenf - 1@ coefficients.
foreign import ccall "fq_poly.h _fq_poly_powmod_ui_binexp_preinv"
  _fq_poly_powmod_ui_binexp_preinv :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CULong -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_powmod_ui_binexp_preinv/ /res/ /poly/ /e/ /f/ /finv/ /ctx/ 
--
-- Sets @res@ to @poly@ raised to the power @e@ modulo @f@, using binary
-- exponentiation. We require @e >= 0@. We require @finv@ to be the inverse
-- of the reverse of @f@.
foreign import ccall "fq_poly.h fq_poly_powmod_ui_binexp_preinv"
  fq_poly_powmod_ui_binexp_preinv :: Ptr CFqPoly -> Ptr CFqPoly -> CULong -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_powmod_fmpz_binexp/ /res/ /poly/ /e/ /f/ /lenf/ /ctx/ 
--
-- Sets @res@ to @poly@ raised to the power @e@ modulo @f@, using binary
-- exponentiation. We require @e > 0@.
-- 
-- We require @lenf > 1@. It is assumed that @poly@ is already reduced
-- modulo @f@ and zero-padded as necessary to have length exactly
-- @lenf - 1@. The output @res@ must have room for @lenf - 1@ coefficients.
foreign import ccall "fq_poly.h _fq_poly_powmod_fmpz_binexp"
  _fq_poly_powmod_fmpz_binexp :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> Ptr CFmpz -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_powmod_fmpz_binexp/ /res/ /poly/ /e/ /f/ /ctx/ 
--
-- Sets @res@ to @poly@ raised to the power @e@ modulo @f@, using binary
-- exponentiation. We require @e >= 0@.
foreign import ccall "fq_poly.h fq_poly_powmod_fmpz_binexp"
  fq_poly_powmod_fmpz_binexp :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFmpz -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_powmod_fmpz_binexp_preinv/ /res/ /poly/ /e/ /f/ /lenf/ /finv/ /lenfinv/ /ctx/ 
--
-- Sets @res@ to @poly@ raised to the power @e@ modulo @f@, using binary
-- exponentiation. We require @e > 0@. We require @finv@ to be the inverse
-- of the reverse of @f@.
-- 
-- We require @lenf > 1@. It is assumed that @poly@ is already reduced
-- modulo @f@ and zero-padded as necessary to have length exactly
-- @lenf - 1@. The output @res@ must have room for @lenf - 1@ coefficients.
foreign import ccall "fq_poly.h _fq_poly_powmod_fmpz_binexp_preinv"
  _fq_poly_powmod_fmpz_binexp_preinv :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> Ptr CFmpz -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_powmod_fmpz_binexp_preinv/ /res/ /poly/ /e/ /f/ /finv/ /ctx/ 
--
-- Sets @res@ to @poly@ raised to the power @e@ modulo @f@, using binary
-- exponentiation. We require @e >= 0@. We require @finv@ to be the inverse
-- of the reverse of @f@.
foreign import ccall "fq_poly.h fq_poly_powmod_fmpz_binexp_preinv"
  fq_poly_powmod_fmpz_binexp_preinv :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFmpz -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_powmod_fmpz_sliding_preinv/ /res/ /poly/ /e/ /k/ /f/ /lenf/ /finv/ /lenfinv/ /ctx/ 
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
foreign import ccall "fq_poly.h _fq_poly_powmod_fmpz_sliding_preinv"
  _fq_poly_powmod_fmpz_sliding_preinv :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> Ptr CFmpz -> CULong -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_powmod_fmpz_sliding_preinv/ /res/ /poly/ /e/ /k/ /f/ /finv/ /ctx/ 
--
-- Sets @res@ to @poly@ raised to the power @e@ modulo @f@, using
-- sliding-window exponentiation with window size @k@. We require @e >= 0@.
-- We require @finv@ to be the inverse of the reverse of @f@. If @k@ is set
-- to zero, then an \"optimum\" size will be selected automatically base on
-- @e@.
foreign import ccall "fq_poly.h fq_poly_powmod_fmpz_sliding_preinv"
  fq_poly_powmod_fmpz_sliding_preinv :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFmpz -> CULong -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_powmod_x_fmpz_preinv/ /res/ /e/ /f/ /lenf/ /finv/ /lenfinv/ /ctx/ 
--
-- Sets @res@ to @x@ raised to the power @e@ modulo @f@, using sliding
-- window exponentiation. We require @e > 0@. We require @finv@ to be the
-- inverse of the reverse of @f@.
-- 
-- We require @lenf > 2@. The output @res@ must have room for @lenf - 1@
-- coefficients.
foreign import ccall "fq_poly.h _fq_poly_powmod_x_fmpz_preinv"
  _fq_poly_powmod_x_fmpz_preinv :: Ptr (Ptr CFq) -> Ptr CFmpz -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_powmod_x_fmpz_preinv/ /res/ /e/ /f/ /finv/ /ctx/ 
--
-- Sets @res@ to @x@ raised to the power @e@ modulo @f@, using sliding
-- window exponentiation. We require @e >= 0@. We require @finv@ to be the
-- inverse of the reverse of @f@.
foreign import ccall "fq_poly.h fq_poly_powmod_x_fmpz_preinv"
  fq_poly_powmod_x_fmpz_preinv :: Ptr CFqPoly -> Ptr CFmpz -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_pow_trunc_binexp/ /res/ /poly/ /e/ /trunc/ /ctx/ 
--
-- Sets @res@ to the low @trunc@ coefficients of @poly@ (assumed to be zero
-- padded if necessary to length @trunc@) to the power @e@. This is
-- equivalent to doing a powering followed by a truncation. We require that
-- @res@ has enough space for @trunc@ coefficients, that @trunc > 0@ and
-- that @e > 1@. Aliasing is not permitted. Uses the binary exponentiation
-- method.
foreign import ccall "fq_poly.h _fq_poly_pow_trunc_binexp"
  _fq_poly_pow_trunc_binexp :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CULong -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_pow_trunc_binexp/ /res/ /poly/ /e/ /trunc/ /ctx/ 
--
-- Sets @res@ to the low @trunc@ coefficients of @poly@ to the power @e@.
-- This is equivalent to doing a powering followed by a truncation. Uses
-- the binary exponentiation method.
foreign import ccall "fq_poly.h fq_poly_pow_trunc_binexp"
  fq_poly_pow_trunc_binexp :: Ptr CFqPoly -> Ptr CFqPoly -> CULong -> CLong -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_pow_trunc/ /res/ /poly/ /e/ /trunc/ /mod/ 
--
-- Sets @res@ to the low @trunc@ coefficients of @poly@ (assumed to be zero
-- padded if necessary to length @trunc@) to the power @e@. This is
-- equivalent to doing a powering followed by a truncation. We require that
-- @res@ has enough space for @trunc@ coefficients, that @trunc > 0@ and
-- that @e > 1@. Aliasing is not permitted.
foreign import ccall "fq_poly.h _fq_poly_pow_trunc"
  _fq_poly_pow_trunc :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CULong -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_pow_trunc/ /res/ /poly/ /e/ /trunc/ /ctx/ 
--
-- Sets @res@ to the low @trunc@ coefficients of @poly@ to the power @e@.
-- This is equivalent to doing a powering followed by a truncation.
foreign import ccall "fq_poly.h fq_poly_pow_trunc"
  fq_poly_pow_trunc :: Ptr CFqPoly -> Ptr CFqPoly -> CULong -> CLong -> Ptr CFqCtx -> IO ()

-- Shifting --------------------------------------------------------------------

-- | /_fq_poly_shift_left/ /rop/ /op/ /len/ /n/ /ctx/ 
--
-- Sets @(rop, len + n)@ to @(op, len)@ shifted left by \(n\) coefficients.
-- 
-- Inserts zero coefficients at the lower end. Assumes that @len@ and \(n\)
-- are positive, and that @rop@ fits @len + n@ elements. Supports aliasing
-- between @rop@ and @op@.
foreign import ccall "fq_poly.h _fq_poly_shift_left"
  _fq_poly_shift_left :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_shift_left/ /rop/ /op/ /n/ /ctx/ 
--
-- Sets @rop@ to @op@ shifted left by \(n\) coeffs. Zero coefficients are
-- inserted.
foreign import ccall "fq_poly.h fq_poly_shift_left"
  fq_poly_shift_left :: Ptr CFqPoly -> Ptr CFqPoly -> CLong -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_shift_right/ /rop/ /op/ /len/ /n/ /ctx/ 
--
-- Sets @(rop, len - n)@ to @(op, len)@ shifted right by \(n\)
-- coefficients.
-- 
-- Assumes that @len@ and \(n\) are positive, that @len > n@, and that
-- @rop@ fits @len - n@ elements. Supports aliasing between @rop@ and @op@,
-- although in this case the top coefficients of @op@ are not set to zero.
foreign import ccall "fq_poly.h _fq_poly_shift_right"
  _fq_poly_shift_right :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_shift_right/ /rop/ /op/ /n/ /ctx/ 
--
-- Sets @rop@ to @op@ shifted right by \(n\) coefficients. If \(n\) is
-- equal to or greater than the current length of @op@, @rop@ is set to the
-- zero polynomial.
foreign import ccall "fq_poly.h fq_poly_shift_right"
  fq_poly_shift_right :: Ptr CFqPoly -> Ptr CFqPoly -> CLong -> Ptr CFqCtx -> IO ()

-- Norms -----------------------------------------------------------------------

-- | /fq_poly_hamming_weight/ /op/ /ctx/ 
--
-- Returns the number of non-zero entries in the polynomial @op@.
foreign import ccall "fq_poly.h fq_poly_hamming_weight"
  fq_poly_hamming_weight :: Ptr CFqPoly -> Ptr CFqCtx -> IO CLong

-- Euclidean division ----------------------------------------------------------

-- | /_fq_poly_divrem/ /Q/ /R/ /A/ /lenA/ /B/ /lenB/ /invB/ /ctx/ 
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
foreign import ccall "fq_poly.h _fq_poly_divrem"
  _fq_poly_divrem :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> CLong -> Ptr CFq -> Ptr CFqCtx -> IO ()

-- | /fq_poly_divrem/ /Q/ /R/ /A/ /B/ /ctx/ 
--
-- Computes \(Q\), \(R\) such that \(A = B Q + R\) with
-- \(0 \leq \operatorname{len}(R) < \operatorname{len}(B)\).
-- 
-- Assumes that the leading coefficient of \(B\) is invertible. This can be
-- taken for granted the context is for a finite field, that is, when \(p\)
-- is prime and \(f(X)\) is irreducible.
foreign import ccall "fq_poly.h fq_poly_divrem"
  fq_poly_divrem :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /fq_poly_divrem_f/ /f/ /Q/ /R/ /A/ /B/ /ctx/ 
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
foreign import ccall "fq_poly.h fq_poly_divrem_f"
  fq_poly_divrem_f :: Ptr CFq -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_rem/ /R/ /A/ /lenA/ /B/ /lenB/ /invB/ /ctx/ 
--
-- Sets @R@ to the remainder of the division of @(A,lenA)@ by @(B,lenB)@.
-- Assumes that the leading coefficient of @(B,lenB)@ is invertible and
-- that @invB@ is its inverse.
foreign import ccall "fq_poly.h _fq_poly_rem"
  _fq_poly_rem :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> CLong -> Ptr CFq -> Ptr CFqCtx -> IO ()

-- | /fq_poly_rem/ /R/ /A/ /B/ /ctx/ 
--
-- Sets @R@ to the remainder of the division of @A@ by @B@ in the context
-- described by @ctx@.
foreign import ccall "fq_poly.h fq_poly_rem"
  fq_poly_rem :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_div/ /Q/ /A/ /lenA/ /B/ /lenB/ /invB/ /ctx/ 
--
-- Notationally, computes \(Q\), \(R\) such that \(A = B Q + R\) with \(0
-- \leq \operatorname{len}(R) < \operatorname{len}(B)\) but only sets
-- @(Q, lenA - lenB + 1)@. Allows zero-padding in \(A\) but not in \(B\).
-- Assumes that the leading coefficient of \(B\) is a unit.
foreign import ccall "fq_poly.h _fq_poly_div"
  _fq_poly_div :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> CLong -> Ptr CFq -> Ptr CFqCtx -> IO ()

-- | /fq_poly_div/ /Q/ /A/ /B/ /ctx/ 
--
-- Notionally finds polynomials \(Q\) and \(R\) such that \(A = B Q + R\)
-- with \(\operatorname{len}(R) < \operatorname{len}(B)\), but returns only
-- @Q@. If \(\operatorname{len}(B) = 0\) an exception is raised.
foreign import ccall "fq_poly.h fq_poly_div"
  fq_poly_div :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_div_newton_n_preinv/ /Q/ /A/ /lenA/ /B/ /lenB/ /Binv/ /lenBinv/ /ctx_t/ 
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
foreign import ccall "fq_poly.h _fq_poly_div_newton_n_preinv"
  _fq_poly_div_newton_n_preinv :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> CLong -> Ptr CFq -> IO ()

-- | /fq_poly_div_newton_n_preinv/ /Q/ /A/ /B/ /Binv/ /ctx/ 
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
foreign import ccall "fq_poly.h fq_poly_div_newton_n_preinv"
  fq_poly_div_newton_n_preinv :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_divrem_newton_n_preinv/ /Q/ /R/ /A/ /lenA/ /B/ /lenB/ /Binv/ /lenBinv/ /ctx/ 
--
-- Computes \(Q\) and \(R\) such that \(A = BQ + R\) with
-- \(\operatorname{len}(R)\) less than @lenB@, where \(A\) is of length
-- @lenA@ and \(B\) is of length @lenB@. We require that \(Q\) have space
-- for @lenA - lenB + 1@ coefficients. Furthermore, we assume that \(Binv\)
-- is the inverse of the reverse of \(B\) mod
-- \(x^{\operatorname{len}(B)}\). The algorithm used is to call
-- @div_newton_n_preinv@ and then multiply out and compute the remainder.
foreign import ccall "fq_poly.h _fq_poly_divrem_newton_n_preinv"
  _fq_poly_divrem_newton_n_preinv :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO ()

-- -- | /fq_poly_divrem_newton_preinv/ /Q/ /R/ /A/ /B/ /Binv/ /ctx/ 
-- --
-- -- Computes \(Q\) and \(R\) such that \(A = BQ + R\) with
-- -- \(\operatorname{len}(R) <
-- -- \operatorname{len}(B)\). We assume \(Binv\) is the inverse of the
-- -- reverse of \(B\) mod \(x^{\operatorname{len}(B)}\).
-- -- 
-- -- It is required that the length of \(A\) is less than or equal to 2*the
-- -- length of \(B\) - 2.
-- -- 
-- -- The algorithm used is to call @div_newton_n@ and then multiply out and
-- -- compute the remainder.
-- foreign import ccall "fq_poly.h fq_poly_divrem_newton_preinv"
--   fq_poly_divrem_newton_preinv :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_inv_series_newton/ /Qinv/ /Q/ /n/ /ctx/ 
--
-- Given @Q@ of length @n@ whose constant coefficient is invertible modulo
-- the given modulus, find a polynomial @Qinv@ of length @n@ such that
-- @Q * Qinv@ is @1@ modulo \(x^n\). Requires @n > 0@. This function can be
-- viewed as inverting a power series via Newton iteration.
foreign import ccall "fq_poly.h _fq_poly_inv_series_newton"
  _fq_poly_inv_series_newton :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_inv_series_newton/ /Qinv/ /Q/ /n/ /ctx/ 
--
-- Given @Q@ find @Qinv@ such that @Q * Qinv@ is @1@ modulo \(x^n\). The
-- constant coefficient of @Q@ must be invertible modulo the modulus of
-- @Q@. An exception is raised if this is not the case or if @n = 0@. This
-- function can be viewed as inverting a power series via Newton iteration.
foreign import ccall "fq_poly.h fq_poly_inv_series_newton"
  fq_poly_inv_series_newton :: Ptr CFqPoly -> Ptr CFqPoly -> CLong -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_inv_series/ /Qinv/ /Q/ /n/ /ctx/ 
--
-- Given @Q@ of length @n@ whose constant coefficient is invertible modulo
-- the given modulus, find a polynomial @Qinv@ of length @n@ such that
-- @Q * Qinv@ is @1@ modulo \(x^n\). Requires @n > 0@.
foreign import ccall "fq_poly.h _fq_poly_inv_series"
  _fq_poly_inv_series :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_inv_series/ /Qinv/ /Q/ /n/ /ctx/ 
--
-- Given @Q@ find @Qinv@ such that @Q * Qinv@ is @1@ modulo \(x^n\). The
-- constant coefficient of @Q@ must be invertible modulo the modulus of
-- @Q@. An exception is raised if this is not the case or if @n = 0@.
foreign import ccall "fq_poly.h fq_poly_inv_series"
  fq_poly_inv_series :: Ptr CFqPoly -> Ptr CFqPoly -> CLong -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_div_series/ /Q/ /A/ /Alen/ /B/ /Blen/ /n/ /ctx/ 
--
-- Set @(Q, n)@ to the quotient of the series @(A, Alen@) and @(B, Blen)@
-- assuming @Alen, Blen \<= n@. We assume the bottom coefficient of @B@ is
-- invertible.
foreign import ccall "fq_poly.h _fq_poly_div_series"
  _fq_poly_div_series :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_div_series/ /Q/ /A/ /B/ /n/ /ctx/ 
--
-- Set \(Q\) to the quotient of the series \(A\) by \(B\), thinking of the
-- series as though they were of length \(n\). We assume that the bottom
-- coefficient of \(B\) is invertible.
foreign import ccall "fq_poly.h fq_poly_div_series"
  fq_poly_div_series :: Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> Ptr CFmpzModPoly -> CLong -> Ptr CFqCtx -> IO ()

-- Greatest common divisor -----------------------------------------------------

-- | /fq_poly_gcd/ /rop/ /op1/ /op2/ /ctx/ 
--
-- Sets @rop@ to the greatest common divisor of @op1@ and @op2@, using the
-- either the Euclidean or HGCD algorithm. The GCD of zero polynomials is
-- defined to be zero, whereas the GCD of the zero polynomial and some
-- other polynomial \(P\) is defined to be \(P\). Except in the case where
-- the GCD is zero, the GCD \(G\) is made monic.
foreign import ccall "fq_poly.h fq_poly_gcd"
  fq_poly_gcd :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_gcd/ /G/ /A/ /lenA/ /B/ /lenB/ /ctx/ 
--
-- Computes the GCD of \(A\) of length @lenA@ and \(B\) of length @lenB@,
-- where @lenA >= lenB > 0@ and sets \(G\) to it. The length of the GCD
-- \(G\) is returned by the function. No attempt is made to make the GCD
-- monic. It is required that \(G\) have space for @lenB@ coefficients.
foreign import ccall "fq_poly.h _fq_poly_gcd"
  _fq_poly_gcd :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO CLong

-- | /_fq_poly_gcd_euclidean_f/ /f/ /G/ /A/ /lenA/ /B/ /lenB/ /ctx/ 
--
-- Either sets \(f = 1\) and \(G\) to the greatest common divisor of
-- \((A,\operatorname{len}(A))\) and \((B, \operatorname{len}(B))\) and
-- returns its length, or sets \(f\) to a non-trivial factor of the modulus
-- of @ctx@ and leaves the contents of the vector \((G, lenB)\) undefined.
-- 
-- Assumes that \(\operatorname{len}(A) \geq \operatorname{len}(B) > 0\)
-- and that the vector \(G\) has space for sufficiently many coefficients.
foreign import ccall "fq_poly.h _fq_poly_gcd_euclidean_f"
  _fq_poly_gcd_euclidean_f :: Ptr CFq -> Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO CLong

-- | /fq_poly_gcd_euclidean_f/ /f/ /G/ /A/ /B/ /ctx/ 
--
-- Either sets \(f = 1\) and \(G\) to the greatest common divisor of \(A\)
-- and \(B\) or sets \(f\) to a factor of the modulus of @ctx@.
foreign import ccall "fq_poly.h fq_poly_gcd_euclidean_f"
  fq_poly_gcd_euclidean_f :: Ptr CFq -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_xgcd/ /G/ /S/ /T/ /A/ /lenA/ /B/ /lenB/ /ctx/ 
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
foreign import ccall "fq_poly.h _fq_poly_xgcd"
  _fq_poly_xgcd :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO CLong

-- | /fq_poly_xgcd/ /G/ /S/ /T/ /A/ /B/ /ctx/ 
--
-- Computes the GCD of \(A\) and \(B\). The GCD of zero polynomials is
-- defined to be zero, whereas the GCD of the zero polynomial and some
-- other polynomial \(P\) is defined to be \(P\). Except in the case where
-- the GCD is zero, the GCD \(G\) is made monic.
-- 
-- Polynomials @S@ and @T@ are computed such that @S*A + T*B = G@. The
-- length of @S@ will be at most @lenB@ and the length of @T@ will be at
-- most @lenA@.
foreign import ccall "fq_poly.h fq_poly_xgcd"
  fq_poly_xgcd :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_xgcd_euclidean_f/ /f/ /G/ /S/ /T/ /A/ /lenA/ /B/ /lenB/ /invB/ /ctx/ 
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
foreign import ccall "fq_poly.h _fq_poly_xgcd_euclidean_f"
  _fq_poly_xgcd_euclidean_f :: Ptr CFq -> Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> CLong -> Ptr CFmpz -> Ptr CFqCtx -> IO CLong

-- | /fq_poly_xgcd_euclidean_f/ /f/ /G/ /S/ /T/ /A/ /B/ /ctx/ 
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
foreign import ccall "fq_poly.h fq_poly_xgcd_euclidean_f"
  fq_poly_xgcd_euclidean_f :: Ptr CFq -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- Divisibility testing --------------------------------------------------------

-- | /_fq_poly_divides/ /Q/ /A/ /lenA/ /B/ /lenB/ /invB/ /ctx/ 
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
foreign import ccall "fq_poly.h _fq_poly_divides"
  _fq_poly_divides :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> CLong -> Ptr CFq -> Ptr CFqCtx -> IO CInt

-- | /fq_poly_divides/ /Q/ /A/ /B/ /ctx/ 
--
-- Returns \(1\) if \(B\) divides \(A\) exactly and sets \(Q\) to the
-- quotient, otherwise returns \(0\).
-- 
-- This function is currently unoptimised and provided for convenience
-- only.
foreign import ccall "fq_poly.h fq_poly_divides"
  fq_poly_divides :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO CInt

-- Derivative ------------------------------------------------------------------

-- | /_fq_poly_derivative/ /rop/ /op/ /len/ /ctx/ 
--
-- Sets @(rop, len - 1)@ to the derivative of @(op, len)@. Also handles the
-- cases where @len@ is \(0\) or \(1\) correctly. Supports aliasing of
-- @rop@ and @op@.
foreign import ccall "fq_poly.h _fq_poly_derivative"
  _fq_poly_derivative :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_derivative/ /rop/ /op/ /ctx/ 
--
-- Sets @rop@ to the derivative of @op@.
foreign import ccall "fq_poly.h fq_poly_derivative"
  fq_poly_derivative :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- Square root -----------------------------------------------------------------

-- | /_fq_poly_invsqrt_series/ /g/ /h/ /n/ /mod/ 
--
-- Set the first \(n\) terms of \(g\) to the series expansion of
-- \(1/\sqrt{h}\). It is assumed that \(n > 0\), that \(h\) has constant
-- term 1 and that \(h\) is zero-padded as necessary to length \(n\).
-- Aliasing is not permitted.
foreign import ccall "fq_poly.h _fq_poly_invsqrt_series"
  _fq_poly_invsqrt_series :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_invsqrt_series/ /g/ /h/ /n/ /ctx/ 
--
-- Set \(g\) to the series expansion of \(1/\sqrt{h}\) to order \(O(x^n)\).
-- It is assumed that \(h\) has constant term 1.
foreign import ccall "fq_poly.h fq_poly_invsqrt_series"
  fq_poly_invsqrt_series :: Ptr CFqPoly -> Ptr CFqPoly -> CLong -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_sqrt_series/ /g/ /h/ /n/ /ctx/ 
--
-- Set the first \(n\) terms of \(g\) to the series expansion of
-- \(\sqrt{h}\). It is assumed that \(n > 0\), that \(h\) has constant term
-- 1 and that \(h\) is zero-padded as necessary to length \(n\). Aliasing
-- is not permitted.
foreign import ccall "fq_poly.h _fq_poly_sqrt_series"
  _fq_poly_sqrt_series :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_sqrt_series/ /g/ /h/ /n/ /ctx/ 
--
-- Set \(g\) to the series expansion of \(\sqrt{h}\) to order \(O(x^n)\).
-- It is assumed that \(h\) has constant term 1.
foreign import ccall "fq_poly.h fq_poly_sqrt_series"
  fq_poly_sqrt_series :: Ptr CFqPoly -> Ptr CFqPoly -> CLong -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_sqrt/ /s/ /p/ /n/ /mod/ 
--
-- If @(p, n)@ is a perfect square, sets @(s, n \/ 2 + 1)@ to a square root
-- of \(p\) and returns 1. Otherwise returns 0.
foreign import ccall "fq_poly.h _fq_poly_sqrt"
  _fq_poly_sqrt :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO CInt

-- | /fq_poly_sqrt/ /s/ /p/ /mod/ 
--
-- If \(p\) is a perfect square, sets \(s\) to a square root of \(p\) and
-- returns 1. Otherwise returns 0.
foreign import ccall "fq_poly.h fq_poly_sqrt"
  fq_poly_sqrt :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO CInt

-- Evaluation ------------------------------------------------------------------

-- | /_fq_poly_evaluate_fq/ /rop/ /op/ /len/ /a/ /ctx/ 
--
-- Sets @rop@ to @(op, len)@ evaluated at \(a\).
-- 
-- Supports zero padding. There are no restrictions on @len@, that is,
-- @len@ is allowed to be zero, too.
foreign import ccall "fq_poly.h _fq_poly_evaluate_fq"
  _fq_poly_evaluate_fq :: Ptr CFq -> Ptr (Ptr CFq) -> CLong -> Ptr CFq -> Ptr CFqCtx -> IO ()

-- | /fq_poly_evaluate_fq/ /rop/ /f/ /a/ /ctx/ 
--
-- Sets @rop@ to the value of \(f(a)\).
-- 
-- As the coefficient ring \(\mathbf{F}_q\) is finite, Horner\'s method is
-- sufficient.
foreign import ccall "fq_poly.h fq_poly_evaluate_fq"
  fq_poly_evaluate_fq :: Ptr CFq -> Ptr CFqPoly -> Ptr CFq -> Ptr CFqCtx -> IO ()

-- Composition -----------------------------------------------------------------

-- | /_fq_poly_compose/ /rop/ /op1/ /len1/ /op2/ /len2/ /ctx/ 
--
-- Sets @rop@ to the composition of @(op1, len1)@ and @(op2, len2)@.
-- 
-- Assumes that @rop@ has space for @(len1-1)*(len2-1) + 1@ coefficients.
-- Assumes that @op1@ and @op2@ are non-zero polynomials. Does not support
-- aliasing between any of the inputs and the output.
foreign import ccall "fq_poly.h _fq_poly_compose"
  _fq_poly_compose :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_compose/ /rop/ /op1/ /op2/ /ctx/ 
--
-- Sets @rop@ to the composition of @op1@ and @op2@. To be precise about
-- the order of composition, denoting @rop@, @op1@, and @op2@ by \(f\),
-- \(g\), and \(h\), respectively, sets \(f(t) = g(h(t))\).
foreign import ccall "fq_poly.h fq_poly_compose"
  fq_poly_compose :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_compose_mod_horner/ /res/ /f/ /lenf/ /g/ /h/ /lenh/ /ctx/ 
--
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero and that the length of \(g\) is one less than the
-- length of \(h\) (possibly with zero padding). The output is not allowed
-- to be aliased with any of the inputs.
-- 
-- The algorithm used is Horner\'s rule.
foreign import ccall "fq_poly.h _fq_poly_compose_mod_horner"
  _fq_poly_compose_mod_horner :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_compose_mod_horner/ /res/ /f/ /g/ /h/ /ctx/ 
--
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero. The algorithm used is Horner\'s rule.
foreign import ccall "fq_poly.h fq_poly_compose_mod_horner"
  fq_poly_compose_mod_horner :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_compose_mod_horner_preinv/ /res/ /f/ /lenf/ /g/ /h/ /lenh/ /hinv/ /lenhiv/ /ctx/ 
--
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero and that the length of \(g\) is one less than the
-- length of \(h\) (possibly with zero padding). We also require that the
-- length of \(f\) is less than the length of \(h\). Furthermore, we
-- require @hinv@ to be the inverse of the reverse of @h@. The output is
-- not allowed to be aliased with any of the inputs.
-- 
-- The algorithm used is Horner\'s rule.
foreign import ccall "fq_poly.h _fq_poly_compose_mod_horner_preinv"
  _fq_poly_compose_mod_horner_preinv :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_compose_mod_horner_preinv/ /res/ /f/ /g/ /h/ /hinv/ /ctx/ 
--
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero and that \(f\) has smaller degree than \(h\).
-- Furthermore, we require @hinv@ to be the inverse of the reverse of @h@.
-- The algorithm used is Horner\'s rule.
foreign import ccall "fq_poly.h fq_poly_compose_mod_horner_preinv"
  fq_poly_compose_mod_horner_preinv :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_compose_mod_brent_kung/ /res/ /f/ /lenf/ /g/ /h/ /lenh/ /ctx/ 
--
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero and that the length of \(g\) is one less than the
-- length of \(h\) (possibly with zero padding). We also require that the
-- length of \(f\) is less than the length of \(h\). The output is not
-- allowed to be aliased with any of the inputs.
-- 
-- The algorithm used is the Brent-Kung matrix algorithm.
foreign import ccall "fq_poly.h _fq_poly_compose_mod_brent_kung"
  _fq_poly_compose_mod_brent_kung :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_compose_mod_brent_kung/ /res/ /f/ /g/ /h/ /ctx/ 
--
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero and that \(f\) has smaller degree than \(h\). The
-- algorithm used is the Brent-Kung matrix algorithm.
foreign import ccall "fq_poly.h fq_poly_compose_mod_brent_kung"
  fq_poly_compose_mod_brent_kung :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_compose_mod_brent_kung_preinv/ /res/ /f/ /lenf/ /g/ /h/ /lenh/ /hinv/ /lenhiv/ /ctx/ 
--
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero and that the length of \(g\) is one less than the
-- length of \(h\) (possibly with zero padding). We also require that the
-- length of \(f\) is less than the length of \(h\). Furthermore, we
-- require @hinv@ to be the inverse of the reverse of @h@. The output is
-- not allowed to be aliased with any of the inputs.
-- 
-- The algorithm used is the Brent-Kung matrix algorithm.
foreign import ccall "fq_poly.h _fq_poly_compose_mod_brent_kung_preinv"
  _fq_poly_compose_mod_brent_kung_preinv :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_compose_mod_brent_kung_preinv/ /res/ /f/ /g/ /h/ /hinv/ /ctx/ 
--
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero and that \(f\) has smaller degree than \(h\).
-- Furthermore, we require @hinv@ to be the inverse of the reverse of @h@.
-- The algorithm used is the Brent-Kung matrix algorithm.
foreign import ccall "fq_poly.h fq_poly_compose_mod_brent_kung_preinv"
  fq_poly_compose_mod_brent_kung_preinv :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_compose_mod/ /res/ /f/ /lenf/ /g/ /h/ /lenh/ /ctx/ 
--
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero and that the length of \(g\) is one less than the
-- length of \(h\) (possibly with zero padding). The output is not allowed
-- to be aliased with any of the inputs.
foreign import ccall "fq_poly.h _fq_poly_compose_mod"
  _fq_poly_compose_mod :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_compose_mod/ /res/ /f/ /g/ /h/ /ctx/ 
--
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero.
foreign import ccall "fq_poly.h fq_poly_compose_mod"
  fq_poly_compose_mod :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_compose_mod_preinv/ /res/ /f/ /lenf/ /g/ /h/ /lenh/ /hinv/ /lenhiv/ /ctx/ 
--
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero and that the length of \(g\) is one less than the
-- length of \(h\) (possibly with zero padding). We also require that the
-- length of \(f\) is less than the length of \(h\). Furthermore, we
-- require @hinv@ to be the inverse of the reverse of @h@. The output is
-- not allowed to be aliased with any of the inputs.
foreign import ccall "fq_poly.h _fq_poly_compose_mod_preinv"
  _fq_poly_compose_mod_preinv :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_compose_mod_preinv/ /res/ /f/ /g/ /h/ /hinv/ /ctx/ 
--
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that
-- \(h\) is nonzero and that \(f\) has smaller degree than \(h\).
-- Furthermore, we require @hinv@ to be the inverse of the reverse of @h@.
foreign import ccall "fq_poly.h fq_poly_compose_mod_preinv"
  fq_poly_compose_mod_preinv :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_reduce_matrix_mod_poly/ /A/ /B/ /f/ /ctx/ 
--
-- Sets the ith row of @A@ to the reduction of the ith row of \(B\) modulo
-- \(f\) for \(i=1,\ldots,\sqrt{\deg(f)}\). We require \(B\) to be at least
-- a \(\sqrt{\deg(f)}\times \deg(f)\) matrix and \(f\) to be nonzero.
foreign import ccall "fq_poly.h _fq_poly_reduce_matrix_mod_poly"
  _fq_poly_reduce_matrix_mod_poly :: Ptr CFqMat -> Ptr CFqMat -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_precompute_matrix/ /A/ /f/ /g/ /leng/ /ginv/ /lenginv/ /ctx/ 
--
-- Sets the ith row of @A@ to \(f^i\) modulo \(g\) for
-- \(i=1,\ldots,\sqrt{\deg(g)}\). We require \(A\) to be a
-- \(\sqrt{\deg(g)}\times \deg(g)\) matrix. We require @ginv@ to be the
-- inverse of the reverse of @g@ and \(g\) to be nonzero.
foreign import ccall "fq_poly.h _fq_poly_precompute_matrix"
  _fq_poly_precompute_matrix :: Ptr CFqMat -> Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_precompute_matrix/ /A/ /f/ /g/ /ginv/ /ctx/ 
--
-- Sets the ith row of @A@ to \(f^i\) modulo \(g\) for
-- \(i=1,\ldots,\sqrt{\deg(g)}\). We require \(A\) to be a
-- \(\sqrt{\deg(g)}\times \deg(g)\) matrix. We require @ginv@ to be the
-- inverse of the reverse of @g@.
foreign import ccall "fq_poly.h fq_poly_precompute_matrix"
  fq_poly_precompute_matrix :: Ptr CFqMat -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /_fq_poly_compose_mod_brent_kung_precomp_preinv/ /res/ /f/ /lenf/ /A/ /h/ /lenh/ /hinv/ /lenhinv/ /ctx/ 
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
foreign import ccall "fq_poly.h _fq_poly_compose_mod_brent_kung_precomp_preinv"
  _fq_poly_compose_mod_brent_kung_precomp_preinv :: Ptr (Ptr CFq) -> Ptr (Ptr CFq) -> CLong -> Ptr CFqMat -> Ptr (Ptr CFq) -> CLong -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_compose_mod_brent_kung_precomp_preinv/ /res/ /f/ /A/ /h/ /hinv/ /ctx/ 
--
-- Sets @res@ to the composition \(f(g)\) modulo \(h\). We require that the
-- ith row of \(A\) contains \(g^i\) for \(i=1,\ldots,\sqrt{\deg(h)}\),
-- i.e. \(A\) is a \(\sqrt{\deg(h)}\times
-- \deg(h)\) matrix. We require that \(h\) is nonzero and that \(f\) has
-- smaller degree than \(h\). Furthermore, we require @hinv@ to be the
-- inverse of the reverse of @h@. This version of Brent-Kung modular
-- composition is particularly useful if one has to perform several modular
-- composition of the form \(f(g)\) modulo \(h\) for fixed \(g\) and \(h\).
foreign import ccall "fq_poly.h fq_poly_compose_mod_brent_kung_precomp_preinv"
  fq_poly_compose_mod_brent_kung_precomp_preinv :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqMat -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- Output ----------------------------------------------------------------------

-- | /_fq_poly_fprint_pretty/ /file/ /poly/ /len/ /x/ /ctx/ 
--
-- Prints the pretty representation of @(poly, len)@ to the stream @file@,
-- using the string @x@ to represent the indeterminate.
-- 
-- In case of success, returns a positive value. In case of failure,
-- returns a non-positive value.
foreign import ccall "fq_poly.h _fq_poly_fprint_pretty"
  _fq_poly_fprint_pretty :: Ptr CFile -> Ptr (Ptr CFq) -> CLong -> CString -> Ptr CFqCtx -> IO CInt

-- | /fq_poly_fprint_pretty/ /file/ /poly/ /x/ /ctx/ 
--
-- Prints the pretty representation of @poly@ to the stream @file@, using
-- the string @x@ to represent the indeterminate.
-- 
-- In case of success, returns a positive value. In case of failure,
-- returns a non-positive value.
foreign import ccall "fq_poly.h fq_poly_fprint_pretty"
  fq_poly_fprint_pretty :: Ptr CFile -> Ptr CFqPoly -> CString -> Ptr CFqCtx -> IO CInt

-- | /_fq_poly_print_pretty/ /poly/ /len/ /x/ /ctx/ 
--
-- Prints the pretty representation of @(poly, len)@ to @stdout@, using the
-- string @x@ to represent the indeterminate.
-- 
-- In case of success, returns a positive value. In case of failure,
-- returns a non-positive value.
foreign import ccall "fq_poly.h _fq_poly_print_pretty"
  _fq_poly_print_pretty :: Ptr (Ptr CFq) -> CLong -> CString -> Ptr CFqCtx -> IO CInt

-- | /fq_poly_print_pretty/ /poly/ /x/ /ctx/ 
--
-- Prints the pretty representation of @poly@ to @stdout@, using the string
-- @x@ to represent the indeterminate.
-- 
-- In case of success, returns a positive value. In case of failure,
-- returns a non-positive value.
fq_poly_print_pretty :: Ptr CFqPoly -> CString -> Ptr CFqCtx -> IO CInt
fq_poly_print_pretty poly var ctx = 
  printCStr (\poly -> fq_poly_get_str_pretty poly var ctx) poly
  
-- | /_fq_poly_fprint/ /file/ /poly/ /len/ /ctx/ 
--
-- Prints the pretty representation of @(poly, len)@ to the stream @file@.
-- 
-- In case of success, returns a positive value. In case of failure,
-- returns a non-positive value.
foreign import ccall "fq_poly.h _fq_poly_fprint"
  _fq_poly_fprint :: Ptr CFile -> Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO CInt

-- | /fq_poly_fprint/ /file/ /poly/ /ctx/ 
--
-- Prints the pretty representation of @poly@ to the stream @file@.
-- 
-- In case of success, returns a positive value. In case of failure,
-- returns a non-positive value.
foreign import ccall "fq_poly.h fq_poly_fprint"
  fq_poly_fprint :: Ptr CFile -> Ptr CFqPoly -> Ptr CFqCtx -> IO CInt
  
-- | /_fq_poly_print/ /poly/ /len/ /ctx/ 
--
-- Prints the pretty representation of @(poly, len)@ to @stdout@.
-- 
-- In case of success, returns a positive value. In case of failure,
-- returns a non-positive value.
foreign import ccall "fq_poly.h _fq_poly_print"
  _fq_poly_print :: Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO CInt

-- | /fq_poly_print/ /poly/ /ctx/ 
--
-- Prints the representation of @poly@ to @stdout@.
-- 
-- In case of success, returns a positive value. In case of failure,
-- returns a non-positive value.
fq_poly_print :: Ptr CFqPoly -> Ptr CFqCtx -> IO CInt
fq_poly_print poly ctx = printCStr (flip fq_poly_get_str ctx) poly
  
-- | /_fq_poly_get_str/ /poly/ /len/ /ctx/ 
--
-- Returns the plain FLINT string representation of the polynomial
-- @(poly, len)@.
foreign import ccall "fq_poly.h _fq_poly_get_str"
  _fq_poly_get_str :: Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO CString

-- | /fq_poly_get_str/ /poly/ /ctx/ 
--
-- Returns the plain FLINT string representation of the polynomial @poly@.
foreign import ccall "fq_poly.h fq_poly_get_str"
  fq_poly_get_str :: Ptr CFqPoly -> Ptr CFqCtx -> IO CString

-- | /_fq_poly_get_str_pretty/ /poly/ /len/ /x/ /ctx/ 
--
-- Returns a pretty representation of the polynomial @(poly, len)@ using
-- the null-terminated string @x@ as the variable name.
foreign import ccall "fq_poly.h _fq_poly_get_str_pretty"
  _fq_poly_get_str_pretty :: Ptr (Ptr CFq) -> CLong -> CString -> Ptr CFqCtx -> IO CString

-- | /fq_poly_get_str_pretty/ /poly/ /x/ /ctx/ 
--
-- Returns a pretty representation of the polynomial @poly@ using the
-- null-terminated string @x@ as the variable name
foreign import ccall "fq_poly.h fq_poly_get_str_pretty"
  fq_poly_get_str_pretty :: Ptr CFqPoly -> CString -> Ptr CFqCtx -> IO CString

-- Inflation and deflation -----------------------------------------------------

-- | /fq_poly_inflate/ /result/ /input/ /inflation/ /ctx/ 
--
-- Sets @result@ to the inflated polynomial \(p(x^n)\) where \(p\) is given
-- by @input@ and \(n\) is given by @inflation@.
foreign import ccall "fq_poly.h fq_poly_inflate"
  fq_poly_inflate :: Ptr CFqPoly -> Ptr CFqPoly -> CULong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_deflate/ /result/ /input/ /deflation/ /ctx/ 
--
-- Sets @result@ to the deflated polynomial \(p(x^{1/n})\) where \(p\) is
-- given by @input@ and \(n\) is given by @deflation@. Requires \(n > 0\).
foreign import ccall "fq_poly.h fq_poly_deflate"
  fq_poly_deflate :: Ptr CFqPoly -> Ptr CFqPoly -> CULong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_deflation/ /input/ /ctx/ 
--
-- Returns the largest integer by which @input@ can be deflated. As special
-- cases, returns 0 if @input@ is the zero polynomial and 1 of @input@ is a
-- constant polynomial.
foreign import ccall "fq_poly.h fq_poly_deflation"
  fq_poly_deflation :: Ptr CFqPoly -> Ptr CFqCtx -> IO CULong
