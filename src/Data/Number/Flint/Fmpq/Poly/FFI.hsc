
module Data.Number.Flint.Fmpq.Poly.FFI (
  -- * Univariate polynomials over the rational numbers
    FmpqPoly(..)
  , CFmpqPoly (..)
  , newFmpqPoly
  , withFmpqPoly
  , withNewFmpqPoly
  -- * Memory management
  , fmpq_poly_init
  , fmpq_poly_init2
  , fmpq_poly_realloc
  , fmpq_poly_fit_length
  , _fmpq_poly_set_length
  , fmpq_poly_clear
  , _fmpq_poly_normalise
  , _fmpq_poly_canonicalise
  , fmpq_poly_canonicalise
  , _fmpq_poly_is_canonical
  , fmpq_poly_is_canonical
  -- * Polynomial parameters
  , fmpq_poly_degree
  , fmpq_poly_length
  -- * Accessing the numerator and denominator
  , fmpq_poly_numref
  , fmpq_poly_denref
  , fmpq_poly_get_numerator
  , fmpq_poly_get_denominator
  -- * Random testing
  , fmpq_poly_randtest
  , fmpq_poly_randtest_unsigned
  , fmpq_poly_randtest_not_zero
  -- * Assignment, swap, negation
  , fmpq_poly_set
  , fmpq_poly_set_si
  , fmpq_poly_set_ui
  , fmpq_poly_set_fmpz
  , fmpq_poly_set_fmpq
  -- , fmpq_poly_set_mpz -- deprecated
  -- , fmpq_poly_set_mpq -- deprecated
  , fmpq_poly_set_fmpz_poly
  , fmpq_poly_set_nmod_poly
  , fmpq_poly_get_nmod_poly
  , fmpq_poly_get_nmod_poly_den
  -- , _fmpq_poly_set_array_mpq  -- deprecated
  -- , fmpq_poly_set_array_mpq   -- deprecated
  , _fmpq_poly_set_str
  , fmpq_poly_set_str
  , fmpq_poly_get_str
  , fmpq_poly_get_str_pretty
  , fmpq_poly_zero
  , fmpq_poly_one
  , fmpq_poly_neg
  , fmpq_poly_inv
  , fmpq_poly_swap
  , fmpq_poly_truncate
  , fmpq_poly_set_trunc
  , fmpq_poly_get_slice
  , fmpq_poly_reverse
  -- * Getting and setting coefficients
  , fmpq_poly_get_coeff_fmpz
  , fmpq_poly_get_coeff_fmpq
  -- , fmpq_poly_get_coeff_mpq
  , fmpq_poly_set_coeff_si
  , fmpq_poly_set_coeff_ui
  , fmpq_poly_set_coeff_fmpz
  , fmpq_poly_set_coeff_fmpq
  -- , fmpq_poly_set_coeff_mpz -- deprecated
  -- , fmpq_poly_set_coeff_mpq -- deprecated
  -- * Comparison
  , fmpq_poly_equal
  , _fmpq_poly_equal_trunc
  , fmpq_poly_equal_trunc
  , _fmpq_poly_cmp
  , fmpq_poly_cmp
  , fmpq_poly_is_one
  , fmpq_poly_is_zero
  , fmpq_poly_is_gen
  -- * Addition and subtraction
  , _fmpq_poly_add
  , _fmpq_poly_add_can
  , fmpq_poly_add
  , fmpq_poly_add_can
  , _fmpq_poly_add_series
  , _fmpq_poly_add_series_can
  , fmpq_poly_add_series
  , fmpq_poly_add_series_can
  , _fmpq_poly_sub
  , _fmpq_poly_sub_can
  , fmpq_poly_sub
  , fmpq_poly_sub_can
  , _fmpq_poly_sub_series
  , _fmpq_poly_sub_series_can
  , fmpq_poly_sub_series
  , fmpq_poly_sub_series_can
  -- * Scalar multiplication and division
  , _fmpq_poly_scalar_mul_si
  , _fmpq_poly_scalar_mul_ui
  , _fmpq_poly_scalar_mul_fmpz
  , _fmpq_poly_scalar_mul_fmpq
  , fmpq_poly_scalar_mul_si
  , fmpq_poly_scalar_mul_ui
  , fmpq_poly_scalar_mul_fmpz
  , fmpq_poly_scalar_mul_fmpq
  -- , fmpq_poly_scalar_mul_mpz -- deprecated
  -- , fmpq_poly_scalar_mul_mpq -- deprecated
  , _fmpq_poly_scalar_div_fmpz
  , _fmpq_poly_scalar_div_si
  , _fmpq_poly_scalar_div_ui
  , _fmpq_poly_scalar_div_fmpq
  , fmpq_poly_scalar_div_si
  , fmpq_poly_scalar_div_ui
  , fmpq_poly_scalar_div_fmpz
  , fmpq_poly_scalar_div_fmpq
  -- , fmpq_poly_scalar_div_mpz -- deprecated
  -- , fmpq_poly_scalar_div_mpq -- deprecated
  -- * Multiplication
  , _fmpq_poly_mul
  , fmpq_poly_mul
  , _fmpq_poly_mullow
  , fmpq_poly_mullow
  , fmpq_poly_addmul
  , fmpq_poly_submul
  -- * Powering
  , _fmpq_poly_pow
  , fmpq_poly_pow
  , _fmpq_poly_pow_trunc
  , fmpq_poly_pow_trunc
  -- * Shifting
  , fmpq_poly_shift_left
  , fmpq_poly_shift_right
  -- * Euclidean division
  , _fmpq_poly_divrem
  , fmpq_poly_divrem
  , _fmpq_poly_div
  , fmpq_poly_div
  , _fmpq_poly_rem
  , fmpq_poly_rem
  -- * Powering
  , _fmpq_poly_powers_precompute
  , fmpq_poly_powers_precompute
  , _fmpq_poly_powers_clear
  , fmpq_poly_powers_clear
  , _fmpq_poly_rem_powers_precomp
  , fmpq_poly_rem_powers_precomp
  -- * Divisibility testing
  , _fmpq_poly_divides
  , fmpq_poly_divides
  , fmpq_poly_remove
  -- * Power series division
  , _fmpq_poly_inv_series_newton
  , fmpq_poly_inv_series_newton
  , _fmpq_poly_inv_series
  , fmpq_poly_inv_series
  , _fmpq_poly_div_series
  , fmpq_poly_div_series
  -- * Greatest common divisor
  , _fmpq_poly_gcd
  , fmpq_poly_gcd
  , _fmpq_poly_xgcd
  , fmpq_poly_xgcd
  , _fmpq_poly_lcm
  , fmpq_poly_lcm
  , _fmpq_poly_resultant
  , fmpq_poly_resultant
  , fmpq_poly_resultant_div
  -- * Derivative and integral
  , _fmpq_poly_derivative
  , fmpq_poly_derivative
  , _fmpq_poly_nth_derivative
  , fmpq_poly_nth_derivative
  , _fmpq_poly_integral
  , fmpq_poly_integral
  -- * Square roots
  , _fmpq_poly_sqrt_series
  , fmpq_poly_sqrt_series
  , _fmpq_poly_invsqrt_series
  , fmpq_poly_invsqrt_series
  -- * Power sums
  , _fmpq_poly_power_sums
  , fmpq_poly_power_sums
  , _fmpq_poly_power_sums_to_poly
  , fmpq_poly_power_sums_to_fmpz_poly
  , fmpq_poly_power_sums_to_poly
  -- * Transcendental functions
  , _fmpq_poly_log_series
  , fmpq_poly_log_series
  , _fmpq_poly_exp_series
  , fmpq_poly_exp_series
  , _fmpq_poly_exp_expinv_series
  , fmpq_poly_exp_expinv_series
  , _fmpq_poly_atan_series
  , fmpq_poly_atan_series
  , _fmpq_poly_atanh_series
  , fmpq_poly_atanh_series
  , _fmpq_poly_asin_series
  , fmpq_poly_asin_series
  , _fmpq_poly_asinh_series
  , fmpq_poly_asinh_series
  , _fmpq_poly_tan_series
  , fmpq_poly_tan_series
  , _fmpq_poly_sin_series
  , fmpq_poly_sin_series
  , _fmpq_poly_cos_series
  , fmpq_poly_cos_series
  , _fmpq_poly_sin_cos_series
  , fmpq_poly_sin_cos_series
  , _fmpq_poly_sinh_series
  , fmpq_poly_sinh_series
  , _fmpq_poly_cosh_series
  , fmpq_poly_cosh_series
  , _fmpq_poly_sinh_cosh_series
  , fmpq_poly_sinh_cosh_series
  , _fmpq_poly_tanh_series
  , fmpq_poly_tanh_series
  -- * Orthogonal polynomials
  , _fmpq_poly_legendre_p
  , fmpq_poly_legendre_p
  , _fmpq_poly_laguerre_l
  , fmpq_poly_laguerre_l
  , _fmpq_poly_gegenbauer_c
  , fmpq_poly_gegenbauer_c
  -- * Evaluation
  , _fmpq_poly_evaluate_fmpz
  , fmpq_poly_evaluate_fmpz
  , _fmpq_poly_evaluate_fmpq
  , fmpq_poly_evaluate_fmpq
  -- , fmpq_poly_evaluate_mpz -- deprecated
  -- , fmpq_poly_evaluate_mpq -- deprecated
  -- * Interpolation
  , _fmpq_poly_interpolate_fmpz_vec
  , fmpq_poly_interpolate_fmpz_vec
  -- * Composition
  , _fmpq_poly_compose
  , fmpq_poly_compose
  , _fmpq_poly_rescale
  , fmpq_poly_rescale
  -- * Power series composition
  , _fmpq_poly_compose_series_horner
  , fmpq_poly_compose_series_horner
  , _fmpq_poly_compose_series_brent_kung
  , fmpq_poly_compose_series_brent_kung
  , _fmpq_poly_compose_series
  , fmpq_poly_compose_series
  -- * Power series reversion
  , _fmpq_poly_revert_series_lagrange
  , fmpq_poly_revert_series_lagrange
  , _fmpq_poly_revert_series_lagrange_fast
  , fmpq_poly_revert_series_lagrange_fast
  , _fmpq_poly_revert_series_newton
  , fmpq_poly_revert_series_newton
  , _fmpq_poly_revert_series
  , fmpq_poly_revert_series
  -- * Gaussian content
  , _fmpq_poly_content
  , fmpq_poly_content
  , _fmpq_poly_primitive_part
  , fmpq_poly_primitive_part
  , _fmpq_poly_is_monic
  , fmpq_poly_is_monic
  , _fmpq_poly_make_monic
  , fmpq_poly_make_monic
  -- * Square-free
  , fmpq_poly_is_squarefree
  -- * Input and output
  , _fmpq_poly_print
  , fmpq_poly_print
  , _fmpq_poly_print_pretty
  , fmpq_poly_print_pretty
  , _fmpq_poly_fprint
  , fmpq_poly_fprint
  , _fmpq_poly_fprint_pretty
  , fmpq_poly_fprint_pretty
  , fmpq_poly_read
  , fmpq_poly_fread
) where 

-- univariate polynomials over the rational numbers ----------------------------

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, nullPtr, plusPtr )
import Foreign.Storable
import Foreign.Marshal ( free )

import Data.Number.Flint.Flint

import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Poly
import Data.Number.Flint.Fmpq

import Data.Number.Flint.NMod.Types


#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpq.h>
#include <flint/fmpz_poly.h>
#include <flint/fmpq_poly.h>

-- fmpq_poly_t -----------------------------------------------------------------

data FmpqPoly = FmpqPoly {-# UNPACK #-} !(ForeignPtr CFmpqPoly)
data CFmpqPoly = CFmpqPoly (Ptr CFmpz) (Ptr CFmpz) CLong CLong

instance Storable CFmpqPoly where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fmpq_poly_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fmpq_poly_t}
  peek ptr = CFmpqPoly 
    <$> #{peek fmpq_poly_struct, coeffs} ptr
    <*> #{peek fmpq_poly_struct, den   } ptr
    <*> #{peek fmpq_poly_struct, alloc } ptr
    <*> #{peek fmpq_poly_struct, length} ptr
  poke = error "CFmpqPoly.poke: Not defined"

newFmpqPoly = do
  p <- mallocForeignPtr
  withForeignPtr p fmpq_poly_init
  addForeignPtrFinalizer p_fmpq_poly_clear p
  return $ FmpqPoly p

{-# INLINE withFmpqPoly #-}
withFmpqPoly (FmpqPoly p) f = do
  withForeignPtr p $ \fp -> f fp >>= return . (FmpqPoly p,)

withNewFmpqPoly f = do
  x <- newFmpqPoly
  withFmpqPoly x $ \x -> f x

-- fmpq_poly_powers_precomp_t --------------------------------------------------

-- | Data structure containing the /CFmpqPolyPowersPrecomp/ pointer
data FmpqPolyPowersPrecomp = FmpqPolyPowersPrecomp
  {-# UNPACK #-} !(ForeignPtr CFmpqPolyPowersPrecomp) 
type CFmpqPolyPowersPrecomp = CFlint FmpqPolyPowersPrecomp

-- | Data structure containing the /CFmpqPolyFactor/ pointer
data FmpqPolyFactor = FmpqPolyFactor
  {-# UNPACK #-} !(ForeignPtr CFmpqPolyFactor) 
type CFmpqPolyFactor = CFlint FmpqPolyFactor

-- Memory management -----------------------------------------------------------

-- | /fmpq_poly_init/ /poly/ 
-- 
-- Initialises the polynomial for use. The length is set to zero.
foreign import ccall "fmpq_poly.h fmpq_poly_init"
  fmpq_poly_init :: Ptr CFmpqPoly -> IO ()

-- | /fmpq_poly_init2/ /poly/ /alloc/ 
-- 
-- Initialises the polynomial with space for at least @alloc@ coefficients
-- and set the length to zero. The @alloc@ coefficients are all set to
-- zero.
foreign import ccall "fmpq_poly.h fmpq_poly_init2"
  fmpq_poly_init2 :: Ptr CFmpqPoly -> CLong -> IO ()

-- | /fmpq_poly_realloc/ /poly/ /alloc/ 
-- 
-- Reallocates the given polynomial to have space for @alloc@ coefficients.
-- If @alloc@ is zero then the polynomial is cleared and then
-- reinitialised. If the current length is greater than @alloc@ then @poly@
-- is first truncated to length @alloc@. Note that this might leave the
-- rational polynomial in non-canonical form.
foreign import ccall "fmpq_poly.h fmpq_poly_realloc"
  fmpq_poly_realloc :: Ptr CFmpqPoly -> CLong -> IO ()

-- | /fmpq_poly_fit_length/ /poly/ /len/ 
-- 
-- If @len@ is greater than the number of coefficients currently allocated,
-- then the polynomial is reallocated to have space for at least @len@
-- coefficients. No data is lost when calling this function. The function
-- efficiently deals with the case where @fit_length@ is called many times
-- in small increments by at least doubling the number of allocated
-- coefficients when @len@ is larger than the number of coefficients
-- currently allocated.
foreign import ccall "fmpq_poly.h fmpq_poly_fit_length"
  fmpq_poly_fit_length :: Ptr CFmpqPoly -> CLong -> IO ()

-- | /_fmpq_poly_set_length/ /poly/ /len/ 
-- 
-- Sets the length of the numerator polynomial to @len@, demoting
-- coefficients beyond the new length. Note that this method does not
-- guarantee that the rational polynomial is in canonical form.
foreign import ccall "fmpq_poly.h _fmpq_poly_set_length"
  _fmpq_poly_set_length :: Ptr CFmpqPoly -> CLong -> IO ()

-- | /fmpq_poly_clear/ /poly/ 
-- 
-- Clears the given polynomial, releasing any memory used. The polynomial
-- must be reinitialised in order to be used again.
foreign import ccall "fmpq_poly.h fmpq_poly_clear"
  fmpq_poly_clear :: Ptr CFmpqPoly -> IO ()

foreign import ccall "fmpq_poly.h &fmpq_poly_clear"
  p_fmpq_poly_clear :: FunPtr (Ptr CFmpqPoly -> IO ())

-- | /_fmpq_poly_normalise/ /poly/ 
-- 
-- Sets the length of @poly@ so that the top coefficient is non-zero. If
-- all coefficients are zero, the length is set to zero. Note that this
-- function does not guarantee the coprimality of the numerator polynomial
-- and the integer denominator.
foreign import ccall "fmpq_poly.h _fmpq_poly_normalise"
  _fmpq_poly_normalise :: Ptr CFmpqPoly -> IO ()

-- | /_fmpq_poly_canonicalise/ /poly/ /den/ /len/ 
-- 
-- Puts @(poly, den)@ of length @len@ into canonical form.
-- 
-- It is assumed that the array @poly@ contains a non-zero entry in
-- position @len - 1@ whenever @len > 0@. Assumes that @den@ is non-zero.
foreign import ccall "fmpq_poly.h _fmpq_poly_canonicalise"
  _fmpq_poly_canonicalise :: Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- | /fmpq_poly_canonicalise/ /poly/ 
-- 
-- Puts the polynomial @poly@ into canonical form. Firstly, the length is
-- set to the actual length of the numerator polynomial. For non-zero
-- polynomials, it is then ensured that the numerator and denominator are
-- coprime and that the denominator is positive. The canonical form of the
-- zero polynomial is a zero numerator polynomial and a one denominator.
foreign import ccall "fmpq_poly.h fmpq_poly_canonicalise"
  fmpq_poly_canonicalise :: Ptr CFmpqPoly -> IO ()

-- | /_fmpq_poly_is_canonical/ /poly/ /den/ /len/ 
-- 
-- Returns whether the polynomial is in canonical form.
foreign import ccall "fmpq_poly.h _fmpq_poly_is_canonical"
  _fmpq_poly_is_canonical :: Ptr CFmpz -> Ptr CFmpz -> CLong -> IO CInt

-- | /fmpq_poly_is_canonical/ /poly/ 
-- 
-- Returns whether the polynomial is in canonical form.
foreign import ccall "fmpq_poly.h fmpq_poly_is_canonical"
  fmpq_poly_is_canonical :: Ptr CFmpqPoly -> IO CInt

-- Polynomial parameters -------------------------------------------------------

-- | /fmpq_poly_degree/ /poly/ 
-- 
-- Returns the degree of @poly@, which is one less than its length, as a
-- @slong@.
foreign import ccall "fmpq_poly.h fmpq_poly_degree"
  fmpq_poly_degree :: Ptr CFmpqPoly -> IO CLong

-- | /fmpq_poly_length/ /poly/ 
-- 
-- Returns the length of @poly@.
foreign import ccall "fmpq_poly.h fmpq_poly_length"
  fmpq_poly_length :: Ptr CFmpqPoly -> IO CLong

-- Accessing the numerator and denominator -------------------------------------

-- | /fmpq_poly_numref/ /poly/ 
-- 
-- Returns a reference to the numerator polynomial as an array.
-- 
-- Note that, because of a delayed initialisation approach, this might be
-- @NULL@ for zero polynomials. This situation can be salvaged by calling
-- either @fmpq_poly_fit_length@ or @fmpq_poly_realloc@.
-- 
-- This function is implemented as a macro returning @(poly)->coeffs@.
fmpq_poly_numref :: Ptr CFmpqPoly -> IO (Ptr CFmpz)
fmpq_poly_numref poly = do
  CFmpqPoly coeffs _ _ _ <- peek poly
  return $ coeffs
  
-- | /fmpq_poly_denref/ /poly/ 
-- 
-- Returns a reference to the denominator as a @fmpz_t@. The integer is
-- guaranteed to be properly initialised.
-- 
-- This function is implemented as a macro returning @(poly)->den@.
fmpq_poly_denref :: Ptr CFmpqPoly -> IO (Ptr CFmpz)
fmpq_poly_denref poly = do
  CFmpqPoly _ den _ _ <- peek poly
  return $ den
  
-- | /fmpq_poly_get_numerator/ /res/ /poly/ 
-- 
-- Sets @res@ to the numerator of @poly@, e.g. the primitive part as an
-- @fmpz_poly_t@ if it is in canonical form .
foreign import ccall "fmpq_poly.h fmpq_poly_get_numerator"
  fmpq_poly_get_numerator :: Ptr CFmpzPoly -> Ptr CFmpqPoly -> IO ()

-- | /fmpq_poly_get_denominator/ /den/ /poly/ 
-- 
-- Sets @res@ to the denominator of @poly@.
foreign import ccall "fmpq_poly.h fmpq_poly_get_denominator"
  fmpq_poly_get_denominator :: Ptr CFmpz -> Ptr CFmpqPoly -> IO ()

-- Random testing --------------------------------------------------------------

-- The functions @fmpq_poly_randtest_foo@ provide random polynomials
-- suitable for testing. On an integer level, this means that long strings
-- of zeros and ones in the binary representation are favoured as well as
-- the special absolute values \(0\), \(1\), @COEFF_MAX@, and @WORD_MAX@.
-- On a polynomial level, the integer numerator has a reasonable chance to
-- have a non-trivial content.
--
-- | /fmpq_poly_randtest/ /f/ /state/ /len/ /bits/ 
-- 
-- Sets \(f\) to a random polynomial with coefficients up to the given
-- length and where each coefficient has up to the given number of bits.
-- The coefficients are signed randomly. One must call @flint_randinit@
-- before calling this function.
foreign import ccall "fmpq_poly.h fmpq_poly_randtest"
  fmpq_poly_randtest :: Ptr CFmpqPoly -> Ptr CFRandState -> CLong -> CFBitCnt -> IO ()

-- | /fmpq_poly_randtest_unsigned/ /f/ /state/ /len/ /bits/ 
-- 
-- Sets \(f\) to a random polynomial with coefficients up to the given
-- length and where each coefficient has up to the given number of bits.
-- One must call @flint_randinit@ before calling this function.
foreign import ccall "fmpq_poly.h fmpq_poly_randtest_unsigned"
  fmpq_poly_randtest_unsigned :: Ptr CFmpqPoly -> Ptr CFRandState -> CLong -> CFBitCnt -> IO ()

-- | /fmpq_poly_randtest_not_zero/ /f/ /state/ /len/ /bits/ 
-- 
-- As for @fmpq_poly_randtest@ except that @len@ and @bits@ may not be zero
-- and the polynomial generated is guaranteed not to be the zero
-- polynomial. One must call @flint_randinit@ before calling this function.
foreign import ccall "fmpq_poly.h fmpq_poly_randtest_not_zero"
  fmpq_poly_randtest_not_zero :: Ptr CFmpqPoly -> Ptr CFRandState -> CLong -> CFBitCnt -> IO ()

-- Assignment, swap, negation --------------------------------------------------

-- | /fmpq_poly_set/ /poly1/ /poly2/ 
-- 
-- Sets @poly1@ to equal @poly2@.
foreign import ccall "fmpq_poly.h fmpq_poly_set"
  fmpq_poly_set :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> IO ()

-- | /fmpq_poly_set_si/ /poly/ /x/ 
-- 
-- Sets @poly@ to the integer \(x\).
foreign import ccall "fmpq_poly.h fmpq_poly_set_si"
  fmpq_poly_set_si :: Ptr CFmpqPoly -> CLong -> IO ()

-- | /fmpq_poly_set_ui/ /poly/ /x/ 
-- 
-- Sets @poly@ to the integer \(x\).
foreign import ccall "fmpq_poly.h fmpq_poly_set_ui"
  fmpq_poly_set_ui :: Ptr CFmpqPoly -> CULong -> IO ()

-- | /fmpq_poly_set_fmpz/ /poly/ /x/ 
-- 
-- Sets @poly@ to the integer \(x\).
foreign import ccall "fmpq_poly.h fmpq_poly_set_fmpz"
  fmpq_poly_set_fmpz :: Ptr CFmpqPoly -> Ptr CFmpz -> IO ()

-- | /fmpq_poly_set_fmpq/ /poly/ /x/ 
-- 
-- Sets @poly@ to the rational \(x\), which is assumed to be given in
-- lowest terms.
foreign import ccall "fmpq_poly.h fmpq_poly_set_fmpq"
  fmpq_poly_set_fmpq :: Ptr CFmpqPoly -> Ptr CFmpq -> IO ()

-- -- | /fmpq_poly_set_mpz/ /poly/ /x/ 
-- -- 
-- -- Sets @poly@ to the integer \(x\).
-- foreign import ccall "fmpq_poly.h fmpq_poly_set_mpz"
--   fmpq_poly_set_mpz :: Ptr CFmpqPoly -> Ptr CMpz -> IO ()

-- -- | /fmpq_poly_set_mpq/ /poly/ /x/ 
-- -- 
-- -- Sets @poly@ to the rational \(x\), which is assumed to be given in
-- -- lowest terms.
-- foreign import ccall "fmpq_poly.h fmpq_poly_set_mpq"
--   fmpq_poly_set_mpq :: Ptr CFmpqPoly -> Ptr CMpq -> IO ()

-- | /fmpq_poly_set_fmpz_poly/ /rop/ /op/ 
-- 
-- Sets the rational polynomial @rop@ to the same value as the integer
-- polynomial @op@.
foreign import ccall "fmpq_poly.h fmpq_poly_set_fmpz_poly"
  fmpq_poly_set_fmpz_poly :: Ptr CFmpqPoly -> Ptr CFmpzPoly -> IO ()

-- | /fmpq_poly_set_nmod_poly/ /rop/ /op/ 
-- 
-- Sets the coefficients of @rop@ to the residues in @op@, normalised to
-- the interval \(-m/2 \le r < m/2\) where \(m\) is the modulus.
foreign import ccall "fmpq_poly.h fmpq_poly_set_nmod_poly"
  fmpq_poly_set_nmod_poly :: Ptr CFmpqPoly -> Ptr CNModPoly -> IO ()

-- | /fmpq_poly_get_nmod_poly/ /rop/ /op/ 
-- 
-- Sets the coefficients of @rop@ to the coefficients in the denominator
-- of@op@, reduced by the modulus of @rop@. The result is multiplied by the
-- inverse of the denominator of @op@. It is assumed that the reduction of
-- the denominator of @op@ is invertible.
foreign import ccall "fmpq_poly.h fmpq_poly_get_nmod_poly"
  fmpq_poly_get_nmod_poly :: Ptr CNModPoly -> Ptr CFmpqPoly -> IO ()

-- | /fmpq_poly_get_nmod_poly_den/ /rop/ /op/ /den/ 
-- 
-- Sets the coefficients of @rop@ to the coefficients in the denominator of
-- @op@, reduced by the modulus of @rop@. If @den == 1@, the result is
-- multiplied by the inverse of the denominator of @op@. In this case it is
-- assumed that the reduction of the denominator of @op@ is invertible.
foreign import ccall "fmpq_poly.h fmpq_poly_get_nmod_poly_den"
  fmpq_poly_get_nmod_poly_den :: Ptr CNModPoly -> Ptr CFmpqPoly -> CInt -> IO ()

-- -- | /_fmpq_poly_set_array_mpq/ /poly/ /den/ /a/ /n/ 
-- -- 
-- -- Sets @(poly, den)@ to the polynomial given by the first \(n \geq 1\)
-- -- coefficients in the array \(a\), from lowest degree to highest degree.
-- -- 
-- -- The result is only guaranteed to be in lowest terms if all input
-- -- coefficients are given in lowest terms.
-- foreign import ccall "fmpq_poly.h _fmpq_poly_set_array_mpq"
--   _fmpq_poly_set_array_mpq :: Ptr CFmpz -> Ptr CFmpz -> Ptr CMpq -> CLong -> IO ()

-- -- | /fmpq_poly_set_array_mpq/ /poly/ /a/ /n/ 
-- -- 
-- -- Sets @poly@ to the polynomial with coefficients as given in the array
-- -- \(a\) of length \(n \geq 0\), from lowest degree to highest degree.
-- -- 
-- -- The result is only guaranteed to be in canonical form if all input
-- -- coefficients are given in lowest terms.
-- foreign import ccall "fmpq_poly.h fmpq_poly_set_array_mpq"
--   fmpq_poly_set_array_mpq :: Ptr CFmpqPoly -> Ptr CMpq -> CLong -> IO ()

-- | /_fmpq_poly_set_str/ /poly/ /den/ /str/ /len/ 
-- 
-- Sets @(poly, den)@ to the polynomial specified by the null-terminated
-- string @str@ of @len@ coefficients. The input format is a sequence of
-- coefficients separated by one space.
-- 
-- The result is only guaranteed to be in lowest terms if all coefficients
-- in the input string are in lowest terms.
-- 
-- Returns \(0\) if no error occurred. Otherwise, returns -1 in which case
-- the resulting value of @(poly, den)@ is undefined. If @str@ is not
-- null-terminated, calling this method might result in a segmentation
-- fault.
foreign import ccall "fmpq_poly.h _fmpq_poly_set_str"
  _fmpq_poly_set_str :: Ptr CFmpz -> Ptr CFmpz -> CString -> CLong -> IO CInt

-- | /fmpq_poly_set_str/ /poly/ /str/ 
-- 
-- Sets @poly@ to the polynomial specified by the null-terminated string
-- @str@. The input format is the same as the output format of
-- @fmpq_poly_get_str@: the length given as a decimal integer, then two
-- spaces, then the list of coefficients separated by one space.
-- 
-- The result is only guaranteed to be in canonical form if all
-- coefficients in the input string are in lowest terms.
-- 
-- Returns \(0\) if no error occurred. Otherwise, returns -1 in which case
-- the resulting value of @poly@ is set to zero. If @str@ is not
-- null-terminated, calling this method might result in a segmentation
-- fault.
foreign import ccall "fmpq_poly.h fmpq_poly_set_str"
  fmpq_poly_set_str :: Ptr CFmpqPoly -> CString -> IO CInt

-- | /fmpq_poly_get_str/ /poly/ 
-- 
-- Returns the string representation of @poly@.
foreign import ccall "fmpq_poly.h fmpq_poly_get_str"
  fmpq_poly_get_str :: Ptr CFmpqPoly -> IO CString

-- | /fmpq_poly_get_str_pretty/ /poly/ /var/ 
-- 
-- Returns the pretty representation of @poly@, using the null-terminated
-- string @var@ not equal to @\"\\0\"@ as the variable name.
foreign import ccall "fmpq_poly.h fmpq_poly_get_str_pretty"
  fmpq_poly_get_str_pretty :: Ptr CFmpqPoly -> CString -> IO CString

-- | /fmpq_poly_zero/ /poly/ 
-- 
-- Sets @poly@ to zero.
foreign import ccall "fmpq_poly.h fmpq_poly_zero"
  fmpq_poly_zero :: Ptr CFmpqPoly -> IO ()

-- | /fmpq_poly_one/ /poly/ 
-- 
-- Sets @poly@ to the constant polynomial \(1\).
foreign import ccall "fmpq_poly.h fmpq_poly_one"
  fmpq_poly_one :: Ptr CFmpqPoly -> IO ()

-- | /fmpq_poly_neg/ /poly1/ /poly2/ 
-- 
-- Sets @poly1@ to the additive inverse of @poly2@.
foreign import ccall "fmpq_poly.h fmpq_poly_neg"
  fmpq_poly_neg :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> IO ()

-- | /fmpq_poly_inv/ /poly1/ /poly2/ 
-- 
-- Sets @poly1@ to the multiplicative inverse of @poly2@ if possible.
-- Otherwise, if @poly2@ is not a unit, leaves @poly1@ unmodified and calls
-- @abort@.
foreign import ccall "fmpq_poly.h fmpq_poly_inv"
  fmpq_poly_inv :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> IO ()

-- | /fmpq_poly_swap/ /poly1/ /poly2/ 
-- 
-- Efficiently swaps the polynomials @poly1@ and @poly2@.
foreign import ccall "fmpq_poly.h fmpq_poly_swap"
  fmpq_poly_swap :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> IO ()

-- | /fmpq_poly_truncate/ /poly/ /n/ 
-- 
-- If the current length of @poly@ is greater than \(n\), it is truncated
-- to the given length. Discarded coefficients are demoted, but they are
-- not necessarily set to zero.
foreign import ccall "fmpq_poly.h fmpq_poly_truncate"
  fmpq_poly_truncate :: Ptr CFmpqPoly -> CLong -> IO ()

-- | /fmpq_poly_set_trunc/ /res/ /poly/ /n/ 
-- 
-- Sets @res@ to a copy of @poly@, truncated to length @n@.
foreign import ccall "fmpq_poly.h fmpq_poly_set_trunc"
  fmpq_poly_set_trunc :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> IO ()

-- | /fmpq_poly_get_slice/ /rop/ /op/ /i/ /j/ 
-- 
-- Returns the slice with coefficients from \(x^i\) (including) to \(x^j\)
-- (excluding).
foreign import ccall "fmpq_poly.h fmpq_poly_get_slice"
  fmpq_poly_get_slice :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> CLong -> IO ()

-- | /fmpq_poly_reverse/ /res/ /poly/ /n/ 
-- 
-- This function considers the polynomial @poly@ to be of length \(n\),
-- notionally truncating and zero padding if required, and reverses the
-- result. Since the function normalises its result @res@ may be of length
-- less than \(n\).
foreign import ccall "fmpq_poly.h fmpq_poly_reverse"
  fmpq_poly_reverse :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> IO ()

-- Getting and setting coefficients --------------------------------------------

-- | /fmpq_poly_get_coeff_fmpz/ /x/ /poly/ /n/ 
-- 
-- Retrieves the \(n`th coefficient of the numerator of \)poly\`.
foreign import ccall "fmpq_poly.h fmpq_poly_get_coeff_fmpz"
  fmpq_poly_get_coeff_fmpz :: Ptr CFmpz -> Ptr CFmpqPoly -> CLong -> IO ()

-- | /fmpq_poly_get_coeff_fmpq/ /x/ /poly/ /n/ 
-- 
-- Retrieves the \(n`th coefficient of \)poly\`, in lowest terms.
foreign import ccall "fmpq_poly.h fmpq_poly_get_coeff_fmpq"
  fmpq_poly_get_coeff_fmpq :: Ptr CFmpq -> Ptr CFmpqPoly -> CLong -> IO ()

-- -- | /fmpq_poly_get_coeff_mpq/ /x/ /poly/ /n/ 
-- -- 
-- -- Retrieves the \(n`th coefficient of \)poly\`, in lowest terms.
-- foreign import ccall "fmpq_poly.h fmpq_poly_get_coeff_mpq"
--   fmpq_poly_get_coeff_mpq :: Ptr CMpq -> Ptr CFmpqPoly -> CLong -> IO ()

-- | /fmpq_poly_set_coeff_si/ /poly/ /n/ /x/ 
-- 
-- Sets the \(n`th coefficient in \)poly to the integer :math:\`x.
foreign import ccall "fmpq_poly.h fmpq_poly_set_coeff_si"
  fmpq_poly_set_coeff_si :: Ptr CFmpqPoly -> CLong -> CLong -> IO ()

-- | /fmpq_poly_set_coeff_ui/ /poly/ /n/ /x/ 
-- 
-- Sets the \(n`th coefficient in \)poly to the integer :math:\`x.
foreign import ccall "fmpq_poly.h fmpq_poly_set_coeff_ui"
  fmpq_poly_set_coeff_ui :: Ptr CFmpqPoly -> CLong -> CULong -> IO ()

-- | /fmpq_poly_set_coeff_fmpz/ /poly/ /n/ /x/ 
-- 
-- Sets the \(n`th coefficient in \)poly to the integer :math:\`x.
foreign import ccall "fmpq_poly.h fmpq_poly_set_coeff_fmpz"
  fmpq_poly_set_coeff_fmpz :: Ptr CFmpqPoly -> CLong -> Ptr CFmpz -> IO ()

-- | /fmpq_poly_set_coeff_fmpq/ /poly/ /n/ /x/ 
-- 
-- Sets the \(n`th coefficient in \)poly to the rational :math:\`x.
foreign import ccall "fmpq_poly.h fmpq_poly_set_coeff_fmpq"
  fmpq_poly_set_coeff_fmpq :: Ptr CFmpqPoly -> CLong -> Ptr CFmpq -> IO ()

-- -- | /fmpq_poly_set_coeff_mpz/ /rop/ /n/ /x/ 
-- -- 
-- -- Sets the \(n`th coefficient in \)poly to the integer :math:\`x.
-- foreign import ccall "fmpq_poly.h fmpq_poly_set_coeff_mpz"
--   fmpq_poly_set_coeff_mpz :: Ptr CFmpqPoly -> CLong -> Ptr CMpz -> IO ()

-- -- | /fmpq_poly_set_coeff_mpq/ /rop/ /n/ /x/ 
-- -- 
-- -- Sets the \(n`th coefficient in \)poly to the rational~\`x, which is
-- -- expected to be provided in lowest terms.
-- foreign import ccall "fmpq_poly.h fmpq_poly_set_coeff_mpq"
--   fmpq_poly_set_coeff_mpq :: Ptr CFmpqPoly -> CLong -> Ptr CMpq -> IO ()

-- Comparison ------------------------------------------------------------------

-- | /fmpq_poly_equal/ /poly1/ /poly2/ 
-- 
-- Returns \(1\) if @poly1@ is equal to @poly2@, otherwise returns~\`0\`.
foreign import ccall "fmpq_poly.h fmpq_poly_equal"
  fmpq_poly_equal :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> IO CInt

-- | /_fmpq_poly_equal_trunc/ /poly1/ /den1/ /len1/ /poly2/ /den2/ /len2/ /n/ 
-- 
-- Return \(1\) if @poly1@ and @poly2@ notionally truncated to length \(n\)
-- are equal, otherwise returns~\`0\`.
foreign import ccall "fmpq_poly.h _fmpq_poly_equal_trunc"
  _fmpq_poly_equal_trunc :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO CInt

-- | /fmpq_poly_equal_trunc/ /poly1/ /poly2/ /n/ 
-- 
-- Return \(1\) if @poly1@ and @poly2@ notionally truncated to length \(n\)
-- are equal, otherwise returns~\`0\`.
foreign import ccall "fmpq_poly.h fmpq_poly_equal_trunc"
  fmpq_poly_equal_trunc :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> IO CInt

-- | /_fmpq_poly_cmp/ /lpoly/ /lden/ /rpoly/ /rden/ /len/ 
-- 
-- Compares two non-zero polynomials, assuming they have the same length
-- @len > 0@.
-- 
-- The polynomials are expected to be provided in canonical form.
foreign import ccall "fmpq_poly.h _fmpq_poly_cmp"
  _fmpq_poly_cmp :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> IO CInt

-- | /fmpq_poly_cmp/ /left/ /right/ 
-- 
-- Compares the two polynomials @left@ and @right@.
-- 
-- Compares the two polynomials @left@ and @right@, returning \(-1\),
-- \(0\), or \(1\) as @left@ is less than, equal to, or greater than
-- @right@. The comparison is first done by the degree, and then, in case
-- of a tie, by the individual coefficients from highest to lowest.
foreign import ccall "fmpq_poly.h fmpq_poly_cmp"
  fmpq_poly_cmp :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> IO CInt

-- | /fmpq_poly_is_one/ /poly/ 
-- 
-- Returns \(1\) if @poly@ is the constant polynomial~\`1\`, otherwise
-- returns \(0\).
foreign import ccall "fmpq_poly.h fmpq_poly_is_one"
  fmpq_poly_is_one :: Ptr CFmpqPoly -> IO CInt

-- | /fmpq_poly_is_zero/ /poly/ 
-- 
-- Returns \(1\) if @poly@ is the zero polynomial, otherwise returns \(0\).
foreign import ccall "fmpq_poly.h fmpq_poly_is_zero"
  fmpq_poly_is_zero :: Ptr CFmpqPoly -> IO CInt

-- | /fmpq_poly_is_gen/ /poly/ 
-- 
-- Returns \(1\) if @poly@ is the degree \(1\) polynomial \(x\), otherwise
-- returns \(0\).
foreign import ccall "fmpq_poly.h fmpq_poly_is_gen"
  fmpq_poly_is_gen :: Ptr CFmpqPoly -> IO CInt

-- Addition and subtraction ----------------------------------------------------

-- | /_fmpq_poly_add/ /rpoly/ /rden/ /poly1/ /den1/ /len1/ /poly2/ /den2/ /len2/ 
-- 
-- Forms the sum @(rpoly, rden)@ of @(poly1, den1, len1)@ and
-- @(poly2, den2, len2)@, placing the result into canonical form.
-- 
-- Assumes that @rpoly@ is an array of length the maximum of @len1@ and
-- @len2@. The input operands are assumed to be in canonical form and are
-- also allowed to be of length~\`0\`.
-- 
-- @(rpoly, rden)@ and @(poly1, den1)@ may be aliased, but @(rpoly, rden)@
-- and @(poly2, den2)@ may /not/ be aliased.
foreign import ccall "fmpq_poly.h _fmpq_poly_add"
  _fmpq_poly_add :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- | /_fmpq_poly_add_can/ /rpoly/ /rden/ /poly1/ /den1/ /len1/ /poly2/ /den2/ /len2/ /can/ 
-- 
-- As per @_fmpq_poly_add@ except that one can specify whether to
-- canonicalise the output or not. This function is intended to be used
-- with weak canonicalisation to prevent explosion in memory usage. It
-- exists for performance reasons.
foreign import ccall "fmpq_poly.h _fmpq_poly_add_can"
  _fmpq_poly_add_can :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CInt -> IO ()

-- | /fmpq_poly_add/ /res/ /poly1/ /poly2/ 
-- 
-- Sets @res@ to the sum of @poly1@ and @poly2@, using Henrici\'s
-- algorithm.
foreign import ccall "fmpq_poly.h fmpq_poly_add"
  fmpq_poly_add :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> Ptr CFmpqPoly -> IO ()

-- | /fmpq_poly_add_can/ /res/ /poly1/ /poly2/ /can/ 
-- 
-- As per @fmpq_poly_add@ except that one can specify whether to
-- canonicalise the output or not. This function is intended to be used
-- with weak canonicalisation to prevent explosion in memory usage. It
-- exists for performance reasons.
foreign import ccall "fmpq_poly.h fmpq_poly_add_can"
  fmpq_poly_add_can :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> Ptr CFmpqPoly -> CInt -> IO ()

-- | /_fmpq_poly_add_series/ /rpoly/ /rden/ /poly1/ /den1/ /len1/ /poly2/ /den2/ /len2/ /n/ 
-- 
-- As per @_fmpq_poly_add@ but the inputs are first notionally truncated to
-- length \(n\). If \(n\) is less than @len1@ or @len2@ then the output
-- only needs space for \(n\) coefficients. We require \(n \geq 0\).
foreign import ccall "fmpq_poly.h _fmpq_poly_add_series"
  _fmpq_poly_add_series :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

-- | /_fmpq_poly_add_series_can/ /rpoly/ /rden/ /poly1/ /den1/ /len1/ /poly2/ /den2/ /len2/ /n/ /can/ 
-- 
-- As per @_fmpq_poly_add_can@ but the inputs are first notionally
-- truncated to length \(n\). If \(n\) is less than @len1@ or @len2@ then
-- the output only needs space for \(n\) coefficients. We require
-- \(n \geq 0\).
foreign import ccall "fmpq_poly.h _fmpq_poly_add_series_can"
  _fmpq_poly_add_series_can :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> CInt -> IO ()

-- | /fmpq_poly_add_series/ /res/ /poly1/ /poly2/ /n/ 
-- 
-- As per @fmpq_poly_add@ but the inputs are first notionally truncated to
-- length \(n\).
foreign import ccall "fmpq_poly.h fmpq_poly_add_series"
  fmpq_poly_add_series :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> IO ()

-- | /fmpq_poly_add_series_can/ /res/ /poly1/ /poly2/ /n/ /can/ 
-- 
-- As per @fmpq_poly_add_can@ but the inputs are first notionally truncated
-- to length \(n\).
foreign import ccall "fmpq_poly.h fmpq_poly_add_series_can"
  fmpq_poly_add_series_can :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> CInt -> IO ()

-- | /_fmpq_poly_sub/ /rpoly/ /rden/ /poly1/ /den1/ /len1/ /poly2/ /den2/ /len2/ 
-- 
-- Forms the difference @(rpoly, rden)@ of @(poly1, den1, len1)@ and
-- @(poly2, den2, len2)@, placing the result into canonical form.
-- 
-- Assumes that @rpoly@ is an array of length the maximum of @len1@ and
-- @len2@. The input operands are assumed to be in canonical form and are
-- also allowed to be of length~\`0\`.
-- 
-- @(rpoly, rden)@ and @(poly1, den1, len1)@ may be aliased, but
-- @(rpoly, rden)@ and @(poly2, den2, len2)@ may /not/ be aliased.
foreign import ccall "fmpq_poly.h _fmpq_poly_sub"
  _fmpq_poly_sub :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- | /_fmpq_poly_sub_can/ /rpoly/ /rden/ /poly1/ /den1/ /len1/ /poly2/ /den2/ /len2/ /can/ 
-- 
-- As per @_fmpq_poly_sub@ except that one can specify whether to
-- canonicalise the output or not. This function is intended to be used
-- with weak canonicalisation to prevent explosion in memory usage. It
-- exists for performance reasons.
foreign import ccall "fmpq_poly.h _fmpq_poly_sub_can"
  _fmpq_poly_sub_can :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CInt -> IO ()

-- | /fmpq_poly_sub/ /res/ /poly1/ /poly2/ 
-- 
-- Sets @res@ to the difference of @poly1@ and @poly2@, using Henrici\'s
-- algorithm.
foreign import ccall "fmpq_poly.h fmpq_poly_sub"
  fmpq_poly_sub :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> Ptr CFmpqPoly -> IO ()

-- | /fmpq_poly_sub_can/ /res/ /poly1/ /poly2/ /can/ 
-- 
-- As per @_fmpq_poly_sub@ except that one can specify whether to
-- canonicalise the output or not. This function is intended to be used
-- with weak canonicalisation to prevent explosion in memory usage. It
-- exists for performance reasons.
foreign import ccall "fmpq_poly.h fmpq_poly_sub_can"
  fmpq_poly_sub_can :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> Ptr CFmpqPoly -> CInt -> IO ()

-- | /_fmpq_poly_sub_series/ /rpoly/ /rden/ /poly1/ /den1/ /len1/ /poly2/ /den2/ /len2/ /n/ 
-- 
-- As per @_fmpq_poly_sub@ but the inputs are first notionally truncated to
-- length \(n\). If \(n\) is less than @len1@ or @len2@ then the output
-- only needs space for \(n\) coefficients. We require \(n \geq 0\).
foreign import ccall "fmpq_poly.h _fmpq_poly_sub_series"
  _fmpq_poly_sub_series :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

-- | /_fmpq_poly_sub_series_can/ /rpoly/ /rden/ /poly1/ /den1/ /len1/ /poly2/ /den2/ /len2/ /n/ /can/ 
-- 
-- As per @_fmpq_poly_sub_can@ but the inputs are first notionally
-- truncated to length \(n\). If \(n\) is less than @len1@ or @len2@ then
-- the output only needs space for \(n\) coefficients. We require
-- \(n \geq 0\).
foreign import ccall "fmpq_poly.h _fmpq_poly_sub_series_can"
  _fmpq_poly_sub_series_can :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> CInt -> IO ()

-- | /fmpq_poly_sub_series/ /res/ /poly1/ /poly2/ /n/ 
-- 
-- As per @fmpq_poly_sub@ but the inputs are first notionally truncated to
-- length \(n\).
foreign import ccall "fmpq_poly.h fmpq_poly_sub_series"
  fmpq_poly_sub_series :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> IO ()

-- | /fmpq_poly_sub_series_can/ /res/ /poly1/ /poly2/ /n/ /can/ 
-- 
-- As per @fmpq_poly_sub_can@ but the inputs are first notionally truncated
-- to length \(n\).
foreign import ccall "fmpq_poly.h fmpq_poly_sub_series_can"
  fmpq_poly_sub_series_can :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> CInt -> IO ()

-- Scalar multiplication and division ------------------------------------------

-- | /_fmpq_poly_scalar_mul_si/ /rpoly/ /rden/ /poly/ /den/ /len/ /c/ 
-- 
-- Sets @(rpoly, rden, len)@ to the product of \(c\) of @(poly, den, len)@.
-- 
-- If the input is normalised, then so is the output, provided it is
-- non-zero. If the input is in lowest terms, then so is the output.
-- However, even if neither of these conditions are met, the result will be
-- (mathematically) correct.
-- 
-- Supports exact aliasing between @(rpoly, den)@ and @(poly, den)@.
foreign import ccall "fmpq_poly.h _fmpq_poly_scalar_mul_si"
  _fmpq_poly_scalar_mul_si :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

-- | /_fmpq_poly_scalar_mul_ui/ /rpoly/ /rden/ /poly/ /den/ /len/ /c/ 
-- 
-- Sets @(rpoly, rden, len)@ to the product of \(c\) of @(poly, den, len)@.
-- 
-- If the input is normalised, then so is the output, provided it is
-- non-zero. If the input is in lowest terms, then so is the output.
-- However, even if neither of these conditions are met, the result will be
-- (mathematically) correct.
-- 
-- Supports exact aliasing between @(rpoly, den)@ and @(poly, den)@.
foreign import ccall "fmpq_poly.h _fmpq_poly_scalar_mul_ui"
  _fmpq_poly_scalar_mul_ui :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CULong -> IO ()

-- | /_fmpq_poly_scalar_mul_fmpz/ /rpoly/ /rden/ /poly/ /den/ /len/ /c/ 
-- 
-- Sets @(rpoly, rden, len)@ to the product of \(c\) of @(poly, den, len)@.
-- 
-- If the input is normalised, then so is the output, provided it is
-- non-zero. If the input is in lowest terms, then so is the output.
-- However, even if neither of these conditions are met, the result will be
-- (mathematically) correct.
-- 
-- Supports exact aliasing between @(rpoly, den)@ and @(poly, den)@.
foreign import ccall "fmpq_poly.h _fmpq_poly_scalar_mul_fmpz"
  _fmpq_poly_scalar_mul_fmpz :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /_fmpq_poly_scalar_mul_fmpq/ /rpoly/ /rden/ /poly/ /den/ /len/ /r/ /s/ 
-- 
-- Sets @(rpoly, rden)@ to the product of \(r/s\) and @(poly, den, len)@,
-- in lowest terms.
-- 
-- Assumes that @(poly, den, len)@ and \(r/s\) are provided in lowest
-- terms. Assumes that @rpoly@ is an array of length @len@. Supports
-- aliasing of @(rpoly, den)@ and @(poly, den)@. The @fmpz_t@\'s \(r\) and
-- \(s\) may not be part of @(rpoly, rden)@.
foreign import ccall "fmpq_poly.h _fmpq_poly_scalar_mul_fmpq"
  _fmpq_poly_scalar_mul_fmpq :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpq_poly_scalar_mul_si/ /rop/ /op/ /c/ 
-- 
-- Sets @rop@ to \(c\) times @op@.
foreign import ccall "fmpq_poly.h fmpq_poly_scalar_mul_si"
  fmpq_poly_scalar_mul_si :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> IO ()

-- | /fmpq_poly_scalar_mul_ui/ /rop/ /op/ /c/ 
-- 
-- Sets @rop@ to \(c\) times @op@.
foreign import ccall "fmpq_poly.h fmpq_poly_scalar_mul_ui"
  fmpq_poly_scalar_mul_ui :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> CULong -> IO ()

-- | /fmpq_poly_scalar_mul_fmpz/ /rop/ /op/ /c/ 
-- 
-- Sets @rop@ to \(c\) times @op@. Assumes that the @fmpz_t c@ is not part
-- of @rop@.
foreign import ccall "fmpq_poly.h fmpq_poly_scalar_mul_fmpz"
  fmpq_poly_scalar_mul_fmpz :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> Ptr CFmpz -> IO ()

-- | /fmpq_poly_scalar_mul_fmpq/ /rop/ /op/ /c/ 
-- 
-- Sets @rop@ to \(c\) times @op@.
foreign import ccall "fmpq_poly.h fmpq_poly_scalar_mul_fmpq"
  fmpq_poly_scalar_mul_fmpq :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> Ptr CMpq -> IO ()

-- -- | /fmpq_poly_scalar_mul_mpz/ /rop/ /op/ /c/ 
-- -- 
-- -- Sets @rop@ to \(c\) times @op@.
-- foreign import ccall "fmpq_poly.h fmpq_poly_scalar_mul_mpz"
--   fmpq_poly_scalar_mul_mpz :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> Ptr CMpz -> IO ()

-- -- | /fmpq_poly_scalar_mul_mpq/ /rop/ /op/ /c/ 
-- -- 
-- -- Sets @rop@ to \(c\) times @op@.
-- foreign import ccall "fmpq_poly.h fmpq_poly_scalar_mul_mpq"
--   fmpq_poly_scalar_mul_mpq :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> Ptr CFmpq -> IO ()

-- | /_fmpq_poly_scalar_div_fmpz/ /rpoly/ /rden/ /poly/ /den/ /len/ /c/ 
-- 
-- Sets @(rpoly, rden, len)@ to @(poly, den, len)@ divided by \(c\), in
-- lowest terms.
-- 
-- Assumes that @len@ is positive. Assumes that \(c\) is non-zero. Supports
-- aliasing between @(rpoly, rden)@ and @(poly, den)@. Assumes that \(c\)
-- is not part of @(rpoly, rden)@.
foreign import ccall "fmpq_poly.h _fmpq_poly_scalar_div_fmpz"
  _fmpq_poly_scalar_div_fmpz :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /_fmpq_poly_scalar_div_si/ /rpoly/ /rden/ /poly/ /den/ /len/ /c/ 
-- 
-- Sets @(rpoly, rden, len)@ to @(poly, den, len)@ divided by \(c\), in
-- lowest terms.
-- 
-- Assumes that @len@ is positive. Assumes that \(c\) is non-zero. Supports
-- aliasing between @(rpoly, rden)@ and @(poly, den)@.
foreign import ccall "fmpq_poly.h _fmpq_poly_scalar_div_si"
  _fmpq_poly_scalar_div_si :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

-- | /_fmpq_poly_scalar_div_ui/ /rpoly/ /rden/ /poly/ /den/ /len/ /c/ 
-- 
-- Sets @(rpoly, rden, len)@ to @(poly, den, len)@ divided by \(c\), in
-- lowest terms.
-- 
-- Assumes that @len@ is positive. Assumes that \(c\) is non-zero. Supports
-- aliasing between @(rpoly, rden)@ and @(poly, den)@.
foreign import ccall "fmpq_poly.h _fmpq_poly_scalar_div_ui"
  _fmpq_poly_scalar_div_ui :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CULong -> IO ()

-- | /_fmpq_poly_scalar_div_fmpq/ /rpoly/ /rden/ /poly/ /den/ /len/ /r/ /s/ 
-- 
-- Sets @(rpoly, rden, len)@ to @(poly, den, len)@ divided by \(r/s\), in
-- lowest terms.
-- 
-- Assumes that @len@ is positive. Assumes that \(r/s\) is non-zero and in
-- lowest terms. Supports aliasing between @(rpoly, rden)@ and
-- @(poly, den)@. The @fmpz_t@\'s \(r\) and \(s\) may not be part of
-- @(rpoly, poly)@.
foreign import ccall "fmpq_poly.h _fmpq_poly_scalar_div_fmpq"
  _fmpq_poly_scalar_div_fmpq :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpq_poly_scalar_div_si/ /rop/ /op/ /c/ 
-- 
-- Sets @rop@ to @op@ divided by the scalar @c@.
foreign import ccall "fmpq_poly.h fmpq_poly_scalar_div_si"
  fmpq_poly_scalar_div_si :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> IO ()

foreign import ccall "fmpq_poly.h fmpq_poly_scalar_div_ui"
  fmpq_poly_scalar_div_ui :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> IO ()

foreign import ccall "fmpq_poly.h fmpq_poly_scalar_div_fmpz"
  fmpq_poly_scalar_div_fmpz :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> Ptr CFmpz -> IO ()

foreign import ccall "fmpq_poly.h fmpq_poly_scalar_div_fmpq"
  fmpq_poly_scalar_div_fmpq :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> Ptr CFmpq -> IO ()

-- foreign import ccall "fmpq_poly.h fmpq_poly_scalar_div_mpz"
--   fmpq_poly_scalar_div_mpz :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> Ptr Mpz -> IO ()

-- foreign import ccall "fmpq_poly.h fmpq_poly_scalar_div_mpq"
--   fmpq_poly_scalar_div_mpq :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> Ptr Mpq -> IO ()
  
-- Multiplication --------------------------------------------------------------

-- | /_fmpq_poly_mul/ /rpoly/ /rden/ /poly1/ /den1/ /len1/ /poly2/ /den2/ /len2/ 
-- 
-- Sets @(rpoly, rden, len1 + len2 - 1)@ to the product of
-- @(poly1, den1, len1)@ and @(poly2, den2, len2)@. If the input is
-- provided in canonical form, then so is the output.
-- 
-- Assumes @len1 >= len2 > 0@. Allows zero-padding in the input. Does not
-- allow aliasing between the inputs and outputs.
foreign import ccall "fmpq_poly.h _fmpq_poly_mul"
  _fmpq_poly_mul :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- | /fmpq_poly_mul/ /res/ /poly1/ /poly2/ 
-- 
-- Sets @res@ to the product of @poly1@ and @poly2@.
foreign import ccall "fmpq_poly.h fmpq_poly_mul"
  fmpq_poly_mul :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> Ptr CFmpqPoly -> IO ()

-- | /_fmpq_poly_mullow/ /rpoly/ /rden/ /poly1/ /den1/ /len1/ /poly2/ /den2/ /len2/ /n/ 
-- 
-- Sets @(rpoly, rden, n)@ to the low \(n\) coefficients of @(poly1, den1)@
-- and @(poly2, den2)@. The output is not guaranteed to be in canonical
-- form.
-- 
-- Assumes @len1 >= len2 > 0@ and @0 \< n \<= len1 + len2 - 1@. Allows for
-- zero-padding in the inputs. Does not allow aliasing between the inputs
-- and outputs.
foreign import ccall "fmpq_poly.h _fmpq_poly_mullow"
  _fmpq_poly_mullow :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

-- | /fmpq_poly_mullow/ /res/ /poly1/ /poly2/ /n/ 
-- 
-- Sets @res@ to the product of @poly1@ and @poly2@, truncated to
-- length~\`n\`.
foreign import ccall "fmpq_poly.h fmpq_poly_mullow"
  fmpq_poly_mullow :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> IO ()

-- | /fmpq_poly_addmul/ /rop/ /op1/ /op2/ 
-- 
-- Adds the product of @op1@ and @op2@ to @rop@.
foreign import ccall "fmpq_poly.h fmpq_poly_addmul"
  fmpq_poly_addmul :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> Ptr CFmpqPoly -> IO ()

-- | /fmpq_poly_submul/ /rop/ /op1/ /op2/ 
-- 
-- Subtracts the product of @op1@ and @op2@ from @rop@.
foreign import ccall "fmpq_poly.h fmpq_poly_submul"
  fmpq_poly_submul :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> Ptr CFmpqPoly -> IO ()

-- Powering --------------------------------------------------------------------

-- | /_fmpq_poly_pow/ /rpoly/ /rden/ /poly/ /den/ /len/ /e/ 
-- 
-- Sets @(rpoly, rden)@ to @(poly, den)^e@, assuming @e, len > 0@. Assumes
-- that @rpoly@ is an array of length at least @e * (len - 1) + 1@.
-- Supports aliasing of @(rpoly, den)@ and @(poly, den)@.
foreign import ccall "fmpq_poly.h _fmpq_poly_pow"
  _fmpq_poly_pow :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CULong -> IO ()

-- | /fmpq_poly_pow/ /res/ /poly/ /e/ 
-- 
-- Sets @res@ to @poly^e@, where the only special case \(0^0\) is defined
-- as \(1\).
foreign import ccall "fmpq_poly.h fmpq_poly_pow"
  fmpq_poly_pow :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> CULong -> IO ()

-- | /_fmpq_poly_pow_trunc/ /res/ /rden/ /f/ /fden/ /flen/ /exp/ /len/ 
-- 
-- Sets @(rpoly, rden, len)@ to @(poly, den)^e@ truncated to length @len@,
-- where @len@ is at most @e * (flen - 1) + 1@.
foreign import ccall "fmpq_poly.h _fmpq_poly_pow_trunc"
  _fmpq_poly_pow_trunc :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CULong -> CLong -> IO ()

-- | /fmpq_poly_pow_trunc/ /res/ /poly/ /e/ /n/ 
-- 
-- Sets @res@ to @poly^e@ truncated to length @n@.
foreign import ccall "fmpq_poly.h fmpq_poly_pow_trunc"
  fmpq_poly_pow_trunc :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> CULong -> CLong -> IO ()

-- Shifting --------------------------------------------------------------------

-- | /fmpq_poly_shift_left/ /res/ /poly/ /n/ 
-- 
-- Set @res@ to @poly@ shifted left by \(n\) coefficients. Zero
-- coefficients are inserted.
foreign import ccall "fmpq_poly.h fmpq_poly_shift_left"
  fmpq_poly_shift_left :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> IO ()

-- | /fmpq_poly_shift_right/ /res/ /poly/ /n/ 
-- 
-- Set @res@ to @poly@ shifted right by \(n\) coefficients. If \(n\) is
-- equal to or greater than the current length of @poly@, @res@ is set to
-- the zero polynomial.
foreign import ccall "fmpq_poly.h fmpq_poly_shift_right"
  fmpq_poly_shift_right :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> IO ()

-- Euclidean division ----------------------------------------------------------

-- | /_fmpq_poly_divrem/ /Q/ /q/ /R/ /r/ /A/ /a/ /lenA/ /B/ /b/ /lenB/ /inv/ 
-- 
-- Finds the quotient @(Q, q)@ and remainder @(R, r)@ of the Euclidean
-- division of @(A, a)@ by @(B, b)@.
-- 
-- Assumes that @lenA >= lenB > 0@. Assumes that \(R\) has space for @lenA@
-- coefficients, although only the bottom @lenB - 1@ will carry meaningful
-- data on exit. Supports no aliasing between the two outputs, or between
-- the inputs and the outputs.
-- 
-- An optional precomputed inverse of the leading coefficient of \(B\) from
-- @fmpz_preinvn_init@ can be supplied. Otherwise @inv@ should be @NULL@.
foreign import ccall "fmpq_poly.h _fmpq_poly_divrem"
  _fmpq_poly_divrem :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpzPreInvN -> IO ()

-- | /fmpq_poly_divrem/ /Q/ /R/ /poly1/ /poly2/ 
-- 
-- Finds the quotient \(Q\) and remainder \(R\) of the Euclidean division
-- of @poly1@ by @poly2@.
foreign import ccall "fmpq_poly.h fmpq_poly_divrem"
  fmpq_poly_divrem :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> Ptr CFmpqPoly -> Ptr CFmpqPoly -> IO ()

-- | /_fmpq_poly_div/ /Q/ /q/ /A/ /a/ /lenA/ /B/ /b/ /lenB/ /inv/ 
-- 
-- Finds the quotient @(Q, q)@ of the Euclidean division of @(A, a)@ by
-- @(B, b)@.
-- 
-- Assumes that @lenA >= lenB > 0@. Supports no aliasing between the inputs
-- and the outputs.
-- 
-- An optional precomputed inverse of the leading coefficient of \(B\) from
-- @fmpz_preinvn_init@ can be supplied. Otherwise @inv@ should be @NULL@.
foreign import ccall "fmpq_poly.h _fmpq_poly_div"
  _fmpq_poly_div :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpzPreInvN -> IO ()

-- | /fmpq_poly_div/ /Q/ /poly1/ /poly2/ 
-- 
-- Finds the quotient \(Q\) and remainder \(R\) of the Euclidean division
-- of @poly1@ by @poly2@.
foreign import ccall "fmpq_poly.h fmpq_poly_div"
  fmpq_poly_div :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> Ptr CFmpqPoly -> IO ()

-- | /_fmpq_poly_rem/ /R/ /r/ /A/ /a/ /lenA/ /B/ /b/ /lenB/ /inv/ 
-- 
-- Finds the remainder @(R, r)@ of the Euclidean division of @(A, a)@ by
-- @(B, b)@.
-- 
-- Assumes that @lenA >= lenB > 0@. Supports no aliasing between the inputs
-- and the outputs.
-- 
-- An optional precomputed inverse of the leading coefficient of \(B\) from
-- @fmpz_preinvn_init@ can be supplied. Otherwise @inv@ should be @NULL@.
foreign import ccall "fmpq_poly.h _fmpq_poly_rem"
  _fmpq_poly_rem :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpzPreInvN -> IO ()

-- | /fmpq_poly_rem/ /R/ /poly1/ /poly2/ 
-- 
-- Finds the remainder \(R\) of the Euclidean division of @poly1@ by
-- @poly2@.
foreign import ccall "fmpq_poly.h fmpq_poly_rem"
  fmpq_poly_rem :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> Ptr CFmpqPoly -> IO ()

-- Powering --------------------------------------------------------------------

-- | /_fmpq_poly_powers_precompute/ /B/ /denB/ /len/ 
-- 
-- Computes @2*len - 1@ powers of \(x\) modulo the polynomial \(B\) of the
-- given length. This is used as a kind of precomputed inverse in the
-- remainder routine below.
foreign import ccall "fmpq_poly.h _fmpq_poly_powers_precompute"
  _fmpq_poly_powers_precompute :: Ptr CFmpz -> Ptr CFmpz -> CLong -> IO (Ptr CFmpqPoly)

-- | /fmpq_poly_powers_precompute/ /pinv/ /poly/ 
-- 
-- Computes @2*len - 1@ powers of $x$ modulo the polynomial $B$ of the
-- given length. This is used as a kind of precomputed inverse in the
-- remainder routine below.
foreign import ccall "fmpq_poly.h fmpq_poly_powers_precompute"
  fmpq_poly_powers_precompute :: Ptr CFmpqPolyPowersPrecomp -> Ptr CFmpqPoly -> IO ()

-- | /_fmpq_poly_powers_clear/ /powers/ /len/ 
-- 
-- Clean up resources used by precomputed powers which have been computed
-- by @_fmpq_poly_powers_precompute@.
foreign import ccall "fmpq_poly.h _fmpq_poly_powers_clear"
  _fmpq_poly_powers_clear :: Ptr CFmpqPoly -> CLong -> IO ()

-- | /fmpq_poly_powers_clear/ /pinv/ 
-- 
-- Clean up resources used by precomputed powers which have been computed
-- by @fmpq_poly_powers_precompute@.
foreign import ccall "fmpq_poly.h fmpq_poly_powers_clear"
  fmpq_poly_powers_clear :: Ptr CFmpqPolyPowersPrecomp -> IO ()

-- | /_fmpq_poly_rem_powers_precomp/ /A/ /denA/ /m/ /B/ /denB/ /n/ /powers/ 
-- 
-- Set \(A\) to the remainder of \(A\) divide \(B\) given precomputed
-- powers mod \(B\) provided by @_fmpq_poly_powers_precompute@. No aliasing
-- is allowed.
-- 
-- This function is only faster if \(m \leq 2*n - 1\).
-- 
-- The output of this function is /not/ canonicalised.
foreign import ccall "fmpq_poly.h _fmpq_poly_rem_powers_precomp"
  _fmpq_poly_rem_powers_precomp :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpqPoly -> IO ()

-- | /fmpq_poly_rem_powers_precomp/ /R/ /A/ /B/ /B_inv/ 
-- 
-- Set \(R\) to the remainder of \(A\) divide \(B\) given precomputed
-- powers mod \(B\) provided by @fmpq_poly_powers_precompute@.
-- 
-- This function is only faster if @A->length \<= 2*B->length - 1@.
-- 
-- The output of this function is /not/ canonicalised.
foreign import ccall "fmpq_poly.h fmpq_poly_rem_powers_precomp"
  fmpq_poly_rem_powers_precomp :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> Ptr CFmpqPoly -> Ptr CFmpqPolyPowersPrecomp -> IO ()

-- Divisibility testing --------------------------------------------------------

-- | /_fmpq_poly_divides/ /qpoly/ /qden/ /poly1/ /den1/ /len1/ /poly2/ /den2/ /len2/ 
-- 
-- Return \(1\) if @(poly2, den2, len2)@ divides @(poly1, den1, len1)@ and
-- set @(qpoly, qden, len1 - len2 + 1)@ to the quotient. Otherwise return
-- \(0\). Requires that @qpoly@ has space for @len1 - len2 + 1@
-- coefficients and that @len1 >= len2 > 0@.
foreign import ccall "fmpq_poly.h _fmpq_poly_divides"
  _fmpq_poly_divides :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> CLong -> IO CInt

-- | /fmpq_poly_divides/ /q/ /poly1/ /poly2/ 
-- 
-- Return \(1\) if @poly2@ divides @poly1@ and set @q@ to the quotient.
-- Otherwise return \(0\).
foreign import ccall "fmpq_poly.h fmpq_poly_divides"
  fmpq_poly_divides :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> Ptr CFmpqPoly -> IO CInt

-- | /fmpq_poly_remove/ /q/ /poly1/ /poly2/ 
-- 
-- Sets @q@ to the quotient of @poly1@ by the highest power of @poly2@
-- which divides it, and returns the power. The divisor @poly2@ must not be
-- constant or an exception is raised.
foreign import ccall "fmpq_poly.h fmpq_poly_remove"
  fmpq_poly_remove :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> Ptr CFmpqPoly -> IO CLong

-- Power series division -------------------------------------------------------

-- | /_fmpq_poly_inv_series_newton/ /rpoly/ /rden/ /poly/ /den/ /len/ /n/ 
-- 
-- Computes the first \(n\) terms of the inverse power series of
-- @(poly, den, len)@ using Newton iteration.
-- 
-- The result is produced in canonical form.
-- 
-- Assumes that \(n \geq 1\) and that @poly@ has non-zero constant term.
-- Does not support aliasing.
foreign import ccall "fmpq_poly.h _fmpq_poly_inv_series_newton"
  _fmpq_poly_inv_series_newton :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

-- | /fmpq_poly_inv_series_newton/ /res/ /poly/ /n/ 
-- 
-- Computes the first \(n\) terms of the inverse power series of @poly@
-- using Newton iteration, assuming that @poly@ has non-zero constant term
-- and \(n \geq 1\).
foreign import ccall "fmpq_poly.h fmpq_poly_inv_series_newton"
  fmpq_poly_inv_series_newton :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> IO ()

-- | /_fmpq_poly_inv_series/ /rpoly/ /rden/ /poly/ /den/ /n/ 
-- 
-- Computes the first \(n\) terms of the inverse power series of
-- @(poly, den, len)@.
-- 
-- The result is produced in canonical form.
-- 
-- Assumes that \(n \geq 1\) and that @poly@ has non-zero constant term.
-- Does not support aliasing.
foreign import ccall "fmpq_poly.h _fmpq_poly_inv_series"
  _fmpq_poly_inv_series :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- | /fmpq_poly_inv_series/ /res/ /poly/ /n/ 
-- 
-- Computes the first \(n\) terms of the inverse power series of @poly@,
-- assuming that @poly@ has non-zero constant term and \(n \geq 1\).
foreign import ccall "fmpq_poly.h fmpq_poly_inv_series"
  fmpq_poly_inv_series :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> IO ()

-- | /_fmpq_poly_div_series/ /Q/ /denQ/ /A/ /denA/ /lenA/ /B/ /denB/ /lenB/ /n/ 
-- 
-- Divides @(A, denA, lenA)@ by @(B, denB, lenB)@ as power series over
-- \(\mathbb{Q}\), assuming \(B\) has non-zero constant term and that all
-- lengths are positive.
-- 
-- Aliasing is not supported.
-- 
-- This function ensures that the numerator and denominator are coprime on
-- exit.
foreign import ccall "fmpq_poly.h _fmpq_poly_div_series"
  _fmpq_poly_div_series :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

-- | /fmpq_poly_div_series/ /Q/ /A/ /B/ /n/ 
-- 
-- Performs power series division in \(\mathbb{Q}[[x]] / (x^n)\). The
-- function considers the polynomials \(A\) and \(B\) as power series of
-- length~\`n\` starting with the constant terms. The function assumes that
-- \(B\) has non-zero constant term and \(n \geq 1\).
foreign import ccall "fmpq_poly.h fmpq_poly_div_series"
  fmpq_poly_div_series :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> IO ()

-- Greatest common divisor -----------------------------------------------------

-- | /_fmpq_poly_gcd/ /G/ /denG/ /A/ /lenA/ /B/ /lenB/ 
-- 
-- Computes the monic greatest common divisor \(G\) of \(A\) and \(B\).
-- 
-- Assumes that \(G\) has space for \(\operatorname{len}(B)\) coefficients,
-- where \(\operatorname{len}(A) \geq \operatorname{len}(B) > 0\).
-- 
-- Aliasing between the output and input arguments is not supported.
-- 
-- Does not support zero-padding.
foreign import ccall "fmpq_poly.h _fmpq_poly_gcd"
  _fmpq_poly_gcd :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> IO ()

-- | /fmpq_poly_gcd/ /G/ /A/ /B/ 
-- 
-- Computes the monic greatest common divisor \(G\) of \(A\) and \(B\).
-- 
-- In the the special case when \(A = B = 0\), sets \(G = 0\).
foreign import ccall "fmpq_poly.h fmpq_poly_gcd"
  fmpq_poly_gcd :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> Ptr CFmpqPoly -> IO ()

-- | /_fmpq_poly_xgcd/ /G/ /denG/ /S/ /denS/ /T/ /denT/ /A/ /denA/ /lenA/ /B/ /denB/ /lenB/ 
-- 
-- Computes polynomials \(G\), \(S\), and \(T\) such that
-- \(G = \gcd(A, B) = S A + T B\), where \(G\) is the monic greatest common
-- divisor of \(A\) and \(B\).
-- 
-- Assumes that \(G\), \(S\), and \(T\) have space for
-- \(\operatorname{len}(B)\), \(\operatorname{len}(B)\), and
-- \(\operatorname{len}(A)\) coefficients, respectively, where it is also
-- assumed that \(\operatorname{len}(A) \geq \operatorname{len}(B) > 0\).
-- 
-- Does not support zero padding of the input arguments.
foreign import ccall "fmpq_poly.h _fmpq_poly_xgcd"
  _fmpq_poly_xgcd :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- | /fmpq_poly_xgcd/ /G/ /S/ /T/ /A/ /B/ 
-- 
-- Computes polynomials \(G\), \(S\), and \(T\) such that
-- \(G = \gcd(A, B) = S A + T B\), where \(G\) is the monic greatest common
-- divisor of \(A\) and \(B\).
-- 
-- Corner cases are handled as follows. If \(A = B = 0\), returns
-- \(G = S = T = 0\). If \(A \neq 0\), \(B = 0\), returns the suitable
-- scalar multiple of \(G = A\), \(S = 1\), and \(T = 0\). The case when
-- \(A = 0\), \(B \neq 0\) is handled similarly.
foreign import ccall "fmpq_poly.h fmpq_poly_xgcd"
  fmpq_poly_xgcd :: Ptr CFmpqPoly -> Ptr CFmpzPoly -> Ptr CFmpzPoly -> Ptr CFmpqPoly -> Ptr CFmpqPoly -> IO ()

-- | /_fmpq_poly_lcm/ /L/ /denL/ /A/ /lenA/ /B/ /lenB/ 
-- 
-- Computes the monic least common multiple \(L\) of \(A\) and \(B\).
-- 
-- Assumes that \(L\) has space for
-- \(\operatorname{len}(A) + \operatorname{len}(B) - 1\) coefficients,
-- where \(\operatorname{len}(A) \geq \operatorname{len}(B) > 0\).
-- 
-- Aliasing between the output and input arguments is not supported.
-- 
-- Does not support zero-padding.
foreign import ccall "fmpq_poly.h _fmpq_poly_lcm"
  _fmpq_poly_lcm :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> IO ()

-- | /fmpq_poly_lcm/ /L/ /A/ /B/ 
-- 
-- Computes the monic least common multiple \(L\) of \(A\) and \(B\).
-- 
-- In the special case when \(A = B = 0\), sets \(L = 0\).
foreign import ccall "fmpq_poly.h fmpq_poly_lcm"
  fmpq_poly_lcm :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> Ptr CFmpqPoly -> IO ()

-- | /_fmpq_poly_resultant/ /rnum/ /rden/ /poly1/ /den1/ /len1/ /poly2/ /den2/ /len2/ 
-- 
-- Sets @(rnum, rden)@ to the resultant of the two input polynomials.
-- 
-- Assumes that @len1 >= len2 > 0@. Does not support zero-padding of the
-- input polynomials. Does not support aliasing of the input and output
-- arguments.
foreign import ccall "fmpq_poly.h _fmpq_poly_resultant"
  _fmpq_poly_resultant :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- | /fmpq_poly_resultant/ /r/ /f/ /g/ 
-- 
-- Returns the resultant of \(f\) and \(g\).
-- 
-- Enumerating the roots of \(f\) and \(g\) over \(\bar{\mathbf{Q}}\) as
-- \(r_1, \dotsc, r_m\) and \(s_1, \dotsc, s_n\), respectively, and letting
-- \(x\) and \(y\) denote the leading coefficients, the resultant is
-- defined as
-- 
-- \[`\]
-- \[x^{\deg(f)} y^{\deg(g)} \prod_{1 \leq i, j \leq n} (r_i - s_j).\]
-- 
-- We handle special cases as follows: if one of the polynomials is zero,
-- the resultant is zero. Note that otherwise if one of the polynomials is
-- constant, the last term in the above expression is the empty product.
foreign import ccall "fmpq_poly.h fmpq_poly_resultant"
  fmpq_poly_resultant :: Ptr CFmpq -> Ptr CFmpqPoly -> Ptr CFmpqPoly -> IO ()

-- | /fmpq_poly_resultant_div/ /r/ /f/ /g/ /div/ /nbits/ 
-- 
-- Returns the resultant of \(f\) and \(g\) divided by @div@ under the
-- assumption that the result has at most @nbits@ bits. The result must be
-- an integer.
foreign import ccall "fmpq_poly.h fmpq_poly_resultant_div"
  fmpq_poly_resultant_div :: Ptr CFmpq -> Ptr CFmpqPoly -> Ptr CFmpqPoly -> Ptr CFmpz -> CLong -> IO ()

-- Derivative and integral -----------------------------------------------------

-- | /_fmpq_poly_derivative/ /rpoly/ /rden/ /poly/ /den/ /len/ 
-- 
-- Sets @(rpoly, rden, len - 1)@ to the derivative of @(poly, den, len)@.
-- Does nothing if @len \<= 1@. Supports aliasing between the two
-- polynomials.
foreign import ccall "fmpq_poly.h _fmpq_poly_derivative"
  _fmpq_poly_derivative :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- | /fmpq_poly_derivative/ /res/ /poly/ 
-- 
-- Sets @res@ to the derivative of @poly@.
foreign import ccall "fmpq_poly.h fmpq_poly_derivative"
  fmpq_poly_derivative :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> IO ()

-- | /_fmpq_poly_nth_derivative/ /rpoly/ /rden/ /poly/ /den/ /n/ /len/ 
-- 
-- Sets @(rpoly, rden, len - n)@ to the nth derivative of
-- @(poly, den, len)@. Does nothing if @len \<= n@. Supports aliasing
-- between the two polynomials.
foreign import ccall "fmpq_poly.h _fmpq_poly_nth_derivative"
  _fmpq_poly_nth_derivative :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CULong -> CLong -> IO ()

-- | /fmpq_poly_nth_derivative/ /res/ /poly/ /n/ 
-- 
-- Sets @res@ to the nth derivative of @poly@.
foreign import ccall "fmpq_poly.h fmpq_poly_nth_derivative"
  fmpq_poly_nth_derivative :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> CULong -> IO ()

-- | /_fmpq_poly_integral/ /rpoly/ /rden/ /poly/ /den/ /len/ 
-- 
-- Sets @(rpoly, rden, len)@ to the integral of @(poly, den, len - 1)@.
-- Assumes @len >= 0@. Supports aliasing between the two polynomials. The
-- output will be in canonical form if the input is in canonical form.
foreign import ccall "fmpq_poly.h _fmpq_poly_integral"
  _fmpq_poly_integral :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- | /fmpq_poly_integral/ /res/ /poly/ 
-- 
-- Sets @res@ to the integral of @poly@. The constant term is set to zero.
-- In particular, the integral of the zero polynomial is the zero
-- polynomial.
foreign import ccall "fmpq_poly.h fmpq_poly_integral"
  fmpq_poly_integral :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> IO ()

-- Square roots ----------------------------------------------------------------

-- | /_fmpq_poly_sqrt_series/ /g/ /gden/ /f/ /fden/ /flen/ /n/ 
-- 
-- Sets @(g, gden, n)@ to the series expansion of the square root of
-- @(f, fden, flen)@. Assumes @n > 0@ and that @(f, fden, flen)@ has
-- constant term 1. Does not support aliasing between the input and output
-- polynomials.
foreign import ccall "fmpq_poly.h _fmpq_poly_sqrt_series"
  _fmpq_poly_sqrt_series :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

-- | /fmpq_poly_sqrt_series/ /res/ /f/ /n/ 
-- 
-- Sets @res@ to the series expansion of the square root of @f@ to order
-- @n > 1@. Requires @f@ to have constant term 1.
foreign import ccall "fmpq_poly.h fmpq_poly_sqrt_series"
  fmpq_poly_sqrt_series :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> IO ()

-- | /_fmpq_poly_invsqrt_series/ /g/ /gden/ /f/ /fden/ /flen/ /n/ 
-- 
-- Sets @(g, gden, n)@ to the series expansion of the inverse square root
-- of @(f, fden, flen)@. Assumes @n > 0@ and that @(f, fden, flen)@ has
-- constant term 1. Does not support aliasing between the input and output
-- polynomials.
foreign import ccall "fmpq_poly.h _fmpq_poly_invsqrt_series"
  _fmpq_poly_invsqrt_series :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

-- | /fmpq_poly_invsqrt_series/ /res/ /f/ /n/ 
-- 
-- Sets @res@ to the series expansion of the inverse square root of @f@ to
-- order @n > 0@. Requires @f@ to have constant term 1.
foreign import ccall "fmpq_poly.h fmpq_poly_invsqrt_series"
  fmpq_poly_invsqrt_series :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> IO ()

-- Power sums ------------------------------------------------------------------

-- | /_fmpq_poly_power_sums/ /res/ /rden/ /poly/ /len/ /n/ 
-- 
-- Compute the (truncated) power sums series of the polynomial @(poly,len)@
-- up to length \(n\) using Newton identities.
foreign import ccall "fmpq_poly.h _fmpq_poly_power_sums"
  _fmpq_poly_power_sums :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

-- | /fmpq_poly_power_sums/ /res/ /poly/ /n/ 
-- 
-- Compute the (truncated) power sum series of the monic polynomial @poly@
-- up to length \(n\) using Newton identities. That is the power series
-- whose coefficient of degree \(i\) is the sum of the \(i\)-th power of
-- all (complex) roots of the polynomial @poly@.
foreign import ccall "fmpq_poly.h fmpq_poly_power_sums"
  fmpq_poly_power_sums :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> IO ()

-- | /_fmpq_poly_power_sums_to_poly/ /res/ /poly/ /den/ /len/ 
-- 
-- Compute an integer polynomial given by its power sums series
-- @(poly,den,len)@.
foreign import ccall "fmpq_poly.h _fmpq_poly_power_sums_to_poly"
  _fmpq_poly_power_sums_to_poly :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- | /fmpq_poly_power_sums_to_fmpz_poly/ /res/ /Q/ 
-- 
-- Compute the integer polynomial with content one and positive leading
-- coefficient given by its power sums series @Q@.
foreign import ccall "fmpq_poly.h fmpq_poly_power_sums_to_fmpz_poly"
  fmpq_poly_power_sums_to_fmpz_poly :: Ptr CFmpzPoly -> Ptr CFmpqPoly -> IO ()

-- | /fmpq_poly_power_sums_to_poly/ /res/ /Q/ 
-- 
-- Compute the monic polynomial from its power sums series @Q@.
foreign import ccall "fmpq_poly.h fmpq_poly_power_sums_to_poly"
  fmpq_poly_power_sums_to_poly :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> IO ()

-- Transcendental functions ----------------------------------------------------

-- | /_fmpq_poly_log_series/ /g/ /gden/ /f/ /fden/ /flen/ /n/ 
-- 
-- Sets @(g, gden, n)@ to the series expansion of the logarithm of
-- @(f, fden, flen)@. Assumes @n > 0@ and that @(f, fden, flen)@ has
-- constant term 1. Supports aliasing between the input and output
-- polynomials.
foreign import ccall "fmpq_poly.h _fmpq_poly_log_series"
  _fmpq_poly_log_series :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

-- | /fmpq_poly_log_series/ /res/ /f/ /n/ 
-- 
-- Sets @res@ to the series expansion of the logarithm of @f@ to order
-- @n > 0@. Requires @f@ to have constant term 1.
foreign import ccall "fmpq_poly.h fmpq_poly_log_series"
  fmpq_poly_log_series :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> IO ()

-- | /_fmpq_poly_exp_series/ /g/ /gden/ /h/ /hden/ /hlen/ /n/ 
-- 
-- Sets @(g, gden, n)@ to the series expansion of the exponential function
-- of @(h, hden, hlen)@. Assumes @n > 0, hlen > 0@ and that
-- @(h, hden, hlen)@ has constant term 0. Supports aliasing between the
-- input and output polynomials.
foreign import ccall "fmpq_poly.h _fmpq_poly_exp_series"
  _fmpq_poly_exp_series :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

-- | /fmpq_poly_exp_series/ /res/ /h/ /n/ 
-- 
-- Sets @res@ to the series expansion of the exponential function of @h@ to
-- order @n > 0@. Requires @f@ to have constant term 0.
foreign import ccall "fmpq_poly.h fmpq_poly_exp_series"
  fmpq_poly_exp_series :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> IO ()

-- | /_fmpq_poly_exp_expinv_series/ /res1/ /res1den/ /res2/ /res2den/ /h/ /hden/ /hlen/ /n/ 
-- 
-- The same as @fmpq_poly_exp_series@, but simultaneously computes the
-- exponential (in @res1@, @res1den@) and its multiplicative inverse (in
-- @res2@, @res2den@). Supports aliasing between the input and output
-- polynomials.
foreign import ccall "fmpq_poly.h _fmpq_poly_exp_expinv_series"
  _fmpq_poly_exp_expinv_series :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

-- | /fmpq_poly_exp_expinv_series/ /res1/ /res2/ /h/ /n/ 
-- 
-- The same as @fmpq_poly_exp_series@, but simultaneously computes the
-- exponential (in @res1@) and its multiplicative inverse (in @res2@).
foreign import ccall "fmpq_poly.h fmpq_poly_exp_expinv_series"
  fmpq_poly_exp_expinv_series :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> IO ()

-- | /_fmpq_poly_atan_series/ /g/ /gden/ /f/ /fden/ /flen/ /n/ 
-- 
-- Sets @(g, gden, n)@ to the series expansion of the inverse tangent of
-- @(f, fden, flen)@. Assumes @n > 0@ and that @(f, fden, flen)@ has
-- constant term 0. Supports aliasing between the input and output
-- polynomials.
foreign import ccall "fmpq_poly.h _fmpq_poly_atan_series"
  _fmpq_poly_atan_series :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

-- | /fmpq_poly_atan_series/ /res/ /f/ /n/ 
-- 
-- Sets @res@ to the series expansion of the inverse tangent of @f@ to
-- order @n > 0@. Requires @f@ to have constant term 0.
foreign import ccall "fmpq_poly.h fmpq_poly_atan_series"
  fmpq_poly_atan_series :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> IO ()

-- | /_fmpq_poly_atanh_series/ /g/ /gden/ /f/ /fden/ /flen/ /n/ 
-- 
-- Sets @(g, gden, n)@ to the series expansion of the inverse hyperbolic
-- tangent of @(f, fden, flen)@. Assumes @n > 0@ and that @(f, fden, flen)@
-- has constant term 0. Supports aliasing between the input and output
-- polynomials.
foreign import ccall "fmpq_poly.h _fmpq_poly_atanh_series"
  _fmpq_poly_atanh_series :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

-- | /fmpq_poly_atanh_series/ /res/ /f/ /n/ 
-- 
-- Sets @res@ to the series expansion of the inverse hyperbolic tangent of
-- @f@ to order @n > 0@. Requires @f@ to have constant term 0.
foreign import ccall "fmpq_poly.h fmpq_poly_atanh_series"
  fmpq_poly_atanh_series :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> IO ()

-- | /_fmpq_poly_asin_series/ /g/ /gden/ /f/ /fden/ /flen/ /n/ 
-- 
-- Sets @(g, gden, n)@ to the series expansion of the inverse sine of
-- @(f, fden, flen)@. Assumes @n > 0@ and that @(f, fden, flen)@ has
-- constant term 0. Supports aliasing between the input and output
-- polynomials.
foreign import ccall "fmpq_poly.h _fmpq_poly_asin_series"
  _fmpq_poly_asin_series :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

-- | /fmpq_poly_asin_series/ /res/ /f/ /n/ 
-- 
-- Sets @res@ to the series expansion of the inverse sine of @f@ to order
-- @n > 0@. Requires @f@ to have constant term 0.
foreign import ccall "fmpq_poly.h fmpq_poly_asin_series"
  fmpq_poly_asin_series :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> IO ()

-- | /_fmpq_poly_asinh_series/ /g/ /gden/ /f/ /fden/ /flen/ /n/ 
-- 
-- Sets @(g, gden, n)@ to the series expansion of the inverse hyperbolic
-- sine of @(f, fden, flen)@. Assumes @n > 0@ and that @(f, fden, flen)@
-- has constant term 0. Supports aliasing between the input and output
-- polynomials.
foreign import ccall "fmpq_poly.h _fmpq_poly_asinh_series"
  _fmpq_poly_asinh_series :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

-- | /fmpq_poly_asinh_series/ /res/ /f/ /n/ 
-- 
-- Sets @res@ to the series expansion of the inverse hyperbolic sine of @f@
-- to order @n > 0@. Requires @f@ to have constant term 0.
foreign import ccall "fmpq_poly.h fmpq_poly_asinh_series"
  fmpq_poly_asinh_series :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> IO ()

-- | /_fmpq_poly_tan_series/ /g/ /gden/ /f/ /fden/ /flen/ /n/ 
-- 
-- Sets @(g, gden, n)@ to the series expansion of the tangent function of
-- @(f, fden, flen)@. Assumes @n > 0@ and that @(f, fden, flen)@ has
-- constant term 0. Does not support aliasing between the input and output
-- polynomials.
foreign import ccall "fmpq_poly.h _fmpq_poly_tan_series"
  _fmpq_poly_tan_series :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

-- | /fmpq_poly_tan_series/ /res/ /f/ /n/ 
-- 
-- Sets @res@ to the series expansion of the tangent function of @f@ to
-- order @n > 0@. Requires @f@ to have constant term 0.
foreign import ccall "fmpq_poly.h fmpq_poly_tan_series"
  fmpq_poly_tan_series :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> IO ()

-- | /_fmpq_poly_sin_series/ /g/ /gden/ /f/ /fden/ /flen/ /n/ 
-- 
-- Sets @(g, gden, n)@ to the series expansion of the sine of
-- @(f, fden, flen)@. Assumes @n > 0@ and that @(f, fden, flen)@ has
-- constant term 0. Supports aliasing between the input and output
-- polynomials.
foreign import ccall "fmpq_poly.h _fmpq_poly_sin_series"
  _fmpq_poly_sin_series :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

-- | /fmpq_poly_sin_series/ /res/ /f/ /n/ 
-- 
-- Sets @res@ to the series expansion of the sine of @f@ to order @n > 0@.
-- Requires @f@ to have constant term 0.
foreign import ccall "fmpq_poly.h fmpq_poly_sin_series"
  fmpq_poly_sin_series :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> IO ()

-- | /_fmpq_poly_cos_series/ /g/ /gden/ /f/ /fden/ /flen/ /n/ 
-- 
-- Sets @(g, gden, n)@ to the series expansion of the cosine of
-- @(f, fden, flen)@. Assumes @n > 0@ and that @(f, fden, flen)@ has
-- constant term 0. Supports aliasing between the input and output
-- polynomials.
foreign import ccall "fmpq_poly.h _fmpq_poly_cos_series"
  _fmpq_poly_cos_series :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

-- | /fmpq_poly_cos_series/ /res/ /f/ /n/ 
-- 
-- Sets @res@ to the series expansion of the cosine of @f@ to order
-- @n > 0@. Requires @f@ to have constant term 0.
foreign import ccall "fmpq_poly.h fmpq_poly_cos_series"
  fmpq_poly_cos_series :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> IO ()

-- | /_fmpq_poly_sin_cos_series/ /s/ /sden/ /c/ /cden/ /f/ /fden/ /flen/ /n/ 
-- 
-- Sets @(s, sden, n)@ to the series expansion of the sine of
-- @(f, fden, flen)@, and @(c, cden, n)@ to the series expansion of the
-- cosine. Assumes @n > 0@ and that @(f, fden, flen)@ has constant term 0.
-- Supports aliasing between the input and output polynomials.
foreign import ccall "fmpq_poly.h _fmpq_poly_sin_cos_series"
  _fmpq_poly_sin_cos_series :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

-- | /fmpq_poly_sin_cos_series/ /res1/ /res2/ /f/ /n/ 
-- 
-- Sets @res1@ to the series expansion of the sine of @f@ to order @n > 0@,
-- and @res2@ to the series expansion of the cosine. Requires @f@ to have
-- constant term 0.
foreign import ccall "fmpq_poly.h fmpq_poly_sin_cos_series"
  fmpq_poly_sin_cos_series :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> IO ()

-- | /_fmpq_poly_sinh_series/ /g/ /gden/ /f/ /fden/ /flen/ /n/ 
-- 
-- Sets @(g, gden, n)@ to the series expansion of the hyperbolic sine of
-- @(f, fden, flen)@. Assumes @n > 0@ and that @(f, fden, flen)@ has
-- constant term 0. Does not support aliasing between the input and output
-- polynomials.
foreign import ccall "fmpq_poly.h _fmpq_poly_sinh_series"
  _fmpq_poly_sinh_series :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

-- | /fmpq_poly_sinh_series/ /res/ /f/ /n/ 
-- 
-- Sets @res@ to the series expansion of the hyperbolic sine of @f@ to
-- order @n > 0@. Requires @f@ to have constant term 0.
foreign import ccall "fmpq_poly.h fmpq_poly_sinh_series"
  fmpq_poly_sinh_series :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> IO ()

-- | /_fmpq_poly_cosh_series/ /g/ /gden/ /f/ /fden/ /flen/ /n/ 
-- 
-- Sets @(g, gden, n)@ to the series expansion of the hyperbolic cosine of
-- @(f, fden, flen)@. Assumes @n > 0@ and that @(f, fden, flen)@ has
-- constant term 0. Does not support aliasing between the input and output
-- polynomials.
foreign import ccall "fmpq_poly.h _fmpq_poly_cosh_series"
  _fmpq_poly_cosh_series :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

-- | /fmpq_poly_cosh_series/ /res/ /f/ /n/ 
-- 
-- Sets @res@ to the series expansion of the hyperbolic cosine of @f@ to
-- order @n > 0@. Requires @f@ to have constant term 0.
foreign import ccall "fmpq_poly.h fmpq_poly_cosh_series"
  fmpq_poly_cosh_series :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> IO ()

-- | /_fmpq_poly_sinh_cosh_series/ /s/ /sden/ /c/ /cden/ /f/ /fden/ /flen/ /n/ 
-- 
-- Sets @(s, sden, n)@ to the series expansion of the hyperbolic sine of
-- @(f, fden, flen)@, and @(c, cden, n)@ to the series expansion of the
-- hyperbolic cosine. Assumes @n > 0@ and that @(f, fden, flen)@ has
-- constant term 0. Supports aliasing between the input and output
-- polynomials.
foreign import ccall "fmpq_poly.h _fmpq_poly_sinh_cosh_series"
  _fmpq_poly_sinh_cosh_series :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

-- | /fmpq_poly_sinh_cosh_series/ /res1/ /res2/ /f/ /n/ 
-- 
-- Sets @res1@ to the series expansion of the hyperbolic sine of @f@ to
-- order @n > 0@, and @res2@ to the series expansion of the hyperbolic
-- cosine. Requires @f@ to have constant term 0.
foreign import ccall "fmpq_poly.h fmpq_poly_sinh_cosh_series"
  fmpq_poly_sinh_cosh_series :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> IO ()

-- | /_fmpq_poly_tanh_series/ /g/ /gden/ /f/ /fden/ /flen/ /n/ 
-- 
-- Sets @(g, gden, n)@ to the series expansion of the hyperbolic tangent of
-- @(f, fden, flen)@. Assumes @n > 0@ and that @(f, fden, flen)@ has
-- constant term 0. Does not support aliasing between the input and output
-- polynomials.
foreign import ccall "fmpq_poly.h _fmpq_poly_tanh_series"
  _fmpq_poly_tanh_series :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

-- | /fmpq_poly_tanh_series/ /res/ /f/ /n/ 
-- 
-- Sets @res@ to the series expansion of the hyperbolic tangent of @f@ to
-- order @n > 0@. Requires @f@ to have constant term 0.
foreign import ccall "fmpq_poly.h fmpq_poly_tanh_series"
  fmpq_poly_tanh_series :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> IO ()

-- Orthogonal polynomials ------------------------------------------------------

-- | /_fmpq_poly_legendre_p/ /coeffs/ /den/ /n/ 
-- 
-- Sets @coeffs@ to the coefficient array of the Legendre polynomial
-- \(P_n(x)\), defined by
-- \((n+1) P_{n+1}(x) = (2n+1) x P_n(x) - n P_{n-1}(x)\), for \(n\ge0\).
-- Sets @den@ to the overall denominator. The coefficients are calculated
-- using a hypergeometric recurrence. The length of the array will be
-- @n+1@. To improve performance, the common denominator is computed in one
-- step and the coefficients are evaluated using integer arithmetic. The
-- denominator is given by
-- \(\gcd(n!,2^n) = 2^{\lfloor n/2 \rfloor + \lfloor n/4 \rfloor + \ldots}.\)
-- See @fmpz_poly@ for the shifted Legendre polynomials.
foreign import ccall "fmpq_poly.h _fmpq_poly_legendre_p"
  _fmpq_poly_legendre_p :: Ptr CFmpq -> Ptr CFmpz -> CULong -> IO ()

-- | /fmpq_poly_legendre_p/ /poly/ /n/ 
-- 
-- Sets @poly@ to the Legendre polynomial \(P_n(x)\), defined by
-- \((n+1) P_{n+1}(x) = (2n+1) x P_n(x) - n P_{n-1}(x)\), for \(n\ge0\).
-- The coefficients are calculated using a hypergeometric recurrence. To
-- improve performance, the common denominator is computed in one step and
-- the coefficients are evaluated using integer arithmetic. The denominator
-- is given by
-- \(\gcd(n!,2^n) = 2^{\lfloor n/2 \rfloor + \lfloor n/4 \rfloor + \ldots}.\)
-- See @fmpz_poly@ for the shifted Legendre polynomials.
foreign import ccall "fmpq_poly.h fmpq_poly_legendre_p"
  fmpq_poly_legendre_p :: Ptr CFmpqPoly -> CULong -> IO ()

-- | /_fmpq_poly_laguerre_l/ /coeffs/ /den/ /n/ 
-- 
-- Sets @coeffs@ to the coefficient array of the Laguerre polynomial
-- \(L_n(x)\), defined by
-- \((n+1) L_{n+1}(x) = (2n+1-x) L_n(x) - n L_{n-1}(x)\), for \(n\ge0\).
-- Sets @den@ to the overall denominator. The coefficients are calculated
-- using a hypergeometric recurrence. The length of the array will be
-- @n+1@.
foreign import ccall "fmpq_poly.h _fmpq_poly_laguerre_l"
  _fmpq_poly_laguerre_l :: Ptr CFmpq -> Ptr CFmpz -> CULong -> IO ()

-- | /fmpq_poly_laguerre_l/ /poly/ /n/ 
-- 
-- Sets @poly@ to the Laguerre polynomial \(L_n(x)\), defined by
-- \((n+1) L_{n+1}(x) = (2n+1-x) L_n(x) - n L_{n-1}(x)\), for \(n\ge0\).
-- The coefficients are calculated using a hypergeometric recurrence.
foreign import ccall "fmpq_poly.h fmpq_poly_laguerre_l"
  fmpq_poly_laguerre_l :: Ptr CFmpqPoly -> CULong -> IO ()

-- | /_fmpq_poly_gegenbauer_c/ /coeffs/ /den/ /n/ /a/ 
-- 
-- Sets @coeffs@ to the coefficient array of the Gegenbauer
-- (ultraspherical) polynomial
-- \(C^{(\alpha)}_n(x) = \frac{(2\alpha)_n}{n!}{}_2F_1\left(-n,2\alpha+n;
-- \alpha+\frac12;\frac{1-x}{2}\right)\), for integer \(n\ge0\) and
-- rational \(\alpha>0\). Sets @den@ to the overall denominator. The
-- coefficients are calculated using a hypergeometric recurrence.
foreign import ccall "fmpq_poly.h _fmpq_poly_gegenbauer_c"
  _fmpq_poly_gegenbauer_c :: Ptr CFmpq -> Ptr CFmpz -> CULong -> Ptr CFmpq -> IO ()

-- | /fmpq_poly_gegenbauer_c/ /poly/ /n/ /a/ 
-- 
-- Sets @poly@ to the Gegenbauer (ultraspherical) polynomial
-- \(C^{(\alpha)}_n(x) = \frac{(2\alpha)_n}{n!}{}_2F_1\left(-n,2\alpha+n;
-- \alpha+\frac12;\frac{1-x}{2}\right)\), for integer \(n\ge0\) and
-- rational \(\alpha>0\). The coefficients are calculated using a
-- hypergeometric recurrence.
foreign import ccall "fmpq_poly.h fmpq_poly_gegenbauer_c"
  fmpq_poly_gegenbauer_c :: Ptr CFmpqPoly -> CULong -> Ptr CFmpq -> IO ()

-- Evaluation ------------------------------------------------------------------

-- | /_fmpq_poly_evaluate_fmpz/ /rnum/ /rden/ /poly/ /den/ /len/ /a/ 
-- 
-- Evaluates the polynomial @(poly, den, len)@ at the integer \(a\) and
-- sets @(rnum, rden)@ to the result in lowest terms.
foreign import ccall "fmpq_poly.h _fmpq_poly_evaluate_fmpz"
  _fmpq_poly_evaluate_fmpz :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /fmpq_poly_evaluate_fmpz/ /res/ /poly/ /a/ 
-- 
-- Evaluates the polynomial @poly@ at the integer \(a\) and sets @res@ to
-- the result.
foreign import ccall "fmpq_poly.h fmpq_poly_evaluate_fmpz"
  fmpq_poly_evaluate_fmpz :: Ptr CFmpq -> Ptr CFmpqPoly -> Ptr CFmpz -> IO ()

-- | /_fmpq_poly_evaluate_fmpq/ /rnum/ /rden/ /poly/ /den/ /len/ /anum/ /aden/ 
-- 
-- Evaluates the polynomial @(poly, den, len)@ at the rational
-- @(anum, aden)@ and sets @(rnum, rden)@ to the result in lowest terms.
-- Aliasing between @(rnum, rden)@ and @(anum, aden)@ is not supported.
foreign import ccall "fmpq_poly.h _fmpq_poly_evaluate_fmpq"
  _fmpq_poly_evaluate_fmpq :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpq_poly_evaluate_fmpq/ /res/ /poly/ /a/ 
-- 
-- Evaluates the polynomial @poly@ at the rational \(a\) and sets @res@ to
-- the result.
foreign import ccall "fmpq_poly.h fmpq_poly_evaluate_fmpq"
  fmpq_poly_evaluate_fmpq :: Ptr CFmpq -> Ptr CFmpqPoly -> Ptr CFmpq -> IO ()

-- -- | /fmpq_poly_evaluate_mpz/ /res/ /poly/ /a/ 
-- -- 
-- -- Evaluates the polynomial @poly@ at the integer \(a\) of type @mpz@ and
-- -- sets @res@ to the result.
-- foreign import ccall "fmpq_poly.h fmpq_poly_evaluate_mpz"
--   fmpq_poly_evaluate_mpz :: Ptr CMpq -> Ptr CFmpqPoly -> Ptr CMpz -> IO ()

-- -- | /fmpq_poly_evaluate_mpq/ /res/ /poly/ /a/ 
-- -- 
-- -- Evaluates the polynomial @poly@ at the rational \(a\) of type @mpq@ and
-- -- sets @res@ to the result.
-- foreign import ccall "fmpq_poly.h fmpq_poly_evaluate_mpq"
--   fmpq_poly_evaluate_mpq :: Ptr CMpq -> Ptr CFmpqPoly -> Ptr CMpq -> IO ()

-- Interpolation ---------------------------------------------------------------

-- | /_fmpq_poly_interpolate_fmpz_vec/ /poly/ /den/ /xs/ /ys/ /n/ 
-- 
-- Sets @poly@ \/ @den@ to the unique interpolating polynomial of degree at
-- most \(n - 1\) satisfying \(f(x_i) = y_i\) for every pair \(x_i, y_i\)
-- in @xs@ and @ys@.
-- 
-- The vector @poly@ must have room for @n+1@ coefficients, even if the
-- interpolating polynomial is shorter. Aliasing of @poly@ or @den@ with
-- any other argument is not allowed.
-- 
-- It is assumed that the \(x\) values are distinct.
-- 
-- This function uses a simple \(O(n^2)\) implementation of Lagrange
-- interpolation, clearing denominators to avoid working with fractions. It
-- is currently not designed to be efficient for large \(n\).
foreign import ccall "fmpq_poly.h _fmpq_poly_interpolate_fmpz_vec"
  _fmpq_poly_interpolate_fmpz_vec :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- | /fmpq_poly_interpolate_fmpz_vec/ /poly/ /xs/ /ys/ /n/ 
-- 
-- Sets @poly@ to the unique interpolating polynomial of degree at most
-- \(n - 1\) satisfying \(f(x_i) = y_i\) for every pair \(x_i, y_i\) in
-- @xs@ and @ys@. It is assumed that the \(x\) values are distinct.
foreign import ccall "fmpq_poly.h fmpq_poly_interpolate_fmpz_vec"
  fmpq_poly_interpolate_fmpz_vec :: Ptr CFmpqPoly -> Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- Composition -----------------------------------------------------------------

-- | /_fmpq_poly_compose/ /res/ /den/ /poly1/ /den1/ /len1/ /poly2/ /den2/ /len2/ 
-- 
-- Sets @(res, den)@ to the composition of @(poly1, den1, len1)@ and
-- @(poly2, den2, len2)@, assuming @len1, len2 > 0@.
-- 
-- Assumes that @res@ has space for @(len1 - 1) * (len2 - 1) + 1@
-- coefficients. Does not support aliasing.
foreign import ccall "fmpq_poly.h _fmpq_poly_compose"
  _fmpq_poly_compose :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- | /fmpq_poly_compose/ /res/ /poly1/ /poly2/ 
-- 
-- Sets @res@ to the composition of @poly1@ and @poly2@.
foreign import ccall "fmpq_poly.h fmpq_poly_compose"
  fmpq_poly_compose :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> Ptr CFmpqPoly -> IO ()

-- | /_fmpq_poly_rescale/ /res/ /denr/ /poly/ /den/ /len/ /anum/ /aden/ 
-- 
-- Sets @(res, denr, len)@ to @(poly, den, len)@ with the indeterminate
-- rescaled by @(anum, aden)@.
-- 
-- Assumes that @len > 0@ and that @(anum, aden)@ is non-zero and in lowest
-- terms. Supports aliasing between @(res, denr, len)@ and
-- @(poly, den, len)@.
foreign import ccall "fmpq_poly.h _fmpq_poly_rescale"
  _fmpq_poly_rescale :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpq_poly_rescale/ /res/ /poly/ /a/ 
-- 
-- Sets @res@ to @poly@ with the indeterminate rescaled by \(a\).
foreign import ccall "fmpq_poly.h fmpq_poly_rescale"
  fmpq_poly_rescale :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> Ptr CFmpq -> IO ()

-- Power series composition ----------------------------------------------------

-- | /_fmpq_poly_compose_series_horner/ /res/ /den/ /poly1/ /den1/ /len1/ /poly2/ /den2/ /len2/ /n/ 
-- 
-- Sets @(res, den, n)@ to the composition of @(poly1, den1, len1)@ and
-- @(poly2, den2, len2)@ modulo \(x^n\), where the constant term of @poly2@
-- is required to be zero.
-- 
-- Assumes that @len1, len2, n > 0@, that @len1, len2 \<= n@, that
-- @(len1-1) * (len2-1) + 1 \<= n@, and that @res@ has space for @n@
-- coefficients. Does not support aliasing between any of the inputs and
-- the output.
-- 
-- This implementation uses the Horner scheme. The default @fmpz_poly@
-- composition algorithm is automatically used when the composition can be
-- performed over the integers.
foreign import ccall "fmpq_poly.h _fmpq_poly_compose_series_horner"
  _fmpq_poly_compose_series_horner :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

-- | /fmpq_poly_compose_series_horner/ /res/ /poly1/ /poly2/ /n/ 
-- 
-- Sets @res@ to the composition of @poly1@ and @poly2@ modulo \(x^n\),
-- where the constant term of @poly2@ is required to be zero.
-- 
-- This implementation uses the Horner scheme. The default @fmpz_poly@
-- composition algorithm is automatically used when the composition can be
-- performed over the integers.
foreign import ccall "fmpq_poly.h fmpq_poly_compose_series_horner"
  fmpq_poly_compose_series_horner :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> IO ()

-- | /_fmpq_poly_compose_series_brent_kung/ /res/ /den/ /poly1/ /den1/ /len1/ /poly2/ /den2/ /len2/ /n/ 
-- 
-- Sets @(res, den, n)@ to the composition of @(poly1, den1, len1)@ and
-- @(poly2, den2, len2)@ modulo \(x^n\), where the constant term of @poly2@
-- is required to be zero.
-- 
-- Assumes that @len1, len2, n > 0@, that @len1, len2 \<= n@, that
-- @(len1-1) * (len2-1) + 1 \<= n@, and that @res@ has space for @n@
-- coefficients. Does not support aliasing between any of the inputs and
-- the output.
-- 
-- This implementation uses Brent-Kung algorithm 2.1 < [BrentKung1978]>.
-- The default @fmpz_poly@ composition algorithm is automatically used when
-- the composition can be performed over the integers.
foreign import ccall "fmpq_poly.h _fmpq_poly_compose_series_brent_kung"
  _fmpq_poly_compose_series_brent_kung :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

-- | /fmpq_poly_compose_series_brent_kung/ /res/ /poly1/ /poly2/ /n/ 
-- 
-- Sets @res@ to the composition of @poly1@ and @poly2@ modulo \(x^n\),
-- where the constant term of @poly2@ is required to be zero.
-- 
-- This implementation uses Brent-Kung algorithm 2.1 < [BrentKung1978]>.
-- The default @fmpz_poly@ composition algorithm is automatically used when
-- the composition can be performed over the integers.
foreign import ccall "fmpq_poly.h fmpq_poly_compose_series_brent_kung"
  fmpq_poly_compose_series_brent_kung :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> IO ()

-- | /_fmpq_poly_compose_series/ /res/ /den/ /poly1/ /den1/ /len1/ /poly2/ /den2/ /len2/ /n/ 
-- 
-- Sets @(res, den, n)@ to the composition of @(poly1, den1, len1)@ and
-- @(poly2, den2, len2)@ modulo \(x^n\), where the constant term of @poly2@
-- is required to be zero.
-- 
-- Assumes that @len1, len2, n > 0@, that @len1, len2 \<= n@, that
-- @(len1-1) * (len2-1) + 1 \<= n@, and that @res@ has space for @n@
-- coefficients. Does not support aliasing between any of the inputs and
-- the output.
-- 
-- This implementation automatically switches between the Horner scheme and
-- Brent-Kung algorithm 2.1 depending on the size of the inputs. The
-- default @fmpz_poly@ composition algorithm is automatically used when the
-- composition can be performed over the integers.
foreign import ccall "fmpq_poly.h _fmpq_poly_compose_series"
  _fmpq_poly_compose_series :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

-- | /fmpq_poly_compose_series/ /res/ /poly1/ /poly2/ /n/ 
-- 
-- Sets @res@ to the composition of @poly1@ and @poly2@ modulo \(x^n\),
-- where the constant term of @poly2@ is required to be zero.
-- 
-- This implementation automatically switches between the Horner scheme and
-- Brent-Kung algorithm 2.1 depending on the size of the inputs. The
-- default @fmpz_poly@ composition algorithm is automatically used when the
-- composition can be performed over the integers.
foreign import ccall "fmpq_poly.h fmpq_poly_compose_series"
  fmpq_poly_compose_series :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> IO ()

-- Power series reversion ------------------------------------------------------

-- | /_fmpq_poly_revert_series_lagrange/ /res/ /den/ /poly1/ /den1/ /len1/ /n/ 
-- 
-- Sets @(res, den)@ to the power series reversion of @(poly1, den1, len1)@
-- modulo \(x^n\).
-- 
-- The constant term of @poly2@ is required to be zero and the linear term
-- is required to be nonzero. Assumes that \(n > 0\). Does not support
-- aliasing between any of the inputs and the output.
-- 
-- This implementation uses the Lagrange inversion formula. The default
-- @fmpz_poly@ reversion algorithm is automatically used when the reversion
-- can be performed over the integers.
foreign import ccall "fmpq_poly.h _fmpq_poly_revert_series_lagrange"
  _fmpq_poly_revert_series_lagrange :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

-- | /fmpq_poly_revert_series_lagrange/ /res/ /poly/ /n/ 
-- 
-- Sets @res@ to the power series reversion of @poly1@ modulo \(x^n\). The
-- constant term of @poly2@ is required to be zero and the linear term is
-- required to be nonzero.
-- 
-- This implementation uses the Lagrange inversion formula. The default
-- @fmpz_poly@ reversion algorithm is automatically used when the reversion
-- can be performed over the integers.
foreign import ccall "fmpq_poly.h fmpq_poly_revert_series_lagrange"
  fmpq_poly_revert_series_lagrange :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> IO ()

-- | /_fmpq_poly_revert_series_lagrange_fast/ /res/ /den/ /poly1/ /den1/ /len1/ /n/ 
-- 
-- Sets @(res, den)@ to the power series reversion of @(poly1, den1, len1)@
-- modulo \(x^n\).
-- 
-- The constant term of @poly2@ is required to be zero and the linear term
-- is required to be nonzero. Assumes that \(n > 0\). Does not support
-- aliasing between any of the inputs and the output.
-- 
-- This implementation uses a reduced-complexity implementation of the
-- Lagrange inversion formula. The default @fmpz_poly@ reversion algorithm
-- is automatically used when the reversion can be performed over the
-- integers.
foreign import ccall "fmpq_poly.h _fmpq_poly_revert_series_lagrange_fast"
  _fmpq_poly_revert_series_lagrange_fast :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

-- | /fmpq_poly_revert_series_lagrange_fast/ /res/ /poly/ /n/ 
-- 
-- Sets @res@ to the power series reversion of @poly1@ modulo \(x^n\). The
-- constant term of @poly2@ is required to be zero and the linear term is
-- required to be nonzero.
-- 
-- This implementation uses a reduced-complexity implementation of the
-- Lagrange inversion formula. The default @fmpz_poly@ reversion algorithm
-- is automatically used when the reversion can be performed over the
-- integers.
foreign import ccall "fmpq_poly.h fmpq_poly_revert_series_lagrange_fast"
  fmpq_poly_revert_series_lagrange_fast :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> IO ()

-- | /_fmpq_poly_revert_series_newton/ /res/ /den/ /poly1/ /den1/ /len1/ /n/ 
-- 
-- Sets @(res, den)@ to the power series reversion of @(poly1, den1, len1)@
-- modulo \(x^n\).
-- 
-- The constant term of @poly2@ is required to be zero and the linear term
-- is required to be nonzero. Assumes that \(n > 0\). Does not support
-- aliasing between any of the inputs and the output.
-- 
-- This implementation uses Newton iteration. The default @fmpz_poly@
-- reversion algorithm is automatically used when the reversion can be
-- performed over the integers.
foreign import ccall "fmpq_poly.h _fmpq_poly_revert_series_newton"
  _fmpq_poly_revert_series_newton :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

-- | /fmpq_poly_revert_series_newton/ /res/ /poly/ /n/ 
-- 
-- Sets @res@ to the power series reversion of @poly1@ modulo \(x^n\). The
-- constant term of @poly2@ is required to be zero and the linear term is
-- required to be nonzero.
-- 
-- This implementation uses Newton iteration. The default @fmpz_poly@
-- reversion algorithm is automatically used when the reversion can be
-- performed over the integers.
foreign import ccall "fmpq_poly.h fmpq_poly_revert_series_newton"
  fmpq_poly_revert_series_newton :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> IO ()

-- | /_fmpq_poly_revert_series/ /res/ /den/ /poly1/ /den1/ /len1/ /n/ 
-- 
-- Sets @(res, den)@ to the power series reversion of @(poly1, den1, len1)@
-- modulo \(x^n\).
-- 
-- The constant term of @poly2@ is required to be zero and the linear term
-- is required to be nonzero. Assumes that \(n > 0\). Does not support
-- aliasing between any of the inputs and the output.
-- 
-- This implementation defaults to using Newton iteration. The default
-- @fmpz_poly@ reversion algorithm is automatically used when the reversion
-- can be performed over the integers.
foreign import ccall "fmpq_poly.h _fmpq_poly_revert_series"
  _fmpq_poly_revert_series :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

-- | /fmpq_poly_revert_series/ /res/ /poly/ /n/ 
-- 
-- Sets @res@ to the power series reversion of @poly1@ modulo \(x^n\). The
-- constant term of @poly2@ is required to be zero and the linear term is
-- required to be nonzero.
-- 
-- This implementation defaults to using Newton iteration. The default
-- @fmpz_poly@ reversion algorithm is automatically used when the reversion
-- can be performed over the integers.
foreign import ccall "fmpq_poly.h fmpq_poly_revert_series"
  fmpq_poly_revert_series :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> CLong -> IO ()

-- Gaussian content ------------------------------------------------------------

-- | /_fmpq_poly_content/ /res/ /poly/ /den/ /len/ 
-- 
-- Sets @res@ to the content of @(poly, den, len)@. If @len == 0@, sets
-- @res@ to zero.
foreign import ccall "fmpq_poly.h _fmpq_poly_content"
  _fmpq_poly_content :: Ptr CFmpq -> Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- | /fmpq_poly_content/ /res/ /poly/ 
-- 
-- Sets @res@ to the content of @poly@. The content of the zero polynomial
-- is defined to be zero.
foreign import ccall "fmpq_poly.h fmpq_poly_content"
  fmpq_poly_content :: Ptr CFmpq -> Ptr CFmpqPoly -> IO ()

-- | /_fmpq_poly_primitive_part/ /rpoly/ /rden/ /poly/ /den/ /len/ 
-- 
-- Sets @(rpoly, rden, len)@ to the primitive part, with non-negative
-- leading coefficient, of @(poly, den, len)@. Assumes that @len > 0@.
-- Supports aliasing between the two polynomials.
foreign import ccall "fmpq_poly.h _fmpq_poly_primitive_part"
  _fmpq_poly_primitive_part :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- | /fmpq_poly_primitive_part/ /res/ /poly/ 
-- 
-- Sets @res@ to the primitive part, with non-negative leading coefficient,
-- of @poly@.
foreign import ccall "fmpq_poly.h fmpq_poly_primitive_part"
  fmpq_poly_primitive_part :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> IO ()

-- | /_fmpq_poly_is_monic/ /poly/ /den/ /len/ 
-- 
-- Returns whether the polynomial @(poly, den, len)@ is monic. The zero
-- polynomial is not monic by definition.
foreign import ccall "fmpq_poly.h _fmpq_poly_is_monic"
  _fmpq_poly_is_monic :: Ptr CFmpz -> Ptr CFmpz -> CLong -> IO CInt

-- | /fmpq_poly_is_monic/ /poly/ 
-- 
-- Returns whether the polynomial @poly@ is monic. The zero polynomial is
-- not monic by definition.
foreign import ccall "fmpq_poly.h fmpq_poly_is_monic"
  fmpq_poly_is_monic :: Ptr CFmpqPoly -> IO CInt

-- | /_fmpq_poly_make_monic/ /rpoly/ /rden/ /poly/ /den/ /len/ 
-- 
-- Sets @(rpoly, rden, len)@ to the monic scalar multiple of
-- @(poly, den, len)@. Assumes that @len > 0@. Supports aliasing between
-- the two polynomials.
foreign import ccall "fmpq_poly.h _fmpq_poly_make_monic"
  _fmpq_poly_make_monic :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- | /fmpq_poly_make_monic/ /res/ /poly/ 
-- 
-- Sets @res@ to the monic scalar multiple of @poly@ whenever @poly@ is
-- non-zero. If @poly@ is the zero polynomial, sets @res@ to zero.
foreign import ccall "fmpq_poly.h fmpq_poly_make_monic"
  fmpq_poly_make_monic :: Ptr CFmpqPoly -> Ptr CFmpqPoly -> IO ()

-- Square-free -----------------------------------------------------------------

-- | /fmpq_poly_is_squarefree/ /poly/ 
-- 
-- Returns whether the polynomial @poly@ is square-free. A non-zero
-- polynomial is defined to be square-free if it has no non-unit square
-- factors. We also define the zero polynomial to be square-free.
foreign import ccall "fmpq_poly.h fmpq_poly_is_squarefree"
  fmpq_poly_is_squarefree :: Ptr CFmpqPoly -> IO CInt

-- Input and output ------------------------------------------------------------

-- | /_fmpq_poly_print/ /poly/ /den/ /len/ 
-- 
-- Prints the polynomial @(poly, den, len)@ to @stdout@.
-- 
-- In case of success, returns a positive value. In case of failure,
-- returns a non-positive value.
foreign import ccall "fmpq_poly.h _fmpq_poly_print"
  _fmpq_poly_print :: Ptr CFmpz -> Ptr CFmpz -> CLong -> IO CInt

-- | /fmpq_poly_print/ /poly/ 
-- 
-- Prints the polynomial to @stdout@.
-- 
-- In case of success, returns a positive value. In case of failure,
-- returns a non-positive value.
-- foreign import ccall "fmpq_poly.h fmpq_poly_print"
fmpq_poly_print :: Ptr CFmpqPoly -> IO CInt
fmpq_poly_print poly = printCStr fmpq_poly_get_str poly

foreign import ccall "fmpq_poly.h _fmpq_poly_print_pretty"
  _fmpq_poly_print_pretty :: Ptr CFmpz -> Ptr CFmpz -> CLong -> CString -> IO CInt

-- | /fmpq_poly_print_pretty/ /poly/ /var/ 
-- 
-- Prints the pretty representation of @poly@ to @stdout@, using the
-- null-terminated string @var@ not equal to @\"\\0\"@ as the variable
-- name.
-- 
-- In the current implementation always returns~\`1\`.
fmpq_poly_print_pretty :: Ptr CFmpqPoly -> CString -> IO CInt
fmpq_poly_print_pretty poly var =
  printCStr (flip fmpq_poly_get_str_pretty var) poly

-- | /_fmpq_poly_fprint/ /file/ /poly/ /den/ /len/ 
-- 
-- Prints the polynomial @(poly, den, len)@ to the stream @file@.
-- 
-- In case of success, returns a positive value. In case of failure,
-- returns a non-positive value.
foreign import ccall "fmpq_poly.h _fmpq_poly_fprint"
  _fmpq_poly_fprint :: Ptr CFile -> Ptr CFmpz -> Ptr CFmpz -> CLong -> IO CInt

-- | /fmpq_poly_fprint/ /file/ /poly/ 
-- 
-- Prints the polynomial to the stream @file@.
-- 
-- In case of success, returns a positive value. In case of failure,
-- returns a non-positive value.
foreign import ccall "fmpq_poly.h fmpq_poly_fprint"
  fmpq_poly_fprint :: Ptr CFile -> Ptr CFmpqPoly -> IO CInt

foreign import ccall "fmpq_poly.h _fmpq_poly_fprint_pretty"
  _fmpq_poly_fprint_pretty :: Ptr CFile -> Ptr CFmpz -> Ptr CFmpz -> CLong -> CString -> IO CInt

-- | /fmpq_poly_fprint_pretty/ /file/ /poly/ /var/ 
-- 
-- Prints the pretty representation of @poly@ to @stdout@, using the
-- null-terminated string @var@ not equal to @\"\\0\"@ as the variable
-- name.
-- 
-- In the current implementation, always returns~\`1\`.
foreign import ccall "fmpq_poly.h fmpq_poly_fprint_pretty"
  fmpq_poly_fprint_pretty :: Ptr CFile -> Ptr CFmpqPoly -> CString -> IO CInt

-- | /fmpq_poly_read/ /poly/ 
-- 
-- Reads a polynomial from @stdin@, storing the result in @poly@.
-- 
-- In case of success, returns a positive number. In case of failure,
-- returns a non-positive value.
foreign import ccall "fmpq_poly.h fmpq_poly_read"
  fmpq_poly_read :: Ptr CFmpqPoly -> IO CInt

-- | /fmpq_poly_fread/ /file/ /poly/ 
-- 
-- Reads a polynomial from the stream @file@, storing the result in @poly@.
-- 
-- In case of success, returns a positive number. In case of failure,
-- returns a non-positive value.
foreign import ccall "fmpq_poly.h fmpq_poly_fread"
  fmpq_poly_fread :: Ptr CFile -> Ptr CFmpqPoly -> IO CInt

