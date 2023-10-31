module Data.Number.Flint.Calcium.Ca.Poly.FFI (
  -- * Dense univariate polynomials over the real and complex numbers
    CaPoly (..)
  , CCaPoly (..)
  , newCaPoly
  , withCaPoly
  , withNewCaPoly
  -- * Memory management
  , ca_poly_init
  , ca_poly_clear
  , ca_poly_fit_length
  , _ca_poly_set_length
  , _ca_poly_normalise
  -- * Assignment and simple values
  , ca_poly_zero
  , ca_poly_one
  , ca_poly_x
  , ca_poly_set_ca
  , ca_poly_set_si
  , ca_poly_set
  , ca_poly_set_fmpz_poly
  , ca_poly_set_fmpq_poly
  , ca_poly_set_coeff_ca
  , ca_poly_transfer
  -- * Random generation
  , ca_poly_randtest
  , ca_poly_randtest_rational
  -- * Input and output
  , ca_poly_get_str
  , ca_poly_fprint
  , ca_poly_print
  , ca_poly_printn
  -- * Degree and leading coefficient
  , ca_poly_is_proper
  , ca_poly_make_monic
  , _ca_poly_reverse
  , ca_poly_reverse
  -- * Comparisons
  , _ca_poly_check_equal
  , ca_poly_check_equal
  , ca_poly_check_is_zero
  , ca_poly_check_is_one
  -- * Arithmetic
  , _ca_poly_shift_left
  , ca_poly_shift_left
  , _ca_poly_shift_right
  , ca_poly_shift_right
  , ca_poly_neg
  , _ca_poly_add
  , ca_poly_add
  , _ca_poly_sub
  , ca_poly_sub
  , _ca_poly_mul
  , ca_poly_mul
  , _ca_poly_mullow
  , ca_poly_mullow
  , ca_poly_mul_ca
  , ca_poly_div_ca
  , _ca_poly_divrem_basecase
  , ca_poly_divrem_basecase
  , _ca_poly_divrem
  , ca_poly_divrem
  , ca_poly_div
  , ca_poly_rem
  , _ca_poly_pow_ui_trunc
  , ca_poly_pow_ui_trunc
  , _ca_poly_pow_ui
  , ca_poly_pow_ui
  -- * Evaluation and composition
  , _ca_poly_evaluate_horner
  , ca_poly_evaluate_horner
  , _ca_poly_evaluate
  , ca_poly_evaluate
  , _ca_poly_compose
  , ca_poly_compose
  -- * Derivative and integral
  , _ca_poly_derivative
  , ca_poly_derivative
  , _ca_poly_integral
  , ca_poly_integral
  -- * Power series division
  , _ca_poly_inv_series
  , ca_poly_inv_series
  , _ca_poly_div_series
  , ca_poly_div_series
  -- * Elementary functions
  , _ca_poly_exp_series
  , ca_poly_exp_series
  , _ca_poly_log_series
  , ca_poly_log_series
  -- * Greatest common divisor
  , _ca_poly_gcd_euclidean
  , ca_poly_gcd_euclidean
  , _ca_poly_gcd
  , ca_poly_gcd
  -- * Roots and factorization
  , ca_poly_factor_squarefree
  , ca_poly_squarefree_part
  , _ca_poly_set_roots
  , ca_poly_set_roots
  , _ca_poly_roots
  , ca_poly_roots
  -- * Vectors of polynomials
  , _ca_poly_vec_init
  , ca_poly_vec_init
  , _ca_poly_vec_fit_length
  , ca_poly_vec_set_length
  , _ca_poly_vec_clear
  , ca_poly_vec_clear
  , ca_poly_vec_append
) where

-- Dense univariate polynomials over the real and complex number ---------------

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.C.Types
import Foreign.C.String
import Foreign.Storable

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz.Poly
import Data.Number.Flint.Fmpq.Poly
import Data.Number.Flint.Calcium
import Data.Number.Flint.Calcium.Ca.Types
import Data.Number.Flint.Calcium.Ca

#include <flint/ca_poly.h>

-- ca_poly_t -------------------------------------------------------------------

instance Storable CCaPoly where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size ca_poly_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment ca_poly_t}
  peek = error "CCaPoly.peek: Not defined"
  poke = error "CCaPoly.poke: Not defined"

newCaPoly ctx@(CaCtx fctx) = do
  x <- mallocForeignPtr
  withForeignPtr x $ \xp -> do
    withCaCtx ctx $ \ctxp -> do
      ca_poly_init xp ctxp
    addForeignPtrFinalizerEnv p_ca_poly_clear xp fctx
  return $ CaPoly x

{-# INLINE withCaPoly #-}
withCaPoly (CaPoly x) f = do
  withForeignPtr x $ \xp -> f xp >>= return . (CaPoly x,)

withNewCaPoly ctx f = do
  x <- newCaPoly ctx
  withCaPoly x f

-- A @CaPoly@ represents a univariate polynomial over the real or
-- complex numbers (an element of \(\mathbb{R}[X]\) or \(\mathbb{C}[X]\)),
-- implemented as an array of coefficients of type @ca_struct@.
--
-- Most functions are provided in two versions: an underscore method which
-- operates directly on pre-allocated arrays of coefficients and generally
-- has some restrictions (such as requiring the lengths to be nonzero and
-- not supporting aliasing of the input and output arrays), and a
-- non-underscore method which performs automatic memory management and
-- handles degenerate cases.
--
-- Warnings:
--



-- A polynomial with numerical coefficients and with a nonzero leading
-- coefficient is called /proper/. The function @ca_poly_is_proper@ can be
-- used to check for violations.
--
-- Types, macros and constants -------------------------------------------------







-- Memory management -----------------------------------------------------------

-- | /ca_poly_init/ /poly/ /ctx/ 
--
-- Initializes the polynomial for use, setting it to the zero polynomial.
foreign import ccall "ca_poly.h ca_poly_init"
  ca_poly_init :: Ptr CCaPoly -> Ptr CCaCtx -> IO ()

-- | /ca_poly_clear/ /poly/ /ctx/ 
--
-- Clears the polynomial, deallocating all coefficients and the coefficient
-- array.
foreign import ccall "ca_poly.h ca_poly_clear"
  ca_poly_clear :: Ptr CCaPoly -> Ptr CCaCtx -> IO ()

foreign import ccall "ca_poly.h &ca_poly_clear"
  p_ca_poly_clear :: FunPtr (Ptr CCaPoly -> Ptr CCaCtx -> IO ())

-- | /ca_poly_fit_length/ /poly/ /len/ /ctx/ 
--
-- Makes sure that the coefficient array of the polynomial contains at
-- least /len/ initialized coefficients.
foreign import ccall "ca_poly.h ca_poly_fit_length"
  ca_poly_fit_length :: Ptr CCaPoly -> CLong -> Ptr CCaCtx -> IO ()

-- | /_ca_poly_set_length/ /poly/ /len/ /ctx/ 
--
-- Directly changes the length of the polynomial, without allocating or
-- deallocating coefficients. The value should not exceed the allocation
-- length.
foreign import ccall "ca_poly.h _ca_poly_set_length"
  _ca_poly_set_length :: Ptr CCaPoly -> CLong -> Ptr CCaCtx -> IO ()

-- | /_ca_poly_normalise/ /poly/ /ctx/ 
--
-- Strips any top coefficients which can be proved identical to zero.
foreign import ccall "ca_poly.h _ca_poly_normalise"
  _ca_poly_normalise :: Ptr CCaPoly -> Ptr CCaCtx -> IO ()

-- Assignment and simple values ------------------------------------------------

-- | /ca_poly_zero/ /poly/ /ctx/ 
--
-- Sets /poly/ to the zero polynomial.
foreign import ccall "ca_poly.h ca_poly_zero"
  ca_poly_zero :: Ptr CCaPoly -> Ptr CCaCtx -> IO ()

-- | /ca_poly_one/ /poly/ /ctx/ 
--
-- Sets /poly/ to the constant polynomial 1.
foreign import ccall "ca_poly.h ca_poly_one"
  ca_poly_one :: Ptr CCaPoly -> Ptr CCaCtx -> IO ()

-- | /ca_poly_x/ /poly/ /ctx/ 
--
-- Sets /poly/ to the monomial /x/.
foreign import ccall "ca_poly.h ca_poly_x"
  ca_poly_x :: Ptr CCaPoly -> Ptr CCaCtx -> IO ()

-- | /ca_poly_set_ca/ /poly/ /c/ /ctx/ 
foreign import ccall "ca_poly.h ca_poly_set_ca"
  ca_poly_set_ca :: Ptr CCaPoly -> Ptr CCa -> Ptr CCaCtx -> IO ()
-- | /ca_poly_set_si/ /poly/ /c/ /ctx/ 
--
-- Sets /poly/ to the constant polynomial /c/.
foreign import ccall "ca_poly.h ca_poly_set_si"
  ca_poly_set_si :: Ptr CCaPoly -> CLong -> Ptr CCaCtx -> IO ()

-- | /ca_poly_set/ /res/ /src/ /ctx/ 
foreign import ccall "ca_poly.h ca_poly_set"
  ca_poly_set :: Ptr CCaPoly -> Ptr CCaPoly -> Ptr CCaCtx -> IO ()
  
-- | /ca_poly_set_fmpz_poly/ /res/ /src/ /ctx/ 
foreign import ccall "ca_poly.h ca_poly_set_fmpz_poly"
  ca_poly_set_fmpz_poly :: Ptr CCaPoly -> Ptr CFmpzPoly -> Ptr CCaCtx -> IO ()
-- | /ca_poly_set_fmpq_poly/ /res/ /src/ /ctx/ 
--
-- Sets /poly/ the polynomial /src/.
foreign import ccall "ca_poly.h ca_poly_set_fmpq_poly"
  ca_poly_set_fmpq_poly :: Ptr CCaPoly -> Ptr CFmpqPoly -> Ptr CCaCtx -> IO ()

-- | /ca_poly_set_coeff_ca/ /poly/ /n/ /x/ /ctx/ 
--
-- Sets the coefficient at position /n/ in /poly/ to /x/.
foreign import ccall "ca_poly.h ca_poly_set_coeff_ca"
  ca_poly_set_coeff_ca :: Ptr CCaPoly -> CLong -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_poly_transfer/ /res/ /res_ctx/ /src/ /src_ctx/ 
--
-- Sets /res/ to /src/ where the corresponding context objects /res_ctx/
-- and /src_ctx/ may be different.
-- 
-- This operation preserves the mathematical value represented by /src/,
-- but may result in a different internal representation depending on the
-- settings of the context objects.
foreign import ccall "ca_poly.h ca_poly_transfer"
  ca_poly_transfer :: Ptr CCaPoly -> Ptr CCaCtx -> Ptr CCaPoly -> Ptr CCaCtx -> IO ()

-- Random generation -----------------------------------------------------------

-- | /ca_poly_randtest/ /poly/ /state/ /len/ /depth/ /bits/ /ctx/ 
--
-- Sets /poly/ to a random polynomial of length up to /len/ and with
-- entries having complexity up to /depth/ and /bits/ (see @ca_randtest@).
foreign import ccall "ca_poly.h ca_poly_randtest"
  ca_poly_randtest :: Ptr CCaPoly -> Ptr CFRandState -> CLong -> CLong -> CLong -> Ptr CCaCtx -> IO ()

-- | /ca_poly_randtest_rational/ /poly/ /state/ /len/ /bits/ /ctx/ 
--
-- Sets /poly/ to a random rational polynomial of length up to /len/ and
-- with entries up to /bits/ bits in size.
foreign import ccall "ca_poly.h ca_poly_randtest_rational"
  ca_poly_randtest_rational :: Ptr CCaPoly -> Ptr CFRandState -> CLong -> CLong -> Ptr CCaCtx -> IO ()

-- Input and output ------------------------------------------------------------

-- | /ca_poly_get_str/ /poly/ /ctx/ 
--
-- Returns a string representation of /poly/. The coefficients are printed on
-- separate lines.
foreign import ccall "ca_poly.h ca_poly_get_str"
  ca_poly_get_str :: Ptr CCaPoly -> Ptr CCaCtx -> IO CString

-- | /ca_poly_fprint/ /file/ /poly/ /ctx/ 
--
-- Prints /poly/ to file. The coefficients are printed on
-- separate lines.
foreign import ccall "ca_poly.h ca_poly_fprint"
  ca_poly_fprint :: Ptr CFile -> Ptr CCaPoly -> Ptr CCaCtx -> IO ()

-- | /ca_poly_print/ /poly/ /ctx/ 
--
-- Prints /poly/ to standard output. The coefficients are printed on
-- separate lines.
ca_poly_print :: Ptr CCaPoly -> Ptr CCaCtx -> IO ()
ca_poly_print poly ctx = do
  printCStr (\poly -> ca_poly_get_str poly ctx) poly
  return ()
  
-- | /ca_poly_printn/ /poly/ /digits/ /ctx/ 
--
-- Prints a decimal representation of /poly/ with precision specified by
-- /digits/. The coefficients are comma-separated and the whole list is
-- enclosed in square brackets.
foreign import ccall "ca_poly.h ca_poly_printn"
  ca_poly_printn :: Ptr CCaPoly -> CLong -> Ptr CCaCtx -> IO ()

-- Degree and leading coefficient ----------------------------------------------

-- | /ca_poly_is_proper/ /poly/ /ctx/ 
--
-- Checks that /poly/ represents an element of \(\mathbb{C}[X]\) with
-- well-defined degree. This returns 1 if the leading coefficient of /poly/
-- is nonzero and all coefficients of /poly/ are numbers (not special
-- values). It returns 0 otherwise. It returns 1 when /poly/ is precisely
-- the zero polynomial (which does not have a leading coefficient).
foreign import ccall "ca_poly.h ca_poly_is_proper"
  ca_poly_is_proper :: Ptr CCaPoly -> Ptr CCaCtx -> IO CInt

-- | /ca_poly_make_monic/ /res/ /poly/ /ctx/ 
--
-- Makes /poly/ monic by dividing by the leading coefficient if possible
-- and returns 1. Returns 0 if the leading coefficient cannot be certified
-- to be nonzero, or if /poly/ is the zero polynomial.
foreign import ccall "ca_poly.h ca_poly_make_monic"
  ca_poly_make_monic :: Ptr CCaPoly -> Ptr CCaPoly -> Ptr CCaCtx -> IO CInt

-- | /_ca_poly_reverse/ /res/ /poly/ /len/ /n/ /ctx/ 
--
foreign import ccall "ca_poly.h _ca_poly_reverse"
  _ca_poly_reverse :: Ptr CCa -> Ptr CCa -> CLong -> CLong -> Ptr CCaCtx -> IO ()

-- | /ca_poly_reverse/ /res/ /poly/ /n/ /ctx/ 
--
-- Sets /res/ to the reversal of /poly/ considered as a polynomial of
-- length /n/, zero-padding if needed. The underscore method assumes that
-- /len/ is positive and less than or equal to /n/.
foreign import ccall "ca_poly.h ca_poly_reverse"
  ca_poly_reverse :: Ptr CCaPoly -> Ptr CCaPoly -> CLong -> Ptr CCaCtx -> IO ()

-- Comparisons -----------------------------------------------------------------

-- | /_ca_poly_check_equal/ /poly1/ /len1/ /poly2/ /len2/ /ctx/ 
foreign import ccall "ca_poly.h _ca_poly_check_equal"
  _ca_poly_check_equal :: Ptr CCa -> CLong -> Ptr CCa -> CLong -> Ptr CCaCtx -> IO (Ptr CTruth)
-- | /ca_poly_check_equal/ /poly1/ /poly2/ /ctx/ 
--
-- Checks if /poly1/ and /poly2/ represent the same polynomial. The
-- underscore method assumes that /len1/ is at least as large as /len2/.
foreign import ccall "ca_poly.h ca_poly_check_equal"
  ca_poly_check_equal :: Ptr CCaPoly -> Ptr CCaPoly -> Ptr CCaCtx -> IO (Ptr CTruth)

-- | /ca_poly_check_is_zero/ /poly/ /ctx/ 
--
-- Checks if /poly/ is the zero polynomial.
foreign import ccall "ca_poly.h ca_poly_check_is_zero"
  ca_poly_check_is_zero :: Ptr CCaPoly -> Ptr CCaCtx -> IO (Ptr CTruth)

-- | /ca_poly_check_is_one/ /poly/ /ctx/ 
--
-- Checks if /poly/ is the constant polynomial 1.
foreign import ccall "ca_poly.h ca_poly_check_is_one"
  ca_poly_check_is_one :: Ptr CCaPoly -> Ptr CCaCtx -> IO (Ptr CTruth)

-- Arithmetic ------------------------------------------------------------------

-- | /_ca_poly_shift_left/ /res/ /poly/ /len/ /n/ /ctx/ 
foreign import ccall "ca_poly.h _ca_poly_shift_left"
  _ca_poly_shift_left :: Ptr CCa -> Ptr CCa -> CLong -> CLong -> Ptr CCaCtx -> IO ()
-- | /ca_poly_shift_left/ /res/ /poly/ /n/ /ctx/ 
--
-- Sets /res/ to /poly/ shifted /n/ coefficients to the left; that is,
-- multiplied by \(x^n\).
foreign import ccall "ca_poly.h ca_poly_shift_left"
  ca_poly_shift_left :: Ptr CCaPoly -> Ptr CCaPoly -> CLong -> Ptr CCaCtx -> IO ()

-- | /_ca_poly_shift_right/ /res/ /poly/ /len/ /n/ /ctx/ 
foreign import ccall "ca_poly.h _ca_poly_shift_right"
  _ca_poly_shift_right :: Ptr CCa -> Ptr CCa -> CLong -> CLong -> Ptr CCaCtx -> IO ()
-- | /ca_poly_shift_right/ /res/ /poly/ /n/ /ctx/ 
--
-- Sets /res/ to /poly/ shifted /n/ coefficients to the right; that is,
-- divided by \(x^n\).
foreign import ccall "ca_poly.h ca_poly_shift_right"
  ca_poly_shift_right :: Ptr CCaPoly -> Ptr CCaPoly -> CLong -> Ptr CCaCtx -> IO ()

-- | /ca_poly_neg/ /res/ /src/ /ctx/ 
--
-- Sets /res/ to the negation of /src/.
foreign import ccall "ca_poly.h ca_poly_neg"
  ca_poly_neg :: Ptr CCaPoly -> Ptr CCaPoly -> Ptr CCaCtx -> IO ()

-- | /_ca_poly_add/ /res/ /poly1/ /len1/ /poly2/ /len2/ /ctx/ 
foreign import ccall "ca_poly.h _ca_poly_add"
  _ca_poly_add :: Ptr CCa -> Ptr CCa -> CLong -> Ptr CCa -> CLong -> Ptr CCaCtx -> IO ()
-- | /ca_poly_add/ /res/ /poly1/ /poly2/ /ctx/ 
--
-- Sets /res/ to the sum of /poly1/ and /poly2/.
foreign import ccall "ca_poly.h ca_poly_add"
  ca_poly_add :: Ptr CCaPoly -> Ptr CCaPoly -> Ptr CCaPoly -> Ptr CCaCtx -> IO ()

-- | /_ca_poly_sub/ /res/ /poly1/ /len1/ /poly2/ /len2/ /ctx/ 
foreign import ccall "ca_poly.h _ca_poly_sub"
  _ca_poly_sub :: Ptr CCa -> Ptr CCa -> CLong -> Ptr CCa -> CLong -> Ptr CCaCtx -> IO ()
-- | /ca_poly_sub/ /res/ /poly1/ /poly2/ /ctx/ 
--
-- Sets /res/ to the difference of /poly1/ and /poly2/.
foreign import ccall "ca_poly.h ca_poly_sub"
  ca_poly_sub :: Ptr CCaPoly -> Ptr CCaPoly -> Ptr CCaPoly -> Ptr CCaCtx -> IO ()

-- | /_ca_poly_mul/ /res/ /poly1/ /len1/ /poly2/ /len2/ /ctx/ 
foreign import ccall "ca_poly.h _ca_poly_mul"
  _ca_poly_mul :: Ptr CCa -> Ptr CCa -> CLong -> Ptr CCa -> CLong -> Ptr CCaCtx -> IO ()
-- | /ca_poly_mul/ /res/ /poly1/ /poly2/ /ctx/ 
--
-- Sets /res/ to the product of /poly1/ and /poly2/.
foreign import ccall "ca_poly.h ca_poly_mul"
  ca_poly_mul :: Ptr CCaPoly -> Ptr CCaPoly -> Ptr CCaPoly -> Ptr CCaCtx -> IO ()

-- | /_ca_poly_mullow/ /C/ /poly1/ /len1/ /poly2/ /len2/ /n/ /ctx/ 
foreign import ccall "ca_poly.h _ca_poly_mullow"
  _ca_poly_mullow :: Ptr CCa -> Ptr CCa -> CLong -> Ptr CCa -> CLong -> CLong -> Ptr CCaCtx -> IO ()
-- | /ca_poly_mullow/ /res/ /poly1/ /poly2/ /n/ /ctx/ 
--
-- Sets /res/ to the product of /poly1/ and /poly2/ truncated to length
-- /n/.
foreign import ccall "ca_poly.h ca_poly_mullow"
  ca_poly_mullow :: Ptr CCaPoly -> Ptr CCaPoly -> Ptr CCaPoly -> CLong -> Ptr CCaCtx -> IO ()

-- | /ca_poly_mul_ca/ /res/ /poly/ /c/ /ctx/ 
--
-- Sets /res/ to /poly/ multiplied by the scalar /c/.
foreign import ccall "ca_poly.h ca_poly_mul_ca"
  ca_poly_mul_ca :: Ptr CCaPoly -> Ptr CCaPoly -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_poly_div_ca/ /res/ /poly/ /c/ /ctx/ 
--
-- Sets /res/ to /poly/ divided by the scalar /c/.
foreign import ccall "ca_poly.h ca_poly_div_ca"
  ca_poly_div_ca :: Ptr CCaPoly -> Ptr CCaPoly -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /_ca_poly_divrem_basecase/ /Q/ /R/ /A/ /lenA/ /B/ /lenB/ /invB/ /ctx/ 
foreign import ccall "ca_poly.h _ca_poly_divrem_basecase"
  _ca_poly_divrem_basecase :: Ptr CCa -> Ptr CCa -> Ptr CCa -> CLong -> Ptr CCa -> CLong -> Ptr CCa -> Ptr CCaCtx -> IO ()
-- | /ca_poly_divrem_basecase/ /Q/ /R/ /A/ /B/ /ctx/ 
foreign import ccall "ca_poly.h ca_poly_divrem_basecase"
  ca_poly_divrem_basecase :: Ptr CCaPoly -> Ptr CCaPoly -> Ptr CCaPoly -> Ptr CCaPoly -> Ptr CCaCtx -> IO CInt
-- | /_ca_poly_divrem/ /Q/ /R/ /A/ /lenA/ /B/ /lenB/ /invB/ /ctx/ 
foreign import ccall "ca_poly.h _ca_poly_divrem"
  _ca_poly_divrem :: Ptr CCa -> Ptr CCa -> Ptr CCa -> CLong -> Ptr CCa -> CLong -> Ptr CCa -> Ptr CCaCtx -> IO ()
-- | /ca_poly_divrem/ /Q/ /R/ /A/ /B/ /ctx/ 
foreign import ccall "ca_poly.h ca_poly_divrem"
  ca_poly_divrem :: Ptr CCaPoly -> Ptr CCaPoly -> Ptr CCaPoly -> Ptr CCaPoly -> Ptr CCaCtx -> IO CInt
-- | /ca_poly_div/ /Q/ /A/ /B/ /ctx/ 
foreign import ccall "ca_poly.h ca_poly_div"
  ca_poly_div :: Ptr CCaPoly -> Ptr CCaPoly -> Ptr CCaPoly -> Ptr CCaCtx -> IO CInt
-- | /ca_poly_rem/ /R/ /A/ /B/ /ctx/ 
--
-- If the leading coefficient of /B/ can be proved invertible, sets /Q/ and
-- /R/ to the quotient and remainder of polynomial division of /A/ by /B/
-- and returns 1. If the leading coefficient cannot be proved invertible,
-- returns 0. The underscore method takes a precomputed inverse of the
-- leading coefficient of /B/.
foreign import ccall "ca_poly.h ca_poly_rem"
  ca_poly_rem :: Ptr CCaPoly -> Ptr CCaPoly -> Ptr CCaPoly -> Ptr CCaCtx -> IO CInt

-- | /_ca_poly_pow_ui_trunc/ /res/ /f/ /flen/ /exp/ /len/ /ctx/ 
foreign import ccall "ca_poly.h _ca_poly_pow_ui_trunc"
  _ca_poly_pow_ui_trunc :: Ptr CCa -> Ptr CCa -> CLong -> CULong -> CLong -> Ptr CCaCtx -> IO ()
-- | /ca_poly_pow_ui_trunc/ /res/ /poly/ /exp/ /len/ /ctx/ 
--
-- Sets /res/ to /poly/ raised to the power /exp/, truncated to length
-- /len/.
foreign import ccall "ca_poly.h ca_poly_pow_ui_trunc"
  ca_poly_pow_ui_trunc :: Ptr CCaPoly -> Ptr CCaPoly -> CULong -> CLong -> Ptr CCaCtx -> IO ()

-- | /_ca_poly_pow_ui/ /res/ /f/ /flen/ /exp/ /ctx/ 
foreign import ccall "ca_poly.h _ca_poly_pow_ui"
  _ca_poly_pow_ui :: Ptr CCa -> Ptr CCa -> CLong -> CULong -> Ptr CCaCtx -> IO ()
-- | /ca_poly_pow_ui/ /res/ /poly/ /exp/ /ctx/ 
--
-- Sets /res/ to /poly/ raised to the power /exp/.
foreign import ccall "ca_poly.h ca_poly_pow_ui"
  ca_poly_pow_ui :: Ptr CCaPoly -> Ptr CCaPoly -> CULong -> Ptr CCaCtx -> IO ()

-- Evaluation and composition --------------------------------------------------

-- | /_ca_poly_evaluate_horner/ /res/ /f/ /len/ /x/ /ctx/ 
foreign import ccall "ca_poly.h _ca_poly_evaluate_horner"
  _ca_poly_evaluate_horner :: Ptr CCa -> Ptr CCa -> CLong -> Ptr CCa -> Ptr CCaCtx -> IO ()
-- | /ca_poly_evaluate_horner/ /res/ /f/ /a/ /ctx/ 
foreign import ccall "ca_poly.h ca_poly_evaluate_horner"
  ca_poly_evaluate_horner :: Ptr CCa -> Ptr CCaPoly -> Ptr CCa -> Ptr CCaCtx -> IO ()
-- | /_ca_poly_evaluate/ /res/ /f/ /len/ /x/ /ctx/ 
foreign import ccall "ca_poly.h _ca_poly_evaluate"
  _ca_poly_evaluate :: Ptr CCa -> Ptr CCa -> CLong -> Ptr CCa -> Ptr CCaCtx -> IO ()
-- | /ca_poly_evaluate/ /res/ /f/ /a/ /ctx/ 
--
-- Sets /res/ to /f/ evaluated at the point /a/.
foreign import ccall "ca_poly.h ca_poly_evaluate"
  ca_poly_evaluate :: Ptr CCa -> Ptr CCaPoly -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /_ca_poly_compose/ /res/ /poly1/ /len1/ /poly2/ /len2/ /ctx/ 
foreign import ccall "ca_poly.h _ca_poly_compose"
  _ca_poly_compose :: Ptr CCa -> Ptr CCa -> CLong -> Ptr CCa -> CLong -> Ptr CCaCtx -> IO ()
-- | /ca_poly_compose/ /res/ /poly1/ /poly2/ /ctx/ 
--
-- Sets /res/ to the composition of /poly1/ with /poly2/.
foreign import ccall "ca_poly.h ca_poly_compose"
  ca_poly_compose :: Ptr CCaPoly -> Ptr CCaPoly -> Ptr CCaPoly -> Ptr CCaCtx -> IO ()

-- Derivative and integral -----------------------------------------------------

-- | /_ca_poly_derivative/ /res/ /poly/ /len/ /ctx/ 
foreign import ccall "ca_poly.h _ca_poly_derivative"
  _ca_poly_derivative :: Ptr CCa -> Ptr CCa -> CLong -> Ptr CCaCtx -> IO ()
-- | /ca_poly_derivative/ /res/ /poly/ /ctx/ 
--
-- Sets /res/ to the derivative of /poly/. The underscore method needs one
-- less coefficient than /len/ for the output array.
foreign import ccall "ca_poly.h ca_poly_derivative"
  ca_poly_derivative :: Ptr CCaPoly -> Ptr CCaPoly -> Ptr CCaCtx -> IO ()

-- | /_ca_poly_integral/ /res/ /poly/ /len/ /ctx/ 
foreign import ccall "ca_poly.h _ca_poly_integral"
  _ca_poly_integral :: Ptr CCa -> Ptr CCa -> CLong -> Ptr CCaCtx -> IO ()
-- | /ca_poly_integral/ /res/ /poly/ /ctx/ 
--
-- Sets /res/ to the integral of /poly/. The underscore method needs one
-- more coefficient than /len/ for the output array.
foreign import ccall "ca_poly.h ca_poly_integral"
  ca_poly_integral :: Ptr CCaPoly -> Ptr CCaPoly -> Ptr CCaCtx -> IO ()

-- Power series division -------------------------------------------------------

-- | /_ca_poly_inv_series/ /res/ /f/ /flen/ /len/ /ctx/ 
foreign import ccall "ca_poly.h _ca_poly_inv_series"
  _ca_poly_inv_series :: Ptr CCa -> Ptr CCa -> CLong -> CLong -> Ptr CCaCtx -> IO ()
-- | /ca_poly_inv_series/ /res/ /f/ /len/ /ctx/ 
--
-- Sets /res/ to the power series inverse of /f/ truncated to length /len/.
foreign import ccall "ca_poly.h ca_poly_inv_series"
  ca_poly_inv_series :: Ptr CCaPoly -> Ptr CCaPoly -> CLong -> Ptr CCaCtx -> IO ()

-- | /_ca_poly_div_series/ /res/ /f/ /flen/ /g/ /glen/ /len/ /ctx/ 
foreign import ccall "ca_poly.h _ca_poly_div_series"
  _ca_poly_div_series :: Ptr CCa -> Ptr CCa -> CLong -> Ptr CCa -> CLong -> CLong -> Ptr CCaCtx -> IO ()
-- | /ca_poly_div_series/ /res/ /f/ /g/ /len/ /ctx/ 
--
-- Sets /res/ to the power series quotient of /f/ and /g/ truncated to
-- length /len/. This function divides by zero if /g/ has constant term
-- zero; the user should manually remove initial zeros when an exact
-- cancellation is required.
foreign import ccall "ca_poly.h ca_poly_div_series"
  ca_poly_div_series :: Ptr CCaPoly -> Ptr CCaPoly -> Ptr CCaPoly -> CLong -> Ptr CCaCtx -> IO ()

-- Elementary functions --------------------------------------------------------

-- | /_ca_poly_exp_series/ /res/ /f/ /flen/ /len/ /ctx/ 
foreign import ccall "ca_poly.h _ca_poly_exp_series"
  _ca_poly_exp_series :: Ptr CCa -> Ptr CCa -> CLong -> CLong -> Ptr CCaCtx -> IO ()
-- | /ca_poly_exp_series/ /res/ /f/ /len/ /ctx/ 
--
-- Sets /res/ to the power series exponential of /f/ truncated to length
-- /len/.
foreign import ccall "ca_poly.h ca_poly_exp_series"
  ca_poly_exp_series :: Ptr CCaPoly -> Ptr CCaPoly -> CLong -> Ptr CCaCtx -> IO ()

-- | /_ca_poly_log_series/ /res/ /f/ /flen/ /len/ /ctx/ 
foreign import ccall "ca_poly.h _ca_poly_log_series"
  _ca_poly_log_series :: Ptr CCa -> Ptr CCa -> CLong -> CLong -> Ptr CCaCtx -> IO ()
-- | /ca_poly_log_series/ /res/ /f/ /len/ /ctx/ 
--
-- Sets /res/ to the power series logarithm of /f/ truncated to length
-- /len/.
foreign import ccall "ca_poly.h ca_poly_log_series"
  ca_poly_log_series :: Ptr CCaPoly -> Ptr CCaPoly -> CLong -> Ptr CCaCtx -> IO ()

-- Greatest common divisor -----------------------------------------------------

-- | /_ca_poly_gcd_euclidean/ /res/ /A/ /lenA/ /B/ /lenB/ /ctx/ 
foreign import ccall "ca_poly.h _ca_poly_gcd_euclidean"
  _ca_poly_gcd_euclidean :: Ptr CCa -> Ptr CCa -> CLong -> Ptr CCa -> CLong -> Ptr CCaCtx -> IO CLong
-- | /ca_poly_gcd_euclidean/ /res/ /A/ /B/ /ctx/ 
foreign import ccall "ca_poly.h ca_poly_gcd_euclidean"
  ca_poly_gcd_euclidean :: Ptr CCaPoly -> Ptr CCaPoly -> Ptr CCaPoly -> Ptr CCaCtx -> IO CInt
-- | /_ca_poly_gcd/ /res/ /A/ /lenA/ /B/ /lenB/ /ctx/ 
foreign import ccall "ca_poly.h _ca_poly_gcd"
  _ca_poly_gcd :: Ptr CCa -> Ptr CCa -> CLong -> Ptr CCa -> CLong -> Ptr CCaCtx -> IO CLong
-- | /ca_poly_gcd/ /res/ /A/ /g/ /ctx/ 
--
-- Sets /res/ to the GCD of /A/ and /B/ and returns 1 on success. On
-- failure, returns 0 leaving the value of /res/ arbitrary. The computation
-- can fail if testing a leading coefficient for zero fails in the
-- execution of the GCD algorithm. The output is normalized to be monic if
-- it is not the zero polynomial.
-- 
-- The underscore methods assume \(\text{lenA} \ge \text{lenB} \ge 1\), and
-- that both /A/ and /B/ have nonzero leading coefficient. They return the
-- length of the GCD, or 0 if the computation fails.
-- 
-- The /euclidean/ version implements the standard Euclidean algorithm. The
-- default version first checks for rational polynomials or attempts to
-- certify numerically that the polynomials are coprime and otherwise falls
-- back to an automatic choice of algorithm (currently only the Euclidean
-- algorithm).
foreign import ccall "ca_poly.h ca_poly_gcd"
  ca_poly_gcd :: Ptr CCaPoly -> Ptr CCaPoly -> Ptr CCaPoly -> Ptr CCaCtx -> IO CInt

-- Roots and factorization -----------------------------------------------------

-- | /ca_poly_factor_squarefree/ /c/ /fac/ /exp/ /F/ /ctx/ 
--
-- Computes the squarefree factorization of /F/, giving a product
-- \(F = c f_1 f_2^2 \ldots f_n^n\) where all \(f_i\) with \(f_i \ne 1\)
-- are squarefree and pairwise coprime. The nontrivial factors \(f_i\) are
-- written to /fac/ and the corresponding exponents are written to /exp/.
-- This algorithm can fail if GCD computation fails internally. Returns 1
-- on success and 0 on failure.
foreign import ccall "ca_poly.h ca_poly_factor_squarefree"
  ca_poly_factor_squarefree :: Ptr CCa -> Ptr CCaPolyVec -> Ptr CULong -> Ptr CCaPoly -> Ptr CCaCtx -> IO CInt

-- | /ca_poly_squarefree_part/ /res/ /poly/ /ctx/ 
--
-- Sets /res/ to the squarefree part of /poly/, normalized to be monic.
-- This algorithm can fail if GCD computation fails internally. Returns 1
-- on success and 0 on failure.
foreign import ccall "ca_poly.h ca_poly_squarefree_part"
  ca_poly_squarefree_part :: Ptr CCaPoly -> Ptr CCaPoly -> Ptr CCaCtx -> IO CInt

-- | /_ca_poly_set_roots/ /poly/ /roots/ /exp/ /n/ /ctx/ 
foreign import ccall "ca_poly.h _ca_poly_set_roots"
  _ca_poly_set_roots :: Ptr CCa -> Ptr CCa -> Ptr CULong -> CLong -> Ptr CCaCtx -> IO ()
-- | /ca_poly_set_roots/ /poly/ /roots/ /exp/ /ctx/ 
--
-- Sets /poly/ to the monic polynomial with the /n/ roots given in the
-- vector /roots/, with multiplicities given in the vector /exp/. In other
-- words, this constructs the polynomial
-- \((x-r_0)^{e_0} (x-r_1)^{e_1} \cdots (x-r_{n-1})^{e_{n-1}}\). Uses
-- binary splitting.
foreign import ccall "ca_poly.h ca_poly_set_roots"
  ca_poly_set_roots :: Ptr CCaPoly -> Ptr CCaVec -> Ptr CULong -> Ptr CCaCtx -> IO ()

-- | /_ca_poly_roots/ /roots/ /poly/ /len/ /ctx/ 
foreign import ccall "ca_poly.h _ca_poly_roots"
  _ca_poly_roots :: Ptr CCa -> Ptr CCa -> CLong -> Ptr CCaCtx -> IO CInt
-- | /ca_poly_roots/ /roots/ /exp/ /poly/ /ctx/ 
--
-- Attempts to compute all complex roots of the given polynomial /poly/. On
-- success, returns 1 and sets /roots/ to a vector containing all the
-- distinct roots with corresponding multiplicities in /exp/. On failure,
-- returns 0 and leaves the values in /roots/ arbitrary. The roots are
-- returned in arbitrary order.
-- 
-- Failure will occur if the leading coefficient of /poly/ cannot be proved
-- to be nonzero, if determining the correct multiplicities fails, or if
-- the builtin algorithms do not have a means to represent the roots
-- symbolically.
-- 
-- The underscore method assumes that the polynomial is squarefree. The
-- non-underscore method performs a squarefree factorization.
foreign import ccall "ca_poly.h ca_poly_roots"
  ca_poly_roots :: Ptr CCaVec -> Ptr CULong -> Ptr CCaPoly -> Ptr CCaCtx -> IO CInt

-- Vectors of polynomials ------------------------------------------------------

-- | /_ca_poly_vec_init/ /len/ /ctx/ 
foreign import ccall "ca_poly.h _ca_poly_vec_init"
  _ca_poly_vec_init :: CLong -> Ptr CCaCtx -> IO (Ptr CCaPoly)
-- | /ca_poly_vec_init/ /res/ /len/ /ctx/ 
--
-- Initializes a vector with /len/ polynomials.
foreign import ccall "ca_poly.h ca_poly_vec_init"
  ca_poly_vec_init :: Ptr CCaPolyVec -> CLong -> Ptr CCaCtx -> IO ()

-- | /_ca_poly_vec_fit_length/ /vec/ /len/ /ctx/ 
--
-- Allocates space for /len/ polynomials in /vec/.
foreign import ccall "ca_poly.h _ca_poly_vec_fit_length"
  _ca_poly_vec_fit_length :: Ptr CCaPolyVec -> CLong -> Ptr CCaCtx -> IO ()

-- | /ca_poly_vec_set_length/ /vec/ /len/ /ctx/ 
--
-- Resizes /vec/ to length /len/, zero-extending if needed.
foreign import ccall "ca_poly.h ca_poly_vec_set_length"
  ca_poly_vec_set_length :: Ptr CCaPolyVec -> CLong -> Ptr CCaCtx -> IO ()

-- | /_ca_poly_vec_clear/ /vec/ /len/ /ctx/ 
foreign import ccall "ca_poly.h _ca_poly_vec_clear"
  _ca_poly_vec_clear :: Ptr CCaPoly -> CLong -> Ptr CCaCtx -> IO ()
-- | /ca_poly_vec_clear/ /vec/ /ctx/ 
--
-- Clears the vector /vec/.
foreign import ccall "ca_poly.h ca_poly_vec_clear"
  ca_poly_vec_clear :: Ptr CCaPolyVec -> Ptr CCaCtx -> IO ()

-- | /ca_poly_vec_append/ /vec/ /poly/ /ctx/ 
--
-- Appends /poly/ to the end of the vector /vec/.
foreign import ccall "ca_poly.h ca_poly_vec_append"
  ca_poly_vec_append :: Ptr CCaPolyVec -> Ptr CCaPoly -> Ptr CCaCtx -> IO ()




