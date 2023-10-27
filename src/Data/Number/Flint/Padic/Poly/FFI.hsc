{-|
module      :  Data.Number.Flint.Padic.Poly.FFI
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de
-}
module Data.Number.Flint.Padic.Poly.FFI (
  -- * Polynomials over p-adic numbers
    PadicPoly (..)
  , CPadicPoly (..)
  , newPadicPoly
  , withPadicPoly
  , withNewPadicPoly
  -- * Memory management
  , padic_poly_init
  , padic_poly_init2
  , padic_poly_realloc
  , padic_poly_fit_length
  , _padic_poly_set_length
  , padic_poly_clear
  , _padic_poly_normalise
  , _padic_poly_canonicalise
  , padic_poly_reduce
  , padic_poly_truncate
  -- * Polynomial parameters
  , padic_poly_degree
  , padic_poly_length
  , padic_poly_val
  -- , padic_poly_prec
  -- * Randomisation
  , padic_poly_randtest
  , padic_poly_randtest_not_zero
  , padic_poly_randtest_val
  -- * Assignment and basic manipulation
  , padic_poly_set_padic
  , padic_poly_set
  , padic_poly_set_si
  , padic_poly_set_ui
  , padic_poly_set_fmpz
  , padic_poly_set_fmpq
  , padic_poly_set_fmpz_poly
  , padic_poly_set_fmpq_poly
  , padic_poly_get_fmpz_poly
  , padic_poly_get_fmpq_poly
  , padic_poly_zero
  , padic_poly_one
  , padic_poly_swap
  -- * Getting and setting coefficients
  , padic_poly_get_coeff_padic
  , padic_poly_set_coeff_padic
  -- * Comparison
  , padic_poly_equal
  , padic_poly_is_zero
  , padic_poly_is_one
  -- * Addition and subtraction
  , _padic_poly_add
  , padic_poly_add
  , _padic_poly_sub
  , padic_poly_sub
  , padic_poly_neg
  -- * Scalar multiplication
  , _padic_poly_scalar_mul_padic
  , padic_poly_scalar_mul_padic
  -- * Multiplication
  , _padic_poly_mul
  , padic_poly_mul
  -- * Powering
  , _padic_poly_pow
  , padic_poly_pow
  -- * Series inversion
  , padic_poly_inv_series
  -- * Derivative
  , _padic_poly_derivative
  , padic_poly_derivative
  -- * Shifting
  , padic_poly_shift_left
  , padic_poly_shift_right
  -- * Evaluation
  , _padic_poly_evaluate_padic
  , padic_poly_evaluate_padic
  -- * Composition
  , _padic_poly_compose
  , padic_poly_compose
  , _padic_poly_compose_pow
  , padic_poly_compose_pow
  -- * Input and output
  , padic_poly_debug
  , _padic_poly_fprint
  , padic_poly_fprint
  , _padic_poly_print
  , padic_poly_print
  , _padic_poly_fprint_pretty
  , padic_poly_fprint_pretty
  , _padic_poly_print_pretty
  , padic_poly_print_pretty
  , padic_poly_get_str_pretty
  , padic_poly_get_str
  -- * Testing
  , _padic_poly_is_canonical
) where

-- polynomials over p-adic numbers ---------------------------------------------

import Control.Monad

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, nullPtr, plusPtr, castPtr )
import Foreign.Storable
import Foreign.Marshal ( free )

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Poly
import Data.Number.Flint.Fmpq
import Data.Number.Flint.Fmpq.Poly
import Data.Number.Flint.Padic

#include <flint/flint.h>
#include <flint/padic.h>
#include <flint/padic_poly.h>

-- padic_poly_t ----------------------------------------------------------------

data PadicPoly = PadicPoly {-# UNPACK #-} !(ForeignPtr CPadicPoly)
data CPadicPoly = CPadicPoly (Ptr CFmpz) CLong CLong CLong CLong

instance Storable CPadicPoly where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size padic_poly_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment padic_poly_t}
  peek ptr = return CPadicPoly
    `ap` (return $ castPtr ptr)
    `ap` #{peek padic_poly_struct, alloc } ptr
    `ap` #{peek padic_poly_struct, length} ptr
    `ap` #{peek padic_poly_struct, val   } ptr
    `ap` #{peek padic_poly_struct, N     } ptr
  poke ptr (CPadicPoly coeffs alloc length val n) = do
    (#poke padic_poly_struct, coeffs) ptr coeffs
    (#poke padic_poly_struct, alloc ) ptr alloc
    (#poke padic_poly_struct, length) ptr length
    (#poke padic_poly_struct, val   ) ptr val
    (#poke padic_poly_struct, N     ) ptr n

newPadicPoly = do
  x <- mallocForeignPtr
  withForeignPtr x padic_poly_init
  addForeignPtrFinalizer p_padic_poly_clear x
  return $ PadicPoly x

{-# INLINE withPadicPoly #-}
withPadicPoly (PadicPoly x) f = do
  withForeignPtr x $ \px -> f px >>= return . (PadicPoly x,)

{-# INLINE withNewPadicPoly #-}
withNewPadicPoly f = do
  x <- newPadicPoly
  withPadicPoly x f
  
-- Memory management -----------------------------------------------------------

-- | /padic_poly_init/ /poly/ 
-- 
-- Initialises @poly@ for use, setting its length to zero. The precision of
-- the polynomial is set to @PADIC_DEFAULT_PREC@. A corresponding call to
-- @padic_poly_clear@ must be made after finishing with the @padic_poly_t@
-- to free the memory used by the polynomial.
foreign import ccall "padic_poly.h padic_poly_init"
  padic_poly_init :: Ptr CPadicPoly -> IO ()

-- | /padic_poly_init2/ /poly/ /alloc/ /prec/ 
-- 
-- Initialises @poly@ with space for at least @alloc@ coefficients and sets
-- the length to zero. The allocated coefficients are all set to zero. The
-- precision is set to @prec@.
foreign import ccall "padic_poly.h padic_poly_init2"
  padic_poly_init2 :: Ptr CPadicPoly -> CLong -> CLong -> IO ()

-- | /padic_poly_realloc/ /poly/ /alloc/ /p/ 
-- 
-- Reallocates the given polynomial to have space for @alloc@ coefficients.
-- If @alloc@ is zero the polynomial is cleared and then reinitialised. If
-- the current length is greater than @alloc@ the polynomial is first
-- truncated to length @alloc@.
foreign import ccall "padic_poly.h padic_poly_realloc"
  padic_poly_realloc :: Ptr CPadicPoly -> CLong -> Ptr CFmpz -> IO ()

-- | /padic_poly_fit_length/ /poly/ /len/ 
-- 
-- If @len@ is greater than the number of coefficients currently allocated,
-- then the polynomial is reallocated to have space for at least @len@
-- coefficients. No data is lost when calling this function.
-- 
-- The function efficiently deals with the case where @fit_length@ is
-- called many times in small increments by at least doubling the number of
-- allocated coefficients when length is larger than the number of
-- coefficients currently allocated.
foreign import ccall "padic_poly.h padic_poly_fit_length"
  padic_poly_fit_length :: Ptr CPadicPoly -> CLong -> IO ()

-- | /_padic_poly_set_length/ /poly/ /len/ 
-- 
-- Demotes the coefficients of @poly@ beyond @len@ and sets the length of
-- @poly@ to @len@.
-- 
-- Note that if the current length is greater than @len@ the polynomial may
-- no slonger be in canonical form.
foreign import ccall "padic_poly.h _padic_poly_set_length"
  _padic_poly_set_length :: Ptr CPadicPoly -> CLong -> IO ()

-- | /padic_poly_clear/ /poly/ 
-- 
-- Clears the given polynomial, releasing any memory used. It must be
-- reinitialised in order to be used again.
foreign import ccall "padic_poly.h padic_poly_clear"
  padic_poly_clear :: Ptr CPadicPoly -> IO ()

foreign import ccall "padic_poly.h &padic_poly_clear"
  p_padic_poly_clear :: FunPtr (Ptr CPadicPoly -> IO ())

-- | /_padic_poly_normalise/ /poly/ 
-- 
-- Sets the length of @poly@ so that the top coefficient is non-zero. If
-- all coefficients are zero, the length is set to zero. This function is
-- mainly used internally, as all functions guarantee normalisation.
foreign import ccall "padic_poly.h _padic_poly_normalise"
  _padic_poly_normalise :: Ptr CPadicPoly -> IO ()

-- | /_padic_poly_canonicalise/ /poly/ /v/ /len/ /p/ 
-- 
-- Brings the polynomial @poly@ into canonical form, assuming that it is
-- normalised already. Does /not/ carry out any reduction.
foreign import ccall "padic_poly.h _padic_poly_canonicalise"
  _padic_poly_canonicalise :: Ptr CFmpz -> Ptr CLong -> CLong -> Ptr CFmpz -> IO ()

-- | /padic_poly_reduce/ /poly/ /ctx/ 
-- 
-- Reduces the polynomial @poly@ modulo \(p^N\), assuming that it is in
-- canonical form already.
foreign import ccall "padic_poly.h padic_poly_reduce"
  padic_poly_reduce :: Ptr CPadicPoly -> Ptr CPadicCtx -> IO ()

-- | /padic_poly_truncate/ /poly/ /n/ /p/ 
-- 
-- Truncates the polynomial to length at most~\`n\`.
foreign import ccall "padic_poly.h padic_poly_truncate"
  padic_poly_truncate :: Ptr CPadicPoly -> CLong -> Ptr CFmpz -> IO ()

-- Polynomial parameters -------------------------------------------------------

-- | /padic_poly_degree/ /poly/ 
-- 
-- Returns the degree of the polynomial @poly@.
foreign import ccall "padic_poly.h padic_poly_degree"
  padic_poly_degree :: Ptr CPadicPoly -> IO CLong

-- | /padic_poly_length/ /poly/ 
-- 
-- Returns the length of the polynomial @poly@.
foreign import ccall "padic_poly.h padic_poly_length"
  padic_poly_length :: Ptr CPadicPoly -> IO CLong

-- | /padic_poly_val/ /poly/ 
-- 
-- Returns the valuation of the polynomial @poly@, which is defined to be
-- the minimum valuation of all its coefficients.
-- 
-- The valuation of the zero polynomial is~\`0\`.
-- 
-- Note that this is implemented as a macro and can be used as either a
-- @lvalue@ or a @rvalue@.
foreign import ccall "padic_poly.h padic_poly_val"
  padic_poly_val :: Ptr CPadicPoly -> IO CLong

-- | /padic_poly_prec/ /poly/ 
-- 
-- Returns the precision of the polynomial @poly@.
-- 
-- Note that this is implemented as a macro and can be used as either a
-- @lvalue@ or a @rvalue@.
-- 
-- Note that increasing the precision might require a call to
-- @padic_poly_reduce@.
-- foreign import ccall "padic_poly.h padic_poly_prec"
--   padic_poly_prec :: Ptr CPadicPoly -> IO CLong

-- Randomisation ---------------------------------------------------------------

-- | /padic_poly_randtest/ /f/ /state/ /len/ /ctx/ 
-- 
-- Sets \(f\) to a random polynomial of length at most @len@ with entries
-- reduced modulo \(p^N\).
foreign import ccall "padic_poly.h padic_poly_randtest"
  padic_poly_randtest :: Ptr CPadicPoly -> Ptr CFRandState -> CLong -> Ptr CPadicCtx -> IO ()

-- | /padic_poly_randtest_not_zero/ /f/ /state/ /len/ /ctx/ 
-- 
-- Sets \(f\) to a non-zero random polynomial of length at most @len@ with
-- entries reduced modulo \(p^N\).
foreign import ccall "padic_poly.h padic_poly_randtest_not_zero"
  padic_poly_randtest_not_zero :: Ptr CPadicPoly -> Ptr CFRandState -> CLong -> Ptr CPadicCtx -> IO ()

-- | /padic_poly_randtest_val/ /f/ /state/ /val/ /len/ /ctx/ 
-- 
-- Sets \(f\) to a random polynomial of length at most @len@ with at most
-- the prescribed valuation @val@ and entries reduced modulo \(p^N\).
-- 
-- Specifically, we aim to set the valuation to be exactly equal to @val@,
-- but do not check for additional cancellation when creating the
-- coefficients.
foreign import ccall "padic_poly.h padic_poly_randtest_val"
  padic_poly_randtest_val :: Ptr CPadicPoly -> Ptr CFRandState -> CLong -> CLong -> Ptr CPadicCtx -> IO ()

-- Assignment and basic manipulation -------------------------------------------

-- | /padic_poly_set_padic/ /poly/ /x/ /ctx/ 
-- 
-- Sets the polynomial @poly@ to the \(p\)-adic number \(x\), reduced to
-- the precision of the polynomial.
foreign import ccall "padic_poly.h padic_poly_set_padic"
  padic_poly_set_padic :: Ptr CPadicPoly -> Ptr CPadic -> Ptr CPadicCtx -> IO ()

-- | /padic_poly_set/ /poly1/ /poly2/ /ctx/ 
-- 
-- Sets the polynomial @poly1@ to the polynomial @poly2@, reduced to the
-- precision of @poly1@.
foreign import ccall "padic_poly.h padic_poly_set"
  padic_poly_set :: Ptr CPadicPoly -> Ptr CPadicPoly -> Ptr CPadicCtx -> IO ()

-- | /padic_poly_set_si/ /poly/ /x/ /ctx/ 
-- 
-- Sets the polynomial @poly@ to the @signed slong@ integer \(x\) reduced
-- to the precision of the polynomial.
foreign import ccall "padic_poly.h padic_poly_set_si"
  padic_poly_set_si :: Ptr CPadicPoly -> CLong -> Ptr CPadicCtx -> IO ()

-- | /padic_poly_set_ui/ /poly/ /x/ /ctx/ 
-- 
-- Sets the polynomial @poly@ to the @unsigned slong@ integer \(x\) reduced
-- to the precision of the polynomial.
foreign import ccall "padic_poly.h padic_poly_set_ui"
  padic_poly_set_ui :: Ptr CPadicPoly -> CULong -> Ptr CPadicCtx -> IO ()

-- | /padic_poly_set_fmpz/ /poly/ /x/ /ctx/ 
-- 
-- Sets the polynomial @poly@ to the integer \(x\) reduced to the precision
-- of the polynomial.
foreign import ccall "padic_poly.h padic_poly_set_fmpz"
  padic_poly_set_fmpz :: Ptr CPadicPoly -> Ptr CFmpz -> Ptr CPadicCtx -> IO ()

-- | /padic_poly_set_fmpq/ /poly/ /x/ /ctx/ 
-- 
-- Sets the polynomial @poly@ to the value of the rational \(x\), reduced
-- to the precision of the polynomial.
foreign import ccall "padic_poly.h padic_poly_set_fmpq"
  padic_poly_set_fmpq :: Ptr CPadicPoly -> Ptr CFmpq -> Ptr CPadicCtx -> IO ()

-- | /padic_poly_set_fmpz_poly/ /rop/ /op/ /ctx/ 
-- 
-- Sets the polynomial @rop@ to the integer polynomial @op@ reduced to the
-- precision of the polynomial.
foreign import ccall "padic_poly.h padic_poly_set_fmpz_poly"
  padic_poly_set_fmpz_poly :: Ptr CPadicPoly -> Ptr CFmpzPoly -> Ptr CPadicCtx -> IO ()

-- | /padic_poly_set_fmpq_poly/ /rop/ /op/ /ctx/ 
-- 
-- Sets the polynomial @rop@ to the value of the rational polynomial @op@,
-- reduced to the precision of the polynomial.
foreign import ccall "padic_poly.h padic_poly_set_fmpq_poly"
  padic_poly_set_fmpq_poly :: Ptr CPadicPoly -> Ptr CFmpqPoly -> Ptr CPadicCtx -> IO ()

-- | /padic_poly_get_fmpz_poly/ /rop/ /op/ /ctx/ 
-- 
-- Sets the integer polynomial @rop@ to the value of the \(p\)-adic
-- polynomial @op@ and returns \(1\) if the polynomial is \(p\)-adically
-- integral. Otherwise, returns \(0\).
foreign import ccall "padic_poly.h padic_poly_get_fmpz_poly"
  padic_poly_get_fmpz_poly :: Ptr CFmpzPoly -> Ptr CPadicPoly -> Ptr CPadicCtx -> IO CInt

-- | /padic_poly_get_fmpq_poly/ /rop/ /op/ /ctx/ 
-- 
-- Sets @rop@ to the rational polynomial corresponding to the \(p\)-adic
-- polynomial @op@.
foreign import ccall "padic_poly.h padic_poly_get_fmpq_poly"
  padic_poly_get_fmpq_poly :: Ptr CFmpqPoly -> Ptr CPadicPoly -> Ptr CPadicCtx -> IO ()

-- | /padic_poly_zero/ /poly/ 
-- 
-- Sets @poly@ to the zero polynomial.
foreign import ccall "padic_poly.h padic_poly_zero"
  padic_poly_zero :: Ptr CPadicPoly -> IO ()

-- | /padic_poly_one/ /poly/ 
-- 
-- Sets @poly@ to the constant polynomial \(1\), reduced to the precision
-- of the polynomial.
foreign import ccall "padic_poly.h padic_poly_one"
  padic_poly_one :: Ptr CPadicPoly -> IO ()

-- | /padic_poly_swap/ /poly1/ /poly2/ 
-- 
-- Swaps the two polynomials @poly1@ and @poly2@, including their
-- precisions.
-- 
-- This is done efficiently by swapping pointers.
foreign import ccall "padic_poly.h padic_poly_swap"
  padic_poly_swap :: Ptr CPadicPoly -> Ptr CPadicPoly -> IO ()

-- Getting and setting coefficients --------------------------------------------

-- | /padic_poly_get_coeff_padic/ /c/ /poly/ /n/ /ctx/ 
-- 
-- Sets \(c\) to the coefficient of \(x^n\) in the polynomial, reduced
-- modulo the precision of \(c\).
foreign import ccall "padic_poly.h padic_poly_get_coeff_padic"
  padic_poly_get_coeff_padic :: Ptr CPadic -> Ptr CPadicPoly -> CLong -> Ptr CPadicCtx -> IO ()

-- | /padic_poly_set_coeff_padic/ /f/ /n/ /c/ /ctx/ 
-- 
-- Sets the coefficient of \(x^n\) in the polynomial \(f\) to \(c\),
-- reduced to the precision of the polynomial \(f\).
-- 
-- Note that this operation can take linear time in the length of the
-- polynomial.
foreign import ccall "padic_poly.h padic_poly_set_coeff_padic"
  padic_poly_set_coeff_padic :: Ptr CPadicPoly -> CLong -> Ptr CPadic -> Ptr CPadicCtx -> IO ()

-- Comparison ------------------------------------------------------------------

-- | /padic_poly_equal/ /poly1/ /poly2/ 
-- 
-- Returns whether the two polynomials @poly1@ and @poly2@ are equal.
foreign import ccall "padic_poly.h padic_poly_equal"
  padic_poly_equal :: Ptr CPadicPoly -> Ptr CPadicPoly -> IO CInt

-- | /padic_poly_is_zero/ /poly/ 
-- 
-- Returns whether the polynomial @poly@ is the zero polynomial.
foreign import ccall "padic_poly.h padic_poly_is_zero"
  padic_poly_is_zero :: Ptr CPadicPoly -> IO CInt

-- | /padic_poly_is_one/ /poly/ /ctx/ 
-- 
-- Returns whether the polynomial @poly@ is equal to the constant
-- polynomial~\`1\`, taking the precision of the polynomial into account.
foreign import ccall "padic_poly.h padic_poly_is_one"
  padic_poly_is_one :: Ptr CPadicPoly -> Ptr CPadicCtx -> IO CInt

-- Addition and subtraction ----------------------------------------------------

-- | /_padic_poly_add/ /rop/ /rval/ /N/ /op1/ /val1/ /len1/ /N1/ /op2/ /val2/ /len2/ /N2/ /ctx/ 
-- 
-- Sets @(rop, *val, FLINT_MAX(len1, len2)@ to the sum of
-- @(op1, val1, len1)@ and @(op2, val2, len2)@.
-- 
-- Assumes that the input is reduced and guarantees that this is also the
-- case for the output.
-- 
-- Assumes that \(\min\{v_1, v_2\} < N\).
-- 
-- Supports aliasing between the output and input arguments.
foreign import ccall "padic_poly.h _padic_poly_add"
  _padic_poly_add :: Ptr CFmpz -> Ptr CLong -> CLong -> Ptr CFmpz -> CLong -> CLong -> CLong -> Ptr CFmpz -> CLong -> CLong -> CLong -> Ptr CPadicCtx -> IO ()

-- | /padic_poly_add/ /f/ /g/ /h/ /ctx/ 
-- 
-- Sets \(f\) to the sum \(g + h\).
foreign import ccall "padic_poly.h padic_poly_add"
  padic_poly_add :: Ptr CPadicPoly -> Ptr CPadicPoly -> Ptr CPadicPoly -> Ptr CPadicCtx -> IO ()

-- | /_padic_poly_sub/ /rop/ /rval/ /op1/ /val1/ /len1/ /op2/ /val2/ /len2/ /ctx/ 
-- 
-- Sets @(rop, *val, FLINT_MAX(len1, len2)@ to the difference of
-- @(op1, val1, len1)@ and @(op2, val2, len2)@.
-- 
-- Assumes that the input is reduced and guarantees that this is also the
-- case for the output.
-- 
-- Assumes that \(\min\{v_1, v_2\} < N\).
-- 
-- Support aliasing between the output and input arguments.
foreign import ccall "padic_poly.h _padic_poly_sub"
  _padic_poly_sub :: Ptr CFmpz -> Ptr CLong -> Ptr CFmpz -> CLong -> CLong -> Ptr CFmpz -> CLong -> CLong -> Ptr CPadicCtx -> IO ()

-- | /padic_poly_sub/ /f/ /g/ /h/ /ctx/ 
-- 
-- Sets \(f\) to the difference \(g - h\).
foreign import ccall "padic_poly.h padic_poly_sub"
  padic_poly_sub :: Ptr CPadicPoly -> Ptr CPadicPoly -> Ptr CPadicPoly -> Ptr CPadicCtx -> IO ()

-- | /padic_poly_neg/ /f/ /g/ /ctx/ 
-- 
-- Sets \(f\) to \(-g\).
foreign import ccall "padic_poly.h padic_poly_neg"
  padic_poly_neg :: Ptr CPadicPoly -> Ptr CPadicPoly -> Ptr CPadicCtx -> IO ()

-- Scalar multiplication -------------------------------------------------------

-- | /_padic_poly_scalar_mul_padic/ /rop/ /rval/ /op/ /val/ /len/ /c/ /ctx/ 
-- 
-- Sets @(rop, *rval, len)@ to @(op, val, len)@ multiplied by the scalar
-- \(c\).
-- 
-- The result will only be correctly reduced if the polynomial is non-zero.
-- Otherwise, the array @(rop, len)@ will be set to zero but the valuation
-- @*rval@ might be wrong.
foreign import ccall "padic_poly.h _padic_poly_scalar_mul_padic"
  _padic_poly_scalar_mul_padic :: Ptr CFmpz -> Ptr CLong -> Ptr CFmpz -> CLong -> CLong -> Ptr CPadic -> Ptr CPadicCtx -> IO ()

-- | /padic_poly_scalar_mul_padic/ /rop/ /op/ /c/ /ctx/ 
-- 
-- Sets the polynomial @rop@ to the product of the polynomial @op@ and the
-- \(p\)-adic number \(c\), reducing the result modulo \(p^N\).
foreign import ccall "padic_poly.h padic_poly_scalar_mul_padic"
  padic_poly_scalar_mul_padic :: Ptr CPadicPoly -> Ptr CPadicPoly -> Ptr CPadic -> Ptr CPadicCtx -> IO ()

-- Multiplication --------------------------------------------------------------

-- | /_padic_poly_mul/ /rop/ /rval/ /N/ /op1/ /val1/ /len1/ /op2/ /val2/ /len2/ /ctx/ 
-- 
-- Sets @(rop, *rval, len1 + len2 - 1)@ to the product of
-- @(op1, val1, len1)@ and @(op2, val2, len2)@.
-- 
-- Assumes that the resulting valuation @*rval@, which is the sum of the
-- valuations @val1@ and @val2@, is less than the precision~\`N\` of the
-- context.
-- 
-- Assumes that @len1 >= len2 > 0@.
foreign import ccall "padic_poly.h _padic_poly_mul"
  _padic_poly_mul :: Ptr CFmpz -> Ptr CLong -> CLong -> Ptr CFmpz -> CLong -> CLong -> Ptr CFmpz -> CLong -> CLong -> Ptr CPadicCtx -> IO ()

-- | /padic_poly_mul/ /res/ /poly1/ /poly2/ /ctx/ 
-- 
-- Sets the polynomial @res@ to the product of the two polynomials @poly1@
-- and @poly2@, reduced modulo \(p^N\).
foreign import ccall "padic_poly.h padic_poly_mul"
  padic_poly_mul :: Ptr CPadicPoly -> Ptr CPadicPoly -> Ptr CPadicPoly -> Ptr CPadicCtx -> IO ()

-- Powering --------------------------------------------------------------------

-- | /_padic_poly_pow/ /rop/ /rval/ /N/ /op/ /val/ /len/ /e/ /ctx/ 
-- 
-- Sets the polynomial @(rop, *rval, e (len - 1) + 1)@ to the polynomial
-- @(op, val, len)@ raised to the power~\`e\`.
-- 
-- Assumes that \(e > 1\) and @len > 0@.
-- 
-- Does not support aliasing between the input and output arguments.
foreign import ccall "padic_poly.h _padic_poly_pow"
  _padic_poly_pow :: Ptr CFmpz -> Ptr CLong -> CLong -> Ptr CFmpz -> CLong -> CLong -> CULong -> Ptr CPadicCtx -> IO ()

-- | /padic_poly_pow/ /rop/ /op/ /e/ /ctx/ 
-- 
-- Sets the polynomial @rop@ to the polynomial @op@ raised to the
-- power~\`e\`, reduced to the precision in @rop@.
-- 
-- In the special case \(e = 0\), sets @rop@ to the constant polynomial one
-- reduced to the precision of @rop@. Also note that when \(e = 1\), this
-- operation sets @rop@ to @op@ and then reduces @rop@.
-- 
-- When the valuation of the input polynomial is negative, this results in
-- a loss of \(p\)-adic precision. Suppose that the input polynomial is
-- given to precision~\`N\` and has valuation~\`v \< 0\`. The result then
-- has valuation \(e v < 0\) but is only correct to precision
-- \(N + (e - 1) v\).
foreign import ccall "padic_poly.h padic_poly_pow"
  padic_poly_pow :: Ptr CPadicPoly -> Ptr CPadicPoly -> CULong -> Ptr CPadicCtx -> IO ()

-- Series inversion ------------------------------------------------------------

-- | /padic_poly_inv_series/ /g/ /f/ /n/ /ctx/ 
-- 
-- Computes the power series inverse \(g\) of \(f\) modulo \(X^n\), where
-- \(n \geq 1\).
-- 
-- Given the polynomial \(f \in \mathbf{Q}[X] \subset \mathbf{Q}_p[X]\),
-- there exists a unique polynomial \(f^{-1} \in \mathbf{Q}[X]\) such that
-- \(f f^{-1} = 1\) modulo \(X^n\). This function sets \(g\) to \(f^{-1}\)
-- reduced modulo \(p^N\).
-- 
-- Assumes that the constant coefficient of \(f\) is non-zero.
-- 
-- Moreover, assumes that the valuation of the constant coefficient of
-- \(f\) is minimal among the coefficients of \(f\).
-- 
-- Note that the result \(g\) is zero if and only if
-- \(- \operatorname{ord}_p(f) \geq N\).
foreign import ccall "padic_poly.h padic_poly_inv_series"
  padic_poly_inv_series :: Ptr CPadicPoly -> Ptr CPadicPoly -> CLong -> Ptr CPadicCtx -> IO ()

-- Derivative ------------------------------------------------------------------

-- | /_padic_poly_derivative/ /rop/ /rval/ /N/ /op/ /val/ /len/ /ctx/ 
-- 
-- Sets @(rop, rval)@ to the derivative of @(op, val)@ reduced modulo
-- \(p^N\).
-- 
-- Supports aliasing of the input and the output parameters.
foreign import ccall "padic_poly.h _padic_poly_derivative"
  _padic_poly_derivative :: Ptr CFmpz -> Ptr CLong -> CLong -> Ptr CFmpz -> CLong -> CLong -> Ptr CPadicCtx -> IO ()

-- | /padic_poly_derivative/ /rop/ /op/ /ctx/ 
-- 
-- Sets @rop@ to the derivative of @op@, reducing the result modulo the
-- precision of @rop@.
foreign import ccall "padic_poly.h padic_poly_derivative"
  padic_poly_derivative :: Ptr CPadicPoly -> Ptr CPadicPoly -> Ptr CPadicCtx -> IO ()

-- Shifting --------------------------------------------------------------------

-- | /padic_poly_shift_left/ /rop/ /op/ /n/ /ctx/ 
-- 
-- Notationally, sets the polynomial @rop@ to the polynomial @op@
-- multiplied by \(x^n\), where \(n \geq 0\), and reduces the result.
foreign import ccall "padic_poly.h padic_poly_shift_left"
  padic_poly_shift_left :: Ptr CPadicPoly -> Ptr CPadicPoly -> CLong -> Ptr CPadicCtx -> IO ()

-- | /padic_poly_shift_right/ /rop/ /op/ /n/ 
-- 
-- Notationally, sets the polynomial @rop@ to the polynomial @op@ after
-- floor division by \(x^n\), where \(n \geq 0\), ensuring the result is
-- reduced.
foreign import ccall "padic_poly.h padic_poly_shift_right"
  padic_poly_shift_right :: Ptr CPadicPoly -> Ptr CPadicPoly -> CLong -> IO ()

-- Evaluation ------------------------------------------------------------------

foreign import ccall "padic_poly.h _padic_poly_evaluate_padic"
  _padic_poly_evaluate_padic :: Ptr CFmpz -> Ptr CLong -> CLong -> Ptr CFmpz -> CLong -> CLong -> Ptr CFmpz -> CLong -> Ptr CPadicCtx -> IO ()

-- | /_padic_poly_evaluate_padic/ /u/ /v/ /N/ /poly/ /val/ /len/ /a/ /b/ /ctx/ 
-- 
-- Sets the \(p\)-adic number @y@ to @poly@ evaluated at \(a\), reduced in
-- the given context.
-- 
-- Suppose that the polynomial can be written as \(F(X) = p^w f(X)\) with
-- \(\operatorname{ord}_p(f) = 1\), that \(\operatorname{ord}_p(a) = b\)
-- and that both are defined to precision~\`N\`. Then \(f\) is defined to
-- precision \(N-w\) and so \(f(a)\) is defined to precision \(N-w\) when
-- \(a\) is integral and \(N-w+(n-1)b\) when \(b < 0\), where
-- \(n = \deg(f)\). Thus, \(y = F(a)\) is defined to precision \(N\) when
-- \(a\) is integral and \(N+(n-1)b\) when \(b < 0\).

foreign import ccall "flint/padic_poly.h padic_poly_evaluate_padic"
  padic_poly_evaluate_padic :: Ptr CPadic -> Ptr CPadicPoly -> Ptr CPadic -> Ptr CPadicCtx -> IO ()

-- Composition -----------------------------------------------------------------

-- | /_padic_poly_compose/ /rop/ /rval/ /N/ /op1/ /val1/ /len1/ /op2/ /val2/ /len2/ /ctx/ 
-- 
-- Sets @(rop, *rval, (len1-1)*(len2-1)+1)@ to the composition of the two
-- input polynomials, reducing the result modulo \(p^N\).
-- 
-- Assumes that @len1@ is non-zero.
-- 
-- Does not support aliasing.
foreign import ccall "padic_poly.h _padic_poly_compose"
  _padic_poly_compose :: Ptr CFmpz -> Ptr CLong -> CLong -> Ptr CFmpz -> CLong -> CLong -> Ptr CFmpz -> CLong -> CLong -> Ptr CPadicCtx -> IO ()

-- | /padic_poly_compose/ /rop/ /op1/ /op2/ /ctx/ 
-- 
-- Sets @rop@ to the composition of @op1@ and @op2@, reducing the result in
-- the given context.
-- 
-- To be clear about the order of composition, let \(f(X)\) and \(g(X)\)
-- denote the polynomials @op1@ and @op2@, respectively. Then @rop@ is set
-- to \(f(g(X))\).
foreign import ccall "padic_poly.h padic_poly_compose"
  padic_poly_compose :: Ptr CPadicPoly -> Ptr CPadicPoly -> Ptr CPadicPoly -> Ptr CPadicCtx -> IO ()

-- | /_padic_poly_compose_pow/ /rop/ /rval/ /N/ /op/ /val/ /len/ /k/ /ctx/ 
-- 
-- Sets @(rop, *rval, (len - 1)*k + 1)@ to the composition of
-- @(op, val, len)@ and the monomial \(x^k\), where \(k \geq 1\).
-- 
-- Assumes that @len@ is positive.
-- 
-- Supports aliasing between the input and output polynomials.
foreign import ccall "padic_poly.h _padic_poly_compose_pow"
  _padic_poly_compose_pow :: Ptr CFmpz -> Ptr CLong -> CLong -> Ptr CFmpz -> CLong -> CLong -> CLong -> Ptr CPadicCtx -> IO ()

-- | /padic_poly_compose_pow/ /rop/ /op/ /k/ /ctx/ 
-- 
-- Sets @rop@ to the composition of @op@ and the monomial \(x^k\), where
-- \(k \geq 1\).
-- 
-- Note that no reduction takes place.
foreign import ccall "padic_poly.h padic_poly_compose_pow"
  padic_poly_compose_pow :: Ptr CPadicPoly -> Ptr CPadicPoly -> CLong -> Ptr CPadicCtx -> IO ()

-- Input and output ------------------------------------------------------------

-- | /padic_poly_debug/ /poly/ 
-- 
-- Prints the data defining the \(p\)-adic polynomial @poly@ in a simple
-- format useful for debugging purposes.
-- 
-- In the current implementation, always returns \(1\).
foreign import ccall "padic_poly.h padic_poly_debug"
  padic_poly_debug :: Ptr CPadicPoly -> IO CInt

-- | /_padic_poly_fprint/ /file/ /poly/ /val/ /len/ /ctx/ 
-- 
-- Prints a simple representation of the polynomial @poly@ to the stream
-- @file@.
-- 
-- A non-zero polynomial is represented by the number of coefficients, two
-- spaces, followed by a list of the coefficients, which are printed in a
-- way depending on the print mode,
-- 
-- In the @PADIC_TERSE@ mode, the coefficients are printed as rational
-- numbers.
-- 
-- The @PADIC_SERIES@ mode is currently not supported and will raise an
-- abort signal.
-- 
-- In the @PADIC_VAL_UNIT@ mode, the coefficients are printed in the form
-- \(p^v u\).
-- 
-- The zero polynomial is represented by @\"0\"@.
-- 
-- In the current implementation, always returns \(1\).
foreign import ccall "padic_poly.h _padic_poly_fprint"
  _padic_poly_fprint :: Ptr CFile -> Ptr CFmpz -> CLong -> CLong -> Ptr CPadicCtx -> IO CInt

foreign import ccall "flint/padic_poly.h padic_poly_fprint"
  padic_poly_fprint :: Ptr CFile -> Ptr CPadicPoly -> Ptr CPadicCtx -> IO CInt

-- | /_padic_poly_print/ /poly/ /val/ /len/ /ctx/ 
-- 
-- Prints a simple representation of the polynomial @poly@ to @stdout@.
-- 
-- In the current implementation, always returns \(1\).
foreign import ccall "padic_poly.h _padic_poly_print"
  _padic_poly_print :: Ptr CFmpz -> CLong -> CLong -> Ptr CPadicCtx -> IO CInt

padic_poly_print :: Ptr CPadicPoly -> Ptr CPadicCtx -> IO CInt
padic_poly_print poly ctx = do
  cs <- padic_poly_get_str nullPtr poly ctx
  s <- peekCString cs
  free cs
  putStr s
  return (1 :: CInt)

foreign import ccall "padic_poly.h _padic_poly_fprint_pretty"
  _padic_poly_fprint_pretty :: Ptr CFile -> Ptr CFmpz -> CLong -> CLong -> CString -> Ptr CPadicCtx -> IO CInt

foreign import ccall "flint/padic_poly.h _padic_poly_print_pretty"
  _padic_poly_print_pretty :: Ptr CFmpz -> CLong -> CLong -> CString -> Ptr CPadicCtx -> IO CInt

foreign import ccall "flint/padic_poly.h padic_poly_fprint_pretty"
  padic_poly_fprint_pretty :: Ptr CFile -> Ptr CPadicPoly -> CString -> Ptr CPadicCtx -> IO CInt

padic_poly_print_pretty :: Ptr CPadicPoly -> CString -> Ptr CPadicCtx -> IO CInt
padic_poly_print_pretty  poly var ctx = do
  cs <- padic_poly_get_str_pretty poly var ctx
  s <- peekCString cs
  free cs
  putStr s
  return (1 :: CInt)


foreign import ccall "padic_poly_get_str"
  padic_poly_get_str :: CString -> Ptr CPadicPoly -> Ptr CPadicCtx -> IO CString
  
foreign import ccall "padic_poly_get_str_pretty"
  padic_poly_get_str_pretty :: Ptr CPadicPoly -> CString -> Ptr CPadicCtx -> IO CString

-- Testing ---------------------------------------------------------------------

foreign import ccall "padic_poly.h _padic_poly_is_canonical"
  _padic_poly_is_canonical :: Ptr CFmpz -> CLong -> CLong -> Ptr CPadicCtx -> IO CInt

foreign import ccall "flint/padic_poly.h padic_poly_is_canonical"
 padic_poly_is_canonical :: Ptr CPadicPoly -> Ptr CPadicCtx -> IO CInt 

foreign import ccall "flint/padic_poly.h _padic_poly_is_reduced"
  _padic_poly_is_reduced :: Ptr CFmpz -> CLong -> CLong -> Ptr CPadicCtx -> IO CInt

foreign import ccall "flint/padic_poly.h padic_poly_is_reduced"
 padic_poly_is_reduced :: Ptr CPadicPoly -> Ptr CPadicCtx -> IO CInt 
