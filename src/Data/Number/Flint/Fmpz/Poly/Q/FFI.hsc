{-# language
    CApiFFI
  , FlexibleInstances
  , ForeignFunctionInterface
  , TupleSections
  #-}
  
module Data.Number.Flint.Fmpz.Poly.Q.FFI (
  -- * Rational functions over the rational numbers
    FmpzPolyQ (..)
  , CFmpzPolyQ (..)
  , newFmpzPolyQ
  , withFmpzPolyQ
  , withFmpzPolyQNum
  , withFmpzPolyQDen
  -- * Memory management
  , fmpz_poly_q_init
  , fmpz_poly_q_clear
  -- , fmpz_poly_q_numref
  -- , fmpz_poly_q_denref
  , fmpz_poly_q_canonicalise
  , fmpz_poly_q_is_canonical
  -- * Randomisation
  , fmpz_poly_q_randtest
  , fmpz_poly_q_randtest_not_zero
  -- * Assignment
  , fmpz_poly_q_set
  , fmpz_poly_q_set_si
  , fmpz_poly_q_swap
  , fmpz_poly_q_zero
  , fmpz_poly_q_one
  , fmpz_poly_q_neg
  , fmpz_poly_q_inv
  -- * Comparison
  , fmpz_poly_q_is_zero
  , fmpz_poly_q_is_one
  , fmpz_poly_q_equal
  -- * Addition and subtraction
  , fmpz_poly_q_add
  , fmpz_poly_q_sub
  , fmpz_poly_q_addmul
  , fmpz_poly_q_submul
  -- * Scalar multiplication and division
  , fmpz_poly_q_scalar_mul_si
  , fmpz_poly_q_scalar_mul_fmpz
  , fmpz_poly_q_scalar_mul_fmpq
  , fmpz_poly_q_scalar_div_si
  , fmpz_poly_q_scalar_div_fmpz
  , fmpz_poly_q_scalar_div_fmpq
  -- * Multiplication and division
  , fmpz_poly_q_mul
  , fmpz_poly_q_div
  -- * Powering
  , fmpz_poly_q_pow
  -- * Derivative
  , fmpz_poly_q_derivative
  -- * Evaluation
  , fmpz_poly_q_evaluate_fmpq
  -- * Input and output
  , fmpz_poly_q_set_str
  , fmpz_poly_q_get_str
  , fmpz_poly_q_get_str_pretty
  , fmpz_poly_q_print
  , fmpz_poly_q_print_pretty
) where 

-- Rational functions over the rational numbers --------------------------------

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.C.Types
import Foreign.C.String
import Foreign.Storable
import Foreign.Marshal.Array ( advancePtr )

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Poly
import Data.Number.Flint.Fmpq
import Data.Number.Flint.Fmpq.Poly

#include <flint/fmpz_types.h>

-- fmpz_poly_q_t ---------------------------------------------------------------

data FmpzPolyQ = FmpzPolyQ {-# UNPACK #-} !(ForeignPtr CFmpzPolyQ)
data CFmpzPolyQ = CFmpzPolyQ (Ptr CFmpzPoly) (Ptr CFmpzPoly)

instance Storable CFmpzPolyQ where
  sizeOf _ = #{size fmpz_poly_q_t}
  alignment _ = #{size fmpz_poly_q_t}
  peek ptr = CFmpzPolyQ
    <$> #{peek fmpz_poly_q_struct, num} ptr
    <*> #{peek fmpz_poly_q_struct, den} ptr
  poke = undefined

newFmpzPolyQ = do
  x <- mallocForeignPtr
  withForeignPtr x fmpz_poly_q_init
  addForeignPtrFinalizer p_fmpz_poly_q_clear x
  return $ FmpzPolyQ x

withFmpzPolyQ (FmpzPolyQ x) f = do
  withForeignPtr x $ \xp -> do
    return (FmpzPolyQ x, f xp)

withFmpzPolyQNum :: FmpzPolyQ -> (Ptr CFmpzPolyQ -> t) -> IO (FmpzPolyQ, t)
withFmpzPolyQNum (FmpzPolyQ x) f = do
  withForeignPtr x $ \xp -> do
    return (FmpzPolyQ x, f $ castPtr xp)

withFmpzPolyQDen :: FmpzPolyQ -> (Ptr CFmpzPolyQ -> t) -> IO (FmpzPolyQ, t)
withFmpzPolyQDen (FmpzPolyQ x) f = do
  withForeignPtr x $ \xp -> do
    return (FmpzPolyQ x, f $ flip advancePtr 1 $ castPtr xp)

-- Memory management -----------------------------------------------------------

-- We represent a rational function over \(\mathbf{Q}\) as the quotient of
-- two coprime integer polynomials of type @fmpz_poly_t@, enforcing that
-- the leading coefficient of the denominator is positive. The zero
-- function is represented as \(0/1\).
--
-- | /fmpz_poly_q_init/ /rop/ 
--
-- Initialises @rop@.
foreign import ccall "fmpz_poly_q.h fmpz_poly_q_init"
  fmpz_poly_q_init :: Ptr CFmpzPolyQ -> IO ()

-- | /fmpz_poly_q_clear/ /rop/ 
--
-- Clears the object @rop@.
foreign import ccall "fmpz_poly_q.h fmpz_poly_q_clear"
  fmpz_poly_q_clear :: Ptr CFmpzPolyQ -> IO ()

foreign import ccall "fmpz_poly_q.h &fmpz_poly_q_clear"
  p_fmpz_poly_q_clear :: FunPtr (Ptr CFmpzPolyQ -> IO ())

-- -- | /fmpz_poly_q_numref/ /op/ 
-- --
-- -- Returns a reference to the numerator of @op@.
-- foreign import ccall "fmpz_poly_q.h fmpz_poly_q_numref"
--   fmpz_poly_q_numref :: Ptr CFmpzPolyQ -> IO (Ptr CFmpzPoly)

-- -- | /fmpz_poly_q_denref/ /op/ 
-- --
-- -- Returns a reference to the denominator of @op@.
-- foreign import ccall "fmpz_poly_q.h fmpz_poly_q_denref"
--   fmpz_poly_q_denref :: Ptr CFmpzPolyQ -> IO (Ptr CFmpzPoly)

-- | /fmpz_poly_q_canonicalise/ /rop/ 
--
-- Brings @rop@ into canonical form, only assuming that the denominator is
-- non-zero.
foreign import ccall "fmpz_poly_q.h fmpz_poly_q_canonicalise"
  fmpz_poly_q_canonicalise :: Ptr CFmpzPolyQ -> IO ()

-- | /fmpz_poly_q_is_canonical/ /op/ 
--
-- Checks whether the rational function @op@ is in canonical form.
foreign import ccall "fmpz_poly_q.h fmpz_poly_q_is_canonical"
  fmpz_poly_q_is_canonical :: Ptr CFmpzPolyQ -> IO CInt

-- Randomisation ---------------------------------------------------------------

-- | /fmpz_poly_q_randtest/ /poly/ /state/ /len1/ /bits1/ /len2/ /bits2/ 
--
-- Sets @poly@ to a random rational function.
foreign import ccall "fmpz_poly_q.h fmpz_poly_q_randtest"
  fmpz_poly_q_randtest :: Ptr CFmpzPolyQ -> Ptr CFRandState -> CLong -> CFBitCnt -> CLong -> CFBitCnt -> IO ()

-- | /fmpz_poly_q_randtest_not_zero/ /poly/ /state/ /len1/ /bits1/ /len2/ /bits2/ 
--
-- Sets @poly@ to a random non-zero rational function.
foreign import ccall "fmpz_poly_q.h fmpz_poly_q_randtest_not_zero"
  fmpz_poly_q_randtest_not_zero :: Ptr CFmpzPolyQ -> Ptr CFRandState -> CLong -> CFBitCnt -> CLong -> CFBitCnt -> IO ()

-- Assignment ------------------------------------------------------------------

-- | /fmpz_poly_q_set/ /rop/ /op/ 
--
-- Sets the element @rop@ to the same value as the element @op@.
foreign import ccall "fmpz_poly_q.h fmpz_poly_q_set"
  fmpz_poly_q_set :: Ptr CFmpzPolyQ -> Ptr CFmpzPolyQ -> IO ()

-- | /fmpz_poly_q_set_si/ /rop/ /op/ 
--
-- Sets the element @rop@ to the value given by the @slong@ @op@.
foreign import ccall "fmpz_poly_q.h fmpz_poly_q_set_si"
  fmpz_poly_q_set_si :: Ptr CFmpzPolyQ -> CLong -> IO ()

-- | /fmpz_poly_q_swap/ /op1/ /op2/ 
--
-- Swaps the elements @op1@ and @op2@.
-- 
-- This is done efficiently by swapping pointers.
foreign import ccall "fmpz_poly_q.h fmpz_poly_q_swap"
  fmpz_poly_q_swap :: Ptr CFmpzPolyQ -> Ptr CFmpzPolyQ -> IO ()

-- | /fmpz_poly_q_zero/ /rop/ 
--
-- Sets @rop@ to zero.
foreign import ccall "fmpz_poly_q.h fmpz_poly_q_zero"
  fmpz_poly_q_zero :: Ptr CFmpzPolyQ -> IO ()

-- | /fmpz_poly_q_one/ /rop/ 
--
-- Sets @rop@ to one.
foreign import ccall "fmpz_poly_q.h fmpz_poly_q_one"
  fmpz_poly_q_one :: Ptr CFmpzPolyQ -> IO ()

-- | /fmpz_poly_q_neg/ /rop/ /op/ 
--
-- Sets the element @rop@ to the additive inverse of @op@.
foreign import ccall "fmpz_poly_q.h fmpz_poly_q_neg"
  fmpz_poly_q_neg :: Ptr CFmpzPolyQ -> Ptr CFmpzPolyQ -> IO ()

-- | /fmpz_poly_q_inv/ /rop/ /op/ 
--
-- Sets the element @rop@ to the multiplicative inverse of @op@.
-- 
-- Assumes that the element @op@ is non-zero.
foreign import ccall "fmpz_poly_q.h fmpz_poly_q_inv"
  fmpz_poly_q_inv :: Ptr CFmpzPolyQ -> Ptr CFmpzPolyQ -> IO ()

-- Comparison ------------------------------------------------------------------

-- | /fmpz_poly_q_is_zero/ /op/ 
--
-- Returns whether the element @op@ is zero.
foreign import ccall "fmpz_poly_q.h fmpz_poly_q_is_zero"
  fmpz_poly_q_is_zero :: Ptr CFmpzPolyQ -> IO CInt

-- | /fmpz_poly_q_is_one/ /op/ 
--
-- Returns whether the element @rop@ is equal to the constant polynomial
-- \(1\).
foreign import ccall "fmpz_poly_q.h fmpz_poly_q_is_one"
  fmpz_poly_q_is_one :: Ptr CFmpzPolyQ -> IO CInt

-- | /fmpz_poly_q_equal/ /op1/ /op2/ 
--
-- Returns whether the two elements @op1@ and @op2@ are equal.
foreign import ccall "fmpz_poly_q.h fmpz_poly_q_equal"
  fmpz_poly_q_equal :: Ptr CFmpzPolyQ -> Ptr CFmpzPolyQ -> IO CInt

-- Addition and subtraction ----------------------------------------------------

-- | /fmpz_poly_q_add/ /rop/ /op1/ /op2/ 
--
-- Sets @rop@ to the sum of @op1@ and @op2@.
foreign import ccall "fmpz_poly_q.h fmpz_poly_q_add"
  fmpz_poly_q_add :: Ptr CFmpzPolyQ -> Ptr CFmpzPolyQ -> Ptr CFmpzPolyQ -> IO ()

-- | /fmpz_poly_q_sub/ /rop/ /op1/ /op2/ 
--
-- Sets @rop@ to the difference of @op1@ and @op2@.
foreign import ccall "fmpz_poly_q.h fmpz_poly_q_sub"
  fmpz_poly_q_sub :: Ptr CFmpzPolyQ -> Ptr CFmpzPolyQ -> Ptr CFmpzPolyQ -> IO ()

-- | /fmpz_poly_q_addmul/ /rop/ /op1/ /op2/ 
--
-- Adds the product of @op1@ and @op2@ to @rop@.
foreign import ccall "fmpz_poly_q.h fmpz_poly_q_addmul"
  fmpz_poly_q_addmul :: Ptr CFmpzPolyQ -> Ptr CFmpzPolyQ -> Ptr CFmpzPolyQ -> IO ()

-- | /fmpz_poly_q_submul/ /rop/ /op1/ /op2/ 
--
-- Subtracts the product of @op1@ and @op2@ from @rop@.
foreign import ccall "fmpz_poly_q.h fmpz_poly_q_submul"
  fmpz_poly_q_submul :: Ptr CFmpzPolyQ -> Ptr CFmpzPolyQ -> Ptr CFmpzPolyQ -> IO ()

-- Scalar multiplication and division ------------------------------------------

-- | /fmpz_poly_q_scalar_mul_si/ /rop/ /op/ /x/ 
--
-- Sets @rop@ to the product of the rational function @op@ and the @slong@
-- integer \(x\).
foreign import ccall "fmpz_poly_q.h fmpz_poly_q_scalar_mul_si"
  fmpz_poly_q_scalar_mul_si :: Ptr CFmpzPolyQ -> Ptr CFmpzPolyQ -> CLong -> IO ()

-- | /fmpz_poly_q_scalar_mul_fmpz/ /rop/ /op/ /x/ 
--
-- Sets @rop@ to the product of the rational function @op@ and the @fmpz_t@
-- integer \(x\).
foreign import ccall "fmpz_poly_q.h fmpz_poly_q_scalar_mul_fmpz"
  fmpz_poly_q_scalar_mul_fmpz :: Ptr CFmpzPolyQ -> Ptr CFmpzPolyQ -> Ptr CFmpz -> IO ()

-- | /fmpz_poly_q_scalar_mul_fmpq/ /rop/ /op/ /x/ 
--
-- Sets @rop@ to the product of the rational function @op@ and the @fmpq_t@
-- rational \(x\).
foreign import ccall "fmpz_poly_q.h fmpz_poly_q_scalar_mul_fmpq"
  fmpz_poly_q_scalar_mul_fmpq :: Ptr CFmpzPolyQ -> Ptr CFmpzPolyQ -> Ptr CFmpq -> IO ()

-- | /fmpz_poly_q_scalar_div_si/ /rop/ /op/ /x/ 
--
-- Sets @rop@ to the quotient of the rational function @op@ and the @slong@
-- integer \(x\).
foreign import ccall "fmpz_poly_q.h fmpz_poly_q_scalar_div_si"
  fmpz_poly_q_scalar_div_si :: Ptr CFmpzPolyQ -> Ptr CFmpzPolyQ -> CLong -> IO ()

-- | /fmpz_poly_q_scalar_div_fmpz/ /rop/ /op/ /x/ 
--
-- Sets @rop@ to the quotient of the rational function @op@ and the
-- @fmpz_t@ integer \(x\).
foreign import ccall "fmpz_poly_q.h fmpz_poly_q_scalar_div_fmpz"
  fmpz_poly_q_scalar_div_fmpz :: Ptr CFmpzPolyQ -> Ptr CFmpzPolyQ -> Ptr CFmpz -> IO ()

-- | /fmpz_poly_q_scalar_div_fmpq/ /rop/ /op/ /x/ 
--
-- Sets @rop@ to the quotient of the rational function @op@ and the
-- @fmpq_t@ rational \(x\).
foreign import ccall "fmpz_poly_q.h fmpz_poly_q_scalar_div_fmpq"
  fmpz_poly_q_scalar_div_fmpq :: Ptr CFmpzPolyQ -> Ptr CFmpzPolyQ -> Ptr CFmpq -> IO ()

-- Multiplication and division -------------------------------------------------

-- | /fmpz_poly_q_mul/ /rop/ /op1/ /op2/ 
--
-- Sets @rop@ to the product of @op1@ and @op2@.
foreign import ccall "fmpz_poly_q.h fmpz_poly_q_mul"
  fmpz_poly_q_mul :: Ptr CFmpzPolyQ -> Ptr CFmpzPolyQ -> Ptr CFmpzPolyQ -> IO ()

-- | /fmpz_poly_q_div/ /rop/ /op1/ /op2/ 
--
-- Sets @rop@ to the quotient of @op1@ and @op2@.
foreign import ccall "fmpz_poly_q.h fmpz_poly_q_div"
  fmpz_poly_q_div :: Ptr CFmpzPolyQ -> Ptr CFmpzPolyQ -> Ptr CFmpzPolyQ -> IO ()

-- Powering --------------------------------------------------------------------

-- | /fmpz_poly_q_pow/ /rop/ /op/ /exp/ 
--
-- Sets @rop@ to the @exp@-th power of @op@.
-- 
-- The corner case of @exp == 0@ is handled by setting @rop@ to the
-- constant function \(1\). Note that this includes the case \(0^0 = 1\).
foreign import ccall "fmpz_poly_q.h fmpz_poly_q_pow"
  fmpz_poly_q_pow :: Ptr CFmpzPolyQ -> Ptr CFmpzPolyQ -> CULong -> IO ()

-- Derivative ------------------------------------------------------------------

-- | /fmpz_poly_q_derivative/ /rop/ /op/ 
--
-- Sets @rop@ to the derivative of @op@.
foreign import ccall "fmpz_poly_q.h fmpz_poly_q_derivative"
  fmpz_poly_q_derivative :: Ptr CFmpzPolyQ -> Ptr CFmpzPolyQ -> IO ()

-- Evaluation ------------------------------------------------------------------

-- | /fmpz_poly_q_evaluate_fmpq/ /rop/ /f/ /a/ 
--
-- Sets @rop@ to \(f\) evaluated at the rational \(a\).
-- 
-- If the denominator evaluates to zero at \(a\), returns non-zero and does
-- not modify any of the variables. Otherwise, returns \(0\) and sets @rop@
-- to the rational \(f(a)\).
foreign import ccall "fmpz_poly_q.h fmpz_poly_q_evaluate_fmpq"
  fmpz_poly_q_evaluate_fmpq :: Ptr CFmpq -> Ptr CFmpzPolyQ -> Ptr CFmpq -> IO CInt

-- Input and output ------------------------------------------------------------

-- The following three methods enable users to construct elements of type
-- @fmpz_poly_q_t@ from strings or to obtain string representations of such
-- elements. The format used is based on the FLINT format for integer
-- polynomials of type @fmpz_poly_t@, which we recall first: A non-zero
-- polynomial \(a_0 + a_1 X + \dotsb + a_n X^n\) of length n + 1 is
-- represented by the string @\"n+1  a_0 a_1 ... a_n\"@, where there are
-- two space characters following the length and single space characters
-- separating the individual coefficients. There is no leading or trailing
-- white-space. The zero polynomial is simply represented by @\"0\"@. We
-- adapt this notation for rational functions as follows. We denote the
-- zero function by @\"0\"@. Given a non-zero function with numerator and
-- denominator string representations @num@ and @den@, respectively, we use
-- the string @num\/den@ to represent the rational function, unless the
-- denominator is equal to one, in which case we simply use @num@. There is
-- also a @_pretty@ variant available, which bases the string parts for the
-- numerator and denominator on the output of the function
-- @fmpz_poly_get_str_pretty@ and introduces parentheses where necessary.
-- Note that currently these functions are not optimised for performance
-- and are intended to be used only for debugging purposes or one-off input
-- and output, rather than as a low-level parser.
--
-- | /fmpz_poly_q_set_str/ /rop/ /s/ 
--
-- Sets @rop@ to the rational function given by the string @s@.
foreign import ccall "fmpz_poly_q.h fmpz_poly_q_set_str"
  fmpz_poly_q_set_str :: Ptr CFmpzPolyQ -> CString -> IO CInt

-- | /fmpz_poly_q_get_str/ /op/ 
--
-- Returns the string representation of the rational function @op@.
foreign import ccall "fmpz_poly_q.h fmpz_poly_q_get_str"
  fmpz_poly_q_get_str :: Ptr CFmpzPolyQ -> IO CString

-- | /fmpz_poly_q_get_str_pretty/ /op/ /x/ 
--
-- Returns the pretty string representation of the rational function @op@.
foreign import ccall "fmpz_poly_q.h fmpz_poly_q_get_str_pretty"
  fmpz_poly_q_get_str_pretty :: Ptr CFmpzPolyQ -> CString -> IO CString

-- | /fmpz_poly_q_print/ /op/ 
--
-- Prints the representation of the rational function @op@ to @stdout@.
fmpz_poly_q_print :: Ptr CFmpzPolyQ -> IO CInt
fmpz_poly_q_print op = printCStr fmpz_poly_q_get_str op

-- | /fmpz_poly_q_print_pretty/ /op/ /x/ 
--
-- Prints the pretty representation of the rational function @op@ to
-- @stdout@.
fmpz_poly_q_print_pretty :: Ptr CFmpzPolyQ -> CString -> IO CInt
fmpz_poly_q_print_pretty op x = 
  printCStr (\op -> fmpz_poly_q_get_str_pretty op x) op

