{-# language
    CApiFFI
  , FlexibleInstances
  , ForeignFunctionInterface
  , MultiParamTypeClasses
  , TupleSections
  , TypeFamilies
  #-}
{- |
module      : Data.Number.Flint.Fmpz.MPoly.Q.FFI
copyright   : (c) 2023 Hartmut Monien
license     : BSD-style (see LICENSE)
maintainer  : hmonien@uni-bonn.de

An @FmpzMPolyQ@ represents an element of :math:`\mathbb{Q}(x_1,ldots,x_n)`
for fixed /n/ as a pair of Flint multivariate polynomials
(@FmpzMPolyQ@). Instances are always kept in canonical form by
ensuring that the GCD of numerator and denominator is 1 and that the
coefficient of the leading term of the denominator is positive.

The user must create a multivariate polynomial context
(@FmpzMPolyCtx@) specifying the number of variables /n/ and the
monomial ordering.

-}
module Data.Number.Flint.Fmpz.MPoly.Q.FFI (
  -- * Multivariate rational functions over Q
  -- * Types
    FmpzMPolyQ (..)
  , CFmpzMPolyQ (..)
  , newFmpzMPolyQ
  , withFmpzMPolyQ
  , withFmpzMPolyQNumerator
  , withFmpzMPolyQDenominator
  -- * Memory management
  , fmpz_mpoly_q_init
  , fmpz_mpoly_q_clear
  -- * Assignment
  , fmpz_mpoly_q_swap
  , fmpz_mpoly_q_set
  -- * Canonicalisation
  , fmpz_mpoly_q_canonicalise
  , fmpz_mpoly_q_is_canonical
  -- * Properties
  , fmpz_mpoly_q_is_zero
  , fmpz_mpoly_q_is_one
  , fmpz_mpoly_q_used_vars
  -- * Special values
  , fmpz_mpoly_q_zero
  , fmpz_mpoly_q_one
  , fmpz_mpoly_q_gen
  -- * Input and output
  , fmpz_mpoly_q_get_str_pretty
  , fmpz_mpoly_q_fprint_pretty
  , fmpz_mpoly_q_print_pretty
  -- * Random generation
  , fmpz_mpoly_q_randtest
  -- * Comparisons
  , fmpz_mpoly_q_equal
  -- * Arithmetic
  , fmpz_mpoly_q_neg
  , fmpz_mpoly_q_add
  , fmpz_mpoly_q_sub
  , fmpz_mpoly_q_mul
  , fmpz_mpoly_q_div
  , fmpz_mpoly_q_inv
  -- * Content
  , _fmpz_mpoly_q_content
) where 

-- Multivariate rational functions over Q --------------------------------------

import System.IO.Unsafe

import Control.Monad

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr, nullPtr, castPtr )
import Foreign.Storable
import Foreign.Marshal ( free )
import Foreign.Marshal.Array (advancePtr)

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Poly
import Data.Number.Flint.Fmpz.MPoly

#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpz_poly.h>
#include <flint/fmpz_mpoly_q.h>

-- Types -----------------------------------------------------------------------

data FmpzMPolyQ = FmpzMPolyQ {-# UNPACK #-} !(ForeignPtr CFmpzMPolyQ)
data CFmpzMPolyQ = CFmpzMPolyQ CFmpzMPoly CFmpzMPoly

instance Storable CFmpzMPolyQ where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fmpz_mpoly_q_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fmpz_mpoly_q_t}
  peek ptr = CFmpzMPolyQ
    <$> #{peek fmpz_mpoly_q_struct, num} ptr
    <*> #{peek fmpz_mpoly_q_struct, den} ptr
  poke ptr (CFmpzMPolyQ num den) = do
    #{poke fmpz_mpoly_q_struct, num} ptr num
    #{poke fmpz_mpoly_q_struct, den} ptr den

-- | Create a new `FmpzMPolyQ`
newFmpzMPolyQ ctx@(FmpzMPolyCtx pctx) = do
  p <- mallocForeignPtr
  withForeignPtr p $ \p ->
    withFmpzMPolyCtx ctx $ \ctx -> do 
      fmpz_mpoly_q_init p ctx
      addForeignPtrFinalizerEnv p_fmpz_mpoly_q_clear p pctx 
  return $ FmpzMPolyQ p

-- | Use a new `FmpzMPolyQ`
{-# INLINE withFmpzMPolyQ #-}
withFmpzMPolyQ (FmpzMPolyQ p) f = do
  withForeignPtr p $ \fp -> (FmpzMPolyQ p,) <$> f fp

-- | Use the numerator of `FmpzMPolyQ`
withFmpzMPolyQNumerator ::
  FmpzMPolyQ -> (Ptr CFmpzMPoly -> IO t) -> IO (FmpzMPolyQ, t)
withFmpzMPolyQNumerator (FmpzMPolyQ p) f = do
  withForeignPtr p $ \fp -> (FmpzMPolyQ p,) <$> f (castPtr fp)

-- | Use the denominator of `FmpzMPolyQ`
withFmpzMPolyQDenominator ::
  FmpzMPolyQ -> (Ptr CFmpzMPoly -> IO t) -> IO (FmpzMPolyQ, t)
withFmpzMPolyQDenominator (FmpzMPolyQ p) f = do
  withForeignPtr p $ \fp -> (FmpzMPolyQ p,) <$> f (castPtr fp `advancePtr` 1)

-- Memory management -----------------------------------------------------------

-- | /fmpz_mpoly_q_init/ /res/ /ctx/ 
-- 
-- Initializes /res/ for use, and sets its value to zero.
foreign import ccall "fmpz_mpoly_q.h fmpz_mpoly_q_init"
  fmpz_mpoly_q_init :: Ptr CFmpzMPolyQ -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_q_clear/ /res/ /ctx/ 
-- 
-- Clears /res/, freeing or recycling its allocated memory.
foreign import ccall "fmpz_mpoly_q.h fmpz_mpoly_q_clear"
  fmpz_mpoly_q_clear :: Ptr CFmpzMPolyQ -> Ptr CFmpzMPolyCtx -> IO ()

foreign import ccall "fmpz_mpoly_q.h &fmpz_mpoly_q_clear"
  p_fmpz_mpoly_q_clear :: FunPtr (Ptr CFmpzMPolyQ -> Ptr CFmpzMPolyCtx -> IO ())

-- Assignment ------------------------------------------------------------------

-- | /fmpz_mpoly_q_swap/ /x/ /y/ /ctx/ 
-- 
-- Swaps the values of /x/ and /y/ efficiently.
foreign import ccall "fmpz_mpoly_q.h fmpz_mpoly_q_swap"
  fmpz_mpoly_q_swap :: Ptr CFmpzMPolyQ -> Ptr CFmpzMPolyQ -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_q_set/ /res/ /x/ /ctx/ 
-- 
-- Sets /res/ to the value /x/.
foreign import ccall "fmpz_mpoly_q.h fmpz_mpoly_q_set"
  fmpz_mpoly_q_set :: Ptr CFmpzMPolyQ -> Ptr CFmpzMPolyQ -> Ptr CFmpzMPolyCtx -> IO ()

-- Canonicalisation ------------------------------------------------------------

-- | /fmpz_mpoly_q_canonicalise/ /x/ /ctx/ 
-- 
-- Puts the numerator and denominator of /x/ in canonical form by removing
-- common content and making the leading term of the denominator positive.
foreign import ccall "fmpz_mpoly_q.h fmpz_mpoly_q_canonicalise"
  fmpz_mpoly_q_canonicalise :: Ptr CFmpzMPolyQ -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_q_is_canonical/ /x/ /ctx/ 
-- 
-- Returns whether /x/ is in canonical form.
-- 
-- In addition to verifying that the numerator and denominator have no
-- common content and that the leading term of the denominator is positive,
-- this function checks that the denominator is nonzero and that the
-- numerator and denominator have correctly sorted terms (these properties
-- should normally hold; verifying them provides an extra consistency check
-- for test code).
foreign import ccall "fmpz_mpoly_q.h fmpz_mpoly_q_is_canonical"
  fmpz_mpoly_q_is_canonical :: Ptr CFmpzMPolyQ -> Ptr CFmpzMPolyCtx -> IO CInt

-- Properties ------------------------------------------------------------------

-- | /fmpz_mpoly_q_is_zero/ /x/ /ctx/ 
-- 
-- Returns whether /x/ is the constant 0.
foreign import ccall "fmpz_mpoly_q.h fmpz_mpoly_q_is_zero"
  fmpz_mpoly_q_is_zero :: Ptr CFmpzMPolyQ -> Ptr CFmpzMPolyCtx -> IO CInt

-- | /fmpz_mpoly_q_is_one/ /x/ /ctx/ 
-- 
-- Returns whether /x/ is the constant 1.
foreign import ccall "fmpz_mpoly_q.h fmpz_mpoly_q_is_one"
  fmpz_mpoly_q_is_one :: Ptr CFmpzMPolyQ -> Ptr CFmpzMPolyCtx -> IO CInt

-- | /fmpz_mpoly_q_used_vars/ /used/ /f/ /ctx/ 
-- 
-- For each variable, sets the corresponding entry in /used/ to the boolean
-- flag indicating whether that variable appears in the rational function
-- (respectively its numerator or denominator).
foreign import ccall "fmpz_mpoly_q.h fmpz_mpoly_q_used_vars"
  fmpz_mpoly_q_used_vars :: Ptr CInt -> Ptr CFmpzMPolyQ -> Ptr CFmpzMPolyCtx -> IO ()

-- Special values --------------------------------------------------------------

-- | /fmpz_mpoly_q_zero/ /res/ /ctx/ 
-- 
-- Sets /res/ to the constant 0.
foreign import ccall "fmpz_mpoly_q.h fmpz_mpoly_q_zero"
  fmpz_mpoly_q_zero :: Ptr CFmpzMPolyQ -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_q_one/ /res/ /ctx/ 
-- 
-- Sets /res/ to the constant 1.
foreign import ccall "fmpz_mpoly_q.h fmpz_mpoly_q_one"
  fmpz_mpoly_q_one :: Ptr CFmpzMPolyQ -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_q_gen/ /res/ /i/ /ctx/ 
-- 
-- Sets /res/ to the generator \(x_{i+1}\). Requires \(0 \le i < n\) where
-- /n/ is the number of variables of /ctx/.
foreign import ccall "fmpz_mpoly_q.h fmpz_mpoly_q_gen"
  fmpz_mpoly_q_gen :: Ptr CFmpzMPolyQ -> CLong -> Ptr CFmpzMPolyCtx -> IO ()

-- Input and output ------------------------------------------------------------

-- | /fmpz_mpoly_q_get_str_pretty/ /f/ /x/ /ctx/ 
-- 
-- Returns string representation of /f/. If /x/ is not /NULL/, the strings in
-- /x/ are used as the symbols for the variables.
foreign import ccall "fmpz_mpoly_q.h fmpz_mpoly_q_get_str_pretty"
  fmpz_mpoly_q_get_str_pretty :: Ptr CFmpzMPolyQ -> Ptr (Ptr CChar) -> Ptr CFmpzMPolyCtx -> IO CString
  
-- | /fmpz_mpoly_q_print_pretty/ /f/ /x/ /ctx/ 
-- 
-- Prints /f/ to standard output. If /x/ is not /NULL/, the strings in
-- /x/ are used as the symbols for the variables.
fmpz_mpoly_q_print_pretty :: Ptr CFmpzMPolyQ -> Ptr (Ptr CChar) -> Ptr CFmpzMPolyCtx -> IO CInt
fmpz_mpoly_q_print_pretty x vars ctx = do
  printCStr (\x -> fmpz_mpoly_q_get_str_pretty x vars ctx) x

-- | /fmpz_mpoly_q_fprint_pretty/ /out/ /f/ /x/ /ctx/ 
-- 
-- Prints /f/ to file /out/. If /x/ is not /NULL/, the strings in
-- /x/ are used as the symbols for the variables.
foreign import ccall "fmpz_mpoly_q.h fmpz_mpoly_q_fprint_pretty"
  fmpz_mpoly_q_fprint_pretty :: Ptr CFile -> Ptr CFmpzMPolyQ -> Ptr (Ptr CChar) -> Ptr CFmpzMPolyCtx -> IO CInt

-- Random generation -----------------------------------------------------------

-- | /fmpz_mpoly_q_randtest/ /res/ /state/ /length/ /coeff_bits/ /exp_bound/ /ctx/ 
-- 
-- Sets /res/ to a random rational function where both numerator and
-- denominator have up to /length/ terms, coefficients up to size
-- /coeff_bits/, and exponents strictly smaller than /exp_bound/.
foreign import ccall "fmpz_mpoly_q.h fmpz_mpoly_q_randtest"
  fmpz_mpoly_q_randtest :: Ptr CFmpzMPolyQ -> Ptr CFRandState -> CLong -> CMpLimb -> CLong -> Ptr CFmpzMPolyCtx -> IO ()

-- Comparisons -----------------------------------------------------------------

-- | /fmpz_mpoly_q_equal/ /x/ /y/ /ctx/ 
-- 
-- Returns whether /x/ and /y/ are equal.
foreign import ccall "fmpz_mpoly_q.h fmpz_mpoly_q_equal"
  fmpz_mpoly_q_equal :: Ptr CFmpzMPolyQ -> Ptr CFmpzMPolyQ -> Ptr CFmpzMPolyCtx -> IO CInt

-- Arithmetic ------------------------------------------------------------------

-- | /fmpz_mpoly_q_neg/ /res/ /x/ /ctx/ 
-- 
-- Sets /res/ to the negation of /x/.
foreign import ccall "fmpz_mpoly_q.h fmpz_mpoly_q_neg"
  fmpz_mpoly_q_neg :: Ptr CFmpzMPolyQ -> Ptr CFmpzMPolyQ -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_q_add/ /res/ /x/ /y/ /ctx/ 
-- 
-- Sets /res/ to the sum of /x/ and /y/.
foreign import ccall "fmpz_mpoly_q.h fmpz_mpoly_q_add"
  fmpz_mpoly_q_add :: Ptr CFmpzMPolyQ -> Ptr CFmpzMPolyQ -> Ptr CFmpzMPolyQ -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_q_sub/ /res/ /x/ /y/ /ctx/ 
-- 
-- Sets /res/ to the difference of /x/ and /y/.
foreign import ccall "fmpz_mpoly_q.h fmpz_mpoly_q_sub"
  fmpz_mpoly_q_sub :: Ptr CFmpzMPolyQ -> Ptr CFmpzMPolyQ -> Ptr CFmpzMPolyQ -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_q_mul/ /res/ /x/ /y/ /ctx/ 
-- 
-- Sets /res/ to the product of /x/ and /y/.
foreign import ccall "fmpz_mpoly_q.h fmpz_mpoly_q_mul"
  fmpz_mpoly_q_mul :: Ptr CFmpzMPolyQ -> Ptr CFmpzMPolyQ -> Ptr CFmpzMPolyQ -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_q_div/ /res/ /x/ /y/ /ctx/ 
-- 
-- Sets /res/ to the quotient of /x/ and /y/. Division by zero calls
-- /flint_abort/.
foreign import ccall "fmpz_mpoly_q.h fmpz_mpoly_q_div"
  fmpz_mpoly_q_div :: Ptr CFmpzMPolyQ -> Ptr CFmpzMPolyQ -> Ptr CFmpzMPolyQ -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_q_inv/ /res/ /x/ /ctx/ 
-- 
-- Sets /res/ to the inverse of /x/. Division by zero calls /flint_abort/.
foreign import ccall "fmpz_mpoly_q.h fmpz_mpoly_q_inv"
  fmpz_mpoly_q_inv :: Ptr CFmpzMPolyQ -> Ptr CFmpzMPolyQ -> Ptr CFmpzMPolyCtx -> IO ()

-- Content ---------------------------------------------------------------------

-- | /_fmpz_mpoly_q_content/ /num/ /den/ /xnum/ /xden/ /ctx/ 
-- 
-- Sets /res/ to the content of the coefficients of /x/.
foreign import ccall "fmpz_mpoly_q.h _fmpz_mpoly_q_content"
  _fmpz_mpoly_q_content :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO ()




