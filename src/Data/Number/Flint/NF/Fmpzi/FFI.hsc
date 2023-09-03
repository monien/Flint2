{-|
module      :  Data.Number.Flint.NF.Fmpzi.FFI
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de
-}
module Data.Number.Flint.NF.Fmpzi.FFI (
  -- * Gaussian integers
    Fmpzi (..)
  , CFmpzi (..)
  , newFmpzi
  , newFmpzi_
  , withFmpzi
  , withNewFmpzi
  , withFmpziReal
  , withFmpziImag
  -- * Types
  -- * Basic manipulation
  , fmpzi_init
  , fmpzi_clear
  , fmpzi_swap
  , fmpzi_zero
  , fmpzi_one
  , fmpzi_set
  , fmpzi_set_si_si
  -- * Input and output
  , fmpzi_get_str
  , fmpzi_fprint
  , fmpzi_print
  -- * Random number generation
  , fmpzi_randtest
  -- * Properties
  , fmpzi_equal
  , fmpzi_is_zero
  , fmpzi_is_one
  -- * Units
  , fmpzi_is_unit
  , fmpzi_canonical_unit_i_pow
  , fmpzi_canonicalise_unit
  -- * Norms
  , fmpzi_bits
  , fmpzi_norm
  -- * Arithmetic
  , fmpzi_conj
  , fmpzi_neg
  , fmpzi_add
  , fmpzi_sub
  , fmpzi_sqr
  , fmpzi_mul
  , fmpzi_pow_ui
  -- * Division
  , fmpzi_divexact
  , fmpzi_divrem
  , fmpzi_divrem_approx
  , fmpzi_remove_one_plus_i
  -- * GCD
  , fmpzi_gcd_euclidean
) where 

-- Gaussian integers -----------------------------------------------------------

import Control.Monad

import Foreign.C.String
import Foreign.C.Types
import qualified Foreign.Concurrent
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr, castPtr )
import Foreign.Storable
import Foreign.Marshal ( free )
import Foreign.Marshal.Array ( advancePtr )

#include <flint/fmpzi.h>

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz

-- Types -----------------------------------------------------------------------

data Fmpzi = Fmpzi {-# UNPACK #-} !(ForeignPtr CFmpzi)
data CFmpzi = CFmpzi CFmpz CFmpz

instance Storable CFmpzi where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fmpzi_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fmpzi_t}
  peek = undefined
  poke = undefined

-- | Create `Fmpzi`.
newFmpzi = do
  x <- mallocForeignPtr
  withForeignPtr x fmpzi_init
  addForeignPtrFinalizer p_fmpzi_clear x
  return $ Fmpzi x

-- | Create `Fmpzi`.
newFmpzi_ a b = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> do
    fmpzi_init x
    fmpzi_set_si_si x a b
  addForeignPtrFinalizer p_fmpzi_clear x
  return $ Fmpzi x

-- | Use `Fmpzi`
{-# INLINE withFmpzi #-}
withFmpzi (Fmpzi x) f = do
  withForeignPtr x $ \p -> f p >>= return . (Fmpzi x,)

-- | Use real part of `Fmpzi`
{-# INLINE withFmpziReal #-}
withFmpziReal (Fmpzi x) f = do
  withForeignPtr x $ \p -> (Fmpzi x,) <$> f (castPtr p)

-- | Use imaginary part of `Fmpzi`
{-# INLINE withFmpziImag #-}
withFmpziImag (Fmpzi x) f = do
  withForeignPtr x $ \p -> (Fmpzi x,) <$> f (castPtr p `advancePtr` 1)

-- | Use new `Fmpzi`
{-# INLINE withNewFmpzi #-}
withNewFmpzi f = do
  x <- newFmpzi
  withFmpzi x f 

-- Memory management -----------------------------------------------------------

foreign import ccall "fmpzi.h fmpzi_init"
  fmpzi_init :: Ptr CFmpzi -> IO ()

foreign import ccall "fmpzi.h fmpzi_clear"
  fmpzi_clear :: Ptr CFmpzi -> IO ()

foreign import ccall "fmpzi.h &fmpzi_clear"
  p_fmpzi_clear :: FunPtr (Ptr CFmpzi -> IO ())

-- Basic manipulation ----------------------------------------------------------

foreign import ccall "fmpzi.h fmpzi_swap"
  fmpzi_swap :: Ptr CFmpzi -> Ptr CFmpzi -> IO ()

foreign import ccall "fmpzi.h fmpzi_zero"
  fmpzi_zero :: Ptr CFmpzi -> IO ()

foreign import ccall "fmpzi.h fmpzi_one"
  fmpzi_one :: Ptr CFmpzi -> IO ()

foreign import ccall "fmpzi.h fmpzi_set"
  fmpzi_set :: Ptr CFmpzi -> Ptr CFmpzi -> IO ()

foreign import ccall "fmpzi.h fmpzi_set_si_si"
  fmpzi_set_si_si :: Ptr CFmpzi -> CLong -> CLong -> IO ()

-- Input and output ------------------------------------------------------------

foreign import ccall "fmpzi.h fmpzi_get_str"
  fmpzi_get_str :: Ptr CFmpzi -> IO CString

foreign import ccall "fmpzi.h fmpzi_fprint"
  fmpzi_fprint :: Ptr CFile -> Ptr CFmpzi -> IO ()
  
fmpzi_print :: Ptr CFmpzi -> IO ()
fmpzi_print z = do
  printCStr fmpzi_get_str z
  return ()

-- Random number generation ----------------------------------------------------

foreign import ccall "fmpzi.h fmpzi_randtest"
  fmpzi_randtest :: Ptr CFmpzi -> Ptr CFRandState -> CMpBitCnt -> IO ()

-- Properties ------------------------------------------------------------------

foreign import ccall "fmpzi.h fmpzi_equal"
  fmpzi_equal :: Ptr CFmpzi -> Ptr CFmpzi -> IO CInt

foreign import ccall "fmpzi.h fmpzi_is_zero"
  fmpzi_is_zero :: Ptr CFmpzi -> IO CInt

foreign import ccall "fmpzi.h fmpzi_is_one"
  fmpzi_is_one :: Ptr CFmpzi -> IO CInt

-- Units -----------------------------------------------------------------------

foreign import ccall "fmpzi.h fmpzi_is_unit"
  fmpzi_is_unit :: Ptr CFmpzi -> IO CInt

foreign import ccall "fmpzi.h fmpzi_canonical_unit_i_pow"
  fmpzi_canonical_unit_i_pow :: Ptr CFmpzi -> IO CLong

foreign import ccall "fmpzi.h fmpzi_canonicalise_unit"
  fmpzi_canonicalise_unit :: Ptr CFmpzi -> Ptr CFmpzi -> IO ()

-- Norms -----------------------------------------------------------------------

foreign import ccall "fmpzi.h fmpzi_bits"
  fmpzi_bits :: Ptr CFmpzi -> IO CLong

foreign import ccall "fmpzi.h fmpzi_norm"
  fmpzi_norm :: Ptr CFmpz -> Ptr CFmpzi -> IO ()

-- Arithmetic ------------------------------------------------------------------

foreign import ccall "fmpzi.h fmpzi_conj"
  fmpzi_conj :: Ptr CFmpzi -> Ptr CFmpzi -> IO ()

foreign import ccall "fmpzi.h fmpzi_neg"
  fmpzi_neg :: Ptr CFmpzi -> Ptr CFmpzi -> IO ()

foreign import ccall "fmpzi.h fmpzi_add"
  fmpzi_add :: Ptr CFmpzi -> Ptr CFmpzi -> Ptr CFmpzi -> IO ()

foreign import ccall "fmpzi.h fmpzi_sub"
  fmpzi_sub :: Ptr CFmpzi -> Ptr CFmpzi -> Ptr CFmpzi -> IO ()

foreign import ccall "fmpzi.h fmpzi_sqr"
  fmpzi_sqr :: Ptr CFmpzi -> Ptr CFmpzi -> IO ()

foreign import ccall "fmpzi.h fmpzi_mul"
  fmpzi_mul :: Ptr CFmpzi -> Ptr CFmpzi -> Ptr CFmpzi -> IO ()

foreign import ccall "fmpzi.h fmpzi_pow_ui"
  fmpzi_pow_ui :: Ptr CFmpzi -> Ptr CFmpzi -> CULong -> IO ()

-- Division --------------------------------------------------------------------

-- | /fmpzi_divexact/ /q/ /x/ /y/ 
-- 
-- Sets /q/ to the quotient of /x/ and /y/, assuming that the division is
-- exact.
foreign import ccall "fmpzi.h fmpzi_divexact"
  fmpzi_divexact :: Ptr CFmpzi -> Ptr CFmpzi -> Ptr CFmpzi -> IO ()

-- | /fmpzi_divrem/ /q/ /r/ /x/ /y/ 
-- 
-- Computes a quotient and remainder satisfying \(x = q y + r\) with
-- \(N(r) \le N(y)/2\), with a canonical choice of remainder when breaking
-- ties.
foreign import ccall "fmpzi.h fmpzi_divrem"
  fmpzi_divrem :: Ptr CFmpzi -> Ptr CFmpzi -> Ptr CFmpzi -> Ptr CFmpzi -> IO ()

-- | /fmpzi_divrem_approx/ /q/ /r/ /x/ /y/ 
-- 
-- Computes a quotient and remainder satisfying \(x = q y + r\) with
-- \(N(r) < N(y)\), with an implementation-defined, non-canonical choice of
-- remainder.
foreign import ccall "fmpzi.h fmpzi_divrem_approx"
  fmpzi_divrem_approx :: Ptr CFmpzi -> Ptr CFmpzi -> Ptr CFmpzi -> Ptr CFmpzi -> IO ()

-- | /fmpzi_remove_one_plus_i/ /res/ /x/ 
-- 
-- Divide /x/ exactly by the largest possible power \((1+i)^k\) and return
-- the exponent /k/.
foreign import ccall "fmpzi.h fmpzi_remove_one_plus_i"
  fmpzi_remove_one_plus_i :: Ptr CFmpzi -> Ptr CFmpzi -> IO CLong

-- GCD -------------------------------------------------------------------------

-- | /fmpzi_gcd_euclidean/ /res/ /x/ /y/ 
-- 
-- Computes the GCD of /x/ and /y/. The result is in canonical unit form.
-- 
-- The /euclidean/ version is a straightforward implementation of Euclid\'s
-- algorithm. The /euclidean_improved/ version is optimized by performing
-- approximate divisions. The /binary/ version uses a (1+i)-ary analog of
-- the binary GCD algorithm for integers < [Wei2000]>. The /shortest/
-- version finds the GCD as the shortest vector in a lattice. The default
-- version chooses an algorithm automatically.
foreign import ccall "fmpzi.h fmpzi_gcd_euclidean"
  fmpzi_gcd_euclidean :: Ptr CFmpzi -> Ptr CFmpzi -> Ptr CFmpzi -> IO ()

