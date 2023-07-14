{-|
module      :  Data.Number.Flint.Acb.Acf.FFI
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de
-}
module Data.Number.Flint.Acb.Acf.FFI (
  -- * Complex floating-point numbers
    Acf (..)
  , CAcf (..)
  , newAcf
  , withAcf
  , withNewAcf
  -- * Memory management
  , acf_init
  , acf_clear
  , acf_swap
  , acf_allocated_bytes
  -- * Basic manipulation
  , acf_real_ptr
  , acf_imag_ptr
  , acf_set
  , acf_equal
  -- * Arithmetic
  , acf_add
  , acf_sub
  , acf_mul
  -- * Approximate arithmetic
  , acf_approx_inv
  , acf_approx_div
  , acf_approx_sqrt
  , acf_approx_dot
) where

-- Complex floating-point numbers ----------------------------------------------

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.Storable
import Foreign.Marshal.Alloc
import Foreign.C.Types
import Foreign.C.String

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpq

import Data.Number.Flint.Arb.Types
import Data.Number.Flint.Acb.Types

#define ACF_INLINES_C
#include <flint/acf.h>

-- acf_t -----------------------------------------------------------------------

-- | Createst a new `CAcf` structure encapsulated in `Acf`.
newAcf = do
  p <- mallocForeignPtr
  withForeignPtr p acf_init
  addForeignPtrFinalizer p_acf_clear p
  return $ Acf p
  
-- | Access to the C pointer in `Acf` structure.
{-# INLINE withAcf #-}
withAcf (Acf p) f = withForeignPtr p $ fmap (Acf p,) . f

withNewAcf f = do
  x <- newAcf
  withAcf x $ \x -> f x
  
instance Storable CAcf where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size acf_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment acf_t}
  peek = error "CAcf.peek: Not defined"
  poke = error "CAcf.poke: Not defined"

-- Memory management -----------------------------------------------------------

-- | /acf_init/ /x/ 
--
-- Initializes the variable /x/ for use, and sets its value to zero.
foreign import ccall "acf.h acf_init"
  acf_init :: Ptr CAcf -> IO ()

-- | /acf_clear/ /x/ 
--
-- Clears the variable /x/, freeing or recycling its allocated memory.
foreign import ccall "acf.h acf_clear"
  acf_clear :: Ptr CAcf -> IO ()

foreign import ccall "acf.h &acf_clear"
  p_acf_clear :: FunPtr (Ptr CAcf -> IO ())

-- | /acf_swap/ /z/ /x/ 
--
-- Swaps /z/ and /x/ efficiently.
foreign import ccall "acf.h acf_swap"
  acf_swap :: Ptr CAcf -> Ptr CAcf -> IO ()

-- | /acf_allocated_bytes/ /x/ 
--
-- Returns the total number of bytes heap-allocated internally by this
-- object. The count excludes the size of the structure itself. Add
-- @sizeof(acf_struct)@ to get the size of the object as a whole.
foreign import ccall "acf.h acf_allocated_bytes"
  acf_allocated_bytes :: Ptr CAcf -> IO CLong

-- Basic manipulation ----------------------------------------------------------

-- | /acf_real_ptr/ /z/ 
foreign import ccall "acf.h acf_real_ptr"
  acf_real_ptr :: Ptr CAcf -> IO (Ptr CArf)
  
-- | /acf_imag_ptr/ /z/ 
--
-- Returns a pointer to the real or imaginary part of /z/.
foreign import ccall "acf.h acf_imag_ptr"
  acf_imag_ptr :: Ptr CAcf -> IO (Ptr CArf)

-- | /acf_set/ /z/ /x/ 
--
-- Sets /z/ to the value /x/.
foreign import ccall "acf.h acf_set"
  acf_set :: Ptr CAcf -> Ptr CAcf -> IO ()

-- | /acf_equal/ /x/ /y/ 
--
-- Returns whether /x/ and /y/ are equal.
foreign import ccall "acf.h acf_equal"
  acf_equal :: Ptr CAcf -> Ptr CAcf -> IO CInt

-- Arithmetic ------------------------------------------------------------------

-- | /acf_add/ /res/ /x/ /y/ /prec/ /rnd/ 
--
foreign import ccall "acf.h acf_add"
  acf_add :: Ptr CAcf -> Ptr CAcf -> Ptr CAcf -> CLong -> ArfRnd -> IO CInt

-- | /acf_sub/ /res/ /x/ /y/ /prec/ /rnd/ 
--
foreign import ccall "acf.h acf_sub"
  acf_sub :: Ptr CAcf -> Ptr CAcf -> Ptr CAcf -> CLong -> ArfRnd -> IO CInt

-- | /acf_mul/ /res/ /x/ /y/ /prec/ /rnd/ 
--
-- Sets /res/ to the sum, difference or product of /x/ or /y/, correctly
-- rounding the real and imaginary parts in direction /rnd/. The return
-- flag has the least significant bit set if the real part is inexact, and
-- the second least significant bit set if the imaginary part is inexact.
foreign import ccall "acf.h acf_mul"
  acf_mul :: Ptr CAcf -> Ptr CAcf -> Ptr CAcf -> CLong -> ArfRnd -> IO CInt

-- Approximate arithmetic ------------------------------------------------------

-- The following operations are /not/ correctly rounded. The @rnd@
-- parameter specifies the final direction of rounding, but intermediate
-- roundings are implementation-defined.
--
-- | /acf_approx_inv/ /res/ /x/ /prec/ /rnd/ 
foreign import ccall "acf.h acf_approx_inv"
  acf_approx_inv :: Ptr CAcf -> Ptr CAcf -> CLong -> ArfRnd -> IO ()
-- | /acf_approx_div/ /res/ /x/ /y/ /prec/ /rnd/ 
foreign import ccall "acf.h acf_approx_div"
  acf_approx_div :: Ptr CAcf -> Ptr CAcf -> Ptr CAcf -> CLong -> ArfRnd -> IO ()
-- | /acf_approx_sqrt/ /res/ /x/ /prec/ /rnd/ 
--
-- Computes an approximate inverse, quotient or square root.
foreign import ccall "acf.h acf_approx_sqrt"
  acf_approx_sqrt :: Ptr CAcf -> Ptr CAcf -> CLong -> ArfRnd -> IO ()

-- | /acf_approx_dot/ /res/ /initial/ /subtract/ /x/ /xstep/ /y/ /ystep/ /len/ /prec/ /rnd/ 
--
-- Computes an approximate dot product, with the same meaning of the
-- parameters as @arb_dot@.
foreign import ccall "acf.h acf_approx_dot"
  acf_approx_dot :: Ptr CAcf -> Ptr CAcf -> CInt -> Ptr CAcf -> CLong -> Ptr CAcf -> CLong -> CLong -> CLong -> ArfRnd -> IO ()

