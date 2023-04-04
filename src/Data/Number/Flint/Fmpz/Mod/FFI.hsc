{-# language
    CApiFFI
  , FlexibleInstances
  , ForeignFunctionInterface
  , MultiParamTypeClasses
  , TupleSections
  , TypeFamilies
  #-}
  
module Data.Number.Flint.Fmpz.Mod.FFI (
  -- * Arithmetic modulo integers
  -- * Context object
    FmpzModCtx (..)
  , CFmpzModCtx (..)
  , newFmpzModCtx
  , withFmpzModCtx
  , withNewFmpzModCtx
  , fmpz_mod_ctx_init
  , fmpz_mod_ctx_clear
  , fmpz_mod_ctx_set_modulus
  -- * Conversions
  , fmpz_mod_set_fmpz
  -- * Arithmetic
  , fmpz_mod_is_canonical
  , fmpz_mod_is_one
  , fmpz_mod_add
  , fmpz_mod_add_fmpz
  , fmpz_mod_sub
  , fmpz_mod_sub_fmpz
  , fmpz_mod_fmpz_sub
  , fmpz_mod_neg
  , fmpz_mod_mul
  , fmpz_mod_inv
  , fmpz_mod_divides
  , fmpz_mod_pow_ui
  , fmpz_mod_pow_fmpz
  -- * Discrete Logarithms via Pohlig-Hellman
  , fmpz_mod_discrete_log_pohlig_hellman_init
  , fmpz_mod_discrete_log_pohlig_hellman_clear
  , fmpz_mod_discrete_log_pohlig_hellman_precompute_prime
  , fmpz_mod_discrete_log_pohlig_hellman_primitive_root
  , fmpz_mod_discrete_log_pohlig_hellman_run
  , fmpz_next_smooth_prime
) where 

-- arithmetic modulo integers --------------------------------------------------

import Control.Monad

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr )
import Foreign.Storable
import Foreign.Marshal ( free )

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz

#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpz_mod.h>

-- fmpz_mod_ctx_t --------------------------------------------------------------

data FmpzModCtx = FmpzModCtx {-# UNPACK #-} !(ForeignPtr CFmpzModCtx)
type CFmpzModCtx = CFlint FmpzModCtx

instance Storable CFmpzModCtx where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fmpz_mod_ctx_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fmpz_mod_ctx_t}
  peek = error "CFmpzModCtx.peek: Not defined"
  poke = error "CFmpzModCtx.poke: Not defined"

newFmpzModCtx n = do
  p <- mallocForeignPtr
  withFmpz n $ \n -> 
    withForeignPtr p $ \p ->
      fmpz_mod_ctx_init p n
  addForeignPtrFinalizer p_fmpz_mod_ctx_clear p
  return $ FmpzModCtx p

{-# INLINE withFmpzModCtx #-}
withFmpzModCtx (FmpzModCtx p) f = do
  withForeignPtr p $ \fp -> f fp >>= return . (FmpzModCtx p,)

{-# INLINE withNewFmpzModCtx #-}
withNewFmpzModCtx n f = newFmpzModCtx n >>= flip withFmpzModCtx f

-- Context object --------------------------------------------------------------

-- | /fmpz_mod_ctx_init/ /ctx/ /n/ 
-- 
-- Initialise @ctx@ for arithmetic modulo @n@, which is expected to be
-- positive.
foreign import ccall "fmpz_mod.h fmpz_mod_ctx_init"
  fmpz_mod_ctx_init :: Ptr CFmpzModCtx -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_ctx_clear/ /ctx/ 
-- 
-- Free any memory used by @ctx@.
foreign import ccall "fmpz_mod.h fmpz_mod_ctx_clear"
  fmpz_mod_ctx_clear :: Ptr CFmpzModCtx -> IO ()

foreign import ccall "fmpz_mod.h &fmpz_mod_ctx_clear"
  p_fmpz_mod_ctx_clear :: FunPtr (Ptr CFmpzModCtx -> IO ())

-- | /fmpz_mod_ctx_set_modulus/ /ctx/ /n/ 
-- 
-- Reconfigure @ctx@ for arithmetic modulo @n@.
foreign import ccall "fmpz_mod.h fmpz_mod_ctx_set_modulus"
  fmpz_mod_ctx_set_modulus :: Ptr CFmpzModCtx -> Ptr CFmpz -> IO ()

-- Conversions -----------------------------------------------------------------

-- | /fmpz_mod_set_fmpz/ /a/ /b/ /ctx/ 
-- 
-- Set @a@ to @b@ after reduction modulo the modulus.
foreign import ccall "fmpz_mod.h fmpz_mod_set_fmpz"
  fmpz_mod_set_fmpz :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpzModCtx -> IO ()

-- Arithmetic ------------------------------------------------------------------

-- Unless specified otherwise all functions here expect their relevant
-- arguments to be in the canonical range \([0,n)\). Comparison of elements
-- against each other or against zero can be accomplished with
-- func::fmpz_equal or func::fmpz_is_zero without a context.
--
-- | /fmpz_mod_is_canonical/ /a/ /ctx/ 
-- 
-- Return @1@ if \(a\) is in the canonical range \([0,n)\) and @0@
-- otherwise.
foreign import ccall "fmpz_mod.h fmpz_mod_is_canonical"
  fmpz_mod_is_canonical :: Ptr CFmpz -> Ptr CFmpzModCtx -> IO CInt

-- | /fmpz_mod_is_one/ /a/ /ctx/ 
-- 
-- Return @1@ if \(a\) is \(1\) modulo \(n\) and return @0@ otherwise.
foreign import ccall "fmpz_mod.h fmpz_mod_is_one"
  fmpz_mod_is_one :: Ptr CFmpz -> Ptr CFmpzModCtx -> IO CInt

-- | /fmpz_mod_add/ /a/ /b/ /c/ /ctx/ 
-- 
-- Set \(a\) to \(b+c\) modulo \(n\).
foreign import ccall "fmpz_mod.h fmpz_mod_add"
  fmpz_mod_add :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_add_fmpz/ /a/ /b/ /c/ /ctx/ 
-- 
-- Set \(a\) to \(b+c\) modulo \(n\) where only \(b\) is assumed to be
-- canonical.
foreign import ccall "fmpz_mod.h fmpz_mod_add_fmpz"
  fmpz_mod_add_fmpz :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_sub/ /a/ /b/ /c/ /ctx/ 
-- 
-- Set \(a\) to \(b-c\) modulo \(n\).
foreign import ccall "fmpz_mod.h fmpz_mod_sub"
  fmpz_mod_sub :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_sub_fmpz/ /a/ /b/ /c/ /ctx/ 
-- 
-- Set \(a\) to \(b-c\) modulo \(n\) where only \(b\) is assumed to be
-- canonical.
foreign import ccall "fmpz_mod.h fmpz_mod_sub_fmpz"
  fmpz_mod_sub_fmpz :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_fmpz_sub/ /a/ /b/ /c/ /ctx/ 
-- 
-- Set \(a\) to \(b-c\) modulo \(n\) where only \(c\) is assumed to be
-- canonical.
foreign import ccall "fmpz_mod.h fmpz_mod_fmpz_sub"
  fmpz_mod_fmpz_sub :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_neg/ /a/ /b/ /ctx/ 
-- 
-- Set \(a\) to \(-b\) modulo \(n\).
foreign import ccall "fmpz_mod.h fmpz_mod_neg"
  fmpz_mod_neg :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_mul/ /a/ /b/ /c/ /ctx/ 
-- 
-- Set \(a\) to \(b*c\) modulo \(n\).
foreign import ccall "fmpz_mod.h fmpz_mod_mul"
  fmpz_mod_mul :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_inv/ /a/ /b/ /ctx/ 
-- 
-- Set \(a\) to \(b^{-1}\) modulo \(n\). This function expects that \(b\)
-- is invertible modulo \(n\) and throws if this not the case.
-- Invertibility maybe tested with func:fmpz_mod_pow_fmpz or
-- func:fmpz_mod_divides.
foreign import ccall "fmpz_mod.h fmpz_mod_inv"
  fmpz_mod_inv :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_divides/ /a/ /b/ /c/ /ctx/ 
-- 
-- If \(a*c = b \mod n\) has a solution for \(a\) return \(1\) and set
-- \(a\) to such a solution. Otherwise return \(0\) and leave \(a\)
-- undefined.
foreign import ccall "fmpz_mod.h fmpz_mod_divides"
  fmpz_mod_divides :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpzModCtx -> IO CInt

-- | /fmpz_mod_pow_ui/ /a/ /b/ /e/ /ctx/ 
-- 
-- Set \(a\) to \(b^e\) modulo \(n\).
foreign import ccall "fmpz_mod.h fmpz_mod_pow_ui"
  fmpz_mod_pow_ui :: Ptr CFmpz -> Ptr CFmpz -> CULong -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_pow_fmpz/ /a/ /b/ /e/ /ctx/ 
-- 
-- Try to set \(a\) to \(b^e\) modulo \(n\). If \(e < 0\) and \(b\) is not
-- invertible modulo \(n\), the return is \(0\). Otherwise, the return is
-- \(1\).
foreign import ccall "fmpz_mod.h fmpz_mod_pow_fmpz"
  fmpz_mod_pow_fmpz :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpzModCtx -> IO CInt

-- Discrete Logarithms via Pohlig-Hellman --------------------------------------

-- fmpz_mod_discrete_log_pohlig_hellman_t --------------------------------------

data FmpzModDiscreteLogPohligHellmann = FmpzModDiscreteLogPohligHellmann {-# UNPACK #-} !(ForeignPtr CFmpzModDiscreteLogPohligHellmann)
type CFmpzModDiscreteLogPohligHellmann = CFlint FmpzModDiscreteLogPohligHellmann

instance Storable CFmpzModDiscreteLogPohligHellmann where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fmpz_mod_discrete_log_pohlig_hellman_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fmpz_mod_discrete_log_pohlig_hellman_t}
  peek = error "CCFmpzModDiscreteLogPohligHellmann.peek: Not defined"
  poke = error "CCFmpzModDiscreteLogPohligHellmann.poke: Not defined"

newCFmpzModDiscreteLogPohligHellmann = do
  p <- mallocForeignPtr
  withForeignPtr p fmpz_mod_discrete_log_pohlig_hellman_init
  addForeignPtrFinalizer p_fmpz_mod_discrete_log_pohlig_hellman_clear p
  return $ FmpzModDiscreteLogPohligHellmann p
  
-- | /fmpz_mod_discrete_log_pohlig_hellman_init/ /L/ 
-- 
-- Initialize @L@. Upon initialization @L@ is not ready for computation.
foreign import ccall "fmpz_mod.h fmpz_mod_discrete_log_pohlig_hellman_init"
  fmpz_mod_discrete_log_pohlig_hellman_init :: Ptr CFmpzModDiscreteLogPohligHellmann -> IO ()

-- | /fmpz_mod_discrete_log_pohlig_hellman_clear/ /L/ 
-- 
-- Free any space used by @L@.
foreign import ccall "fmpz_mod.h fmpz_mod_discrete_log_pohlig_hellman_clear"
  fmpz_mod_discrete_log_pohlig_hellman_clear :: Ptr CFmpzModDiscreteLogPohligHellmann -> IO ()

foreign import ccall "fmpz_mod.h &fmpz_mod_discrete_log_pohlig_hellman_clear"
  p_fmpz_mod_discrete_log_pohlig_hellman_clear :: FunPtr (Ptr CFmpzModDiscreteLogPohligHellmann -> IO ())
  
-- | /fmpz_mod_discrete_log_pohlig_hellman_precompute_prime/ /L/ /p/ 
-- 
-- Configure @L@ for discrete logarithms modulo @p@ to an internally chosen
-- base. It is assumed that @p@ is prime. The return is an estimate on the
-- number of multiplications needed for one run.
foreign import ccall "fmpz_mod.h fmpz_mod_discrete_log_pohlig_hellman_precompute_prime"
  fmpz_mod_discrete_log_pohlig_hellman_precompute_prime :: Ptr CFmpzModDiscreteLogPohligHellmann -> Ptr CFmpz -> IO CDouble

-- | /fmpz_mod_discrete_log_pohlig_hellman_primitive_root/ /L/ 
-- 
-- Return the internally stored base.
foreign import ccall "fmpz_mod.h fmpz_mod_discrete_log_pohlig_hellman_primitive_root"
  fmpz_mod_discrete_log_pohlig_hellman_primitive_root :: Ptr CFmpzModDiscreteLogPohligHellmann -> IO (Ptr CFmpz)

-- | /fmpz_mod_discrete_log_pohlig_hellman_run/ /x/ /L/ /y/ 
-- 
-- Set @x@ to the logarithm of @y@ with respect to the internally stored
-- base. @y@ is expected to be reduced modulo the @p@. The function is
-- undefined if the logarithm does not exist.
foreign import ccall "fmpz_mod.h fmpz_mod_discrete_log_pohlig_hellman_run"
  fmpz_mod_discrete_log_pohlig_hellman_run :: Ptr CFmpz -> Ptr CFmpzModDiscreteLogPohligHellmann -> Ptr CFmpz -> IO ()

-- | /fmpz_next_smooth_prime/ /a/ /b/ 
-- 
-- Either return \(1\) and set \(a\) to a smooth prime strictly greater
-- than \(b\), or return \(0\) and set \(a\) to \(0\). The smooth primes
-- returned by this function currently have no prime factor of \(a-1\)
-- greater than \(23\), but this should not be relied upon.
foreign import ccall "fmpz_mod.h fmpz_next_smooth_prime"
  fmpz_next_smooth_prime :: Ptr CFmpz -> Ptr CFmpz -> IO CInt

