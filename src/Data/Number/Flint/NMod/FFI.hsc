{-# language
    CApiFFI
  , FlexibleInstances
  , ForeignFunctionInterface
  , TupleSections
  #-}

module Data.Number.Flint.NMod.FFI (
  -- * Integers mod n (word-size n)
    NMod (..)
  , CNMod (..)
  -- * Memory management
  , newNMod
  , withNMod
  , withNewNMod
  , nmod_init
  -- * Modular reduction and arithmetic
  , _nmod_add
  , nmod_add
  , _nmod_sub
  , nmod_sub
  , nmod_neg
  , nmod_mul
  , _nmod_mul_fullword
  , nmod_inv
  , nmod_div
  , nmod_pow_ui
  -- * Discrete Logarithms via Pohlig-Hellman
  , NModDiscreteLogPohligHellman (..)
  , CNModDiscreteLogPohligHellman (..)
  , nmod_discrete_log_pohlig_hellman_init
  , nmod_discrete_log_pohlig_hellman_clear
  , nmod_discrete_log_pohlig_hellman_precompute_prime
  , nmod_discrete_log_pohlig_hellman_primitive_root
  , nmod_discrete_log_pohlig_hellman_run
) where 

-- integers mod n (word-size n) ------------------------------------------------

import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr, nullPtr )
import Foreign.Storable

import Data.Number.Flint.Flint

#include <flint/nmod.h>

-- NMod ------------------------------------------------------------------------

data NMod = NMod {-# UNPACK #-} !(ForeignPtr CNMod)
data CNMod = CNMod CMpLimb CMpLimb CFBitCnt

instance Storable CNMod where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size nmod_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment nmod_t}
  peek ptr = return CNMod 
    <*> #{peek nmod_t, n   } ptr
    <*> #{peek nmod_t, ninv} ptr
    <*> #{peek nmod_t, norm} ptr
  poke = error "CNMod.poke: Not defined"

-- NmodDiscreteLogPohligHellman ------------------------------------------------

data NModDiscreteLogPohligHellman =
   NModDiscreteLogPohligHellman !(ForeignPtr CNModDiscreteLogPohligHellman)
type CNModDiscreteLogPohligHellman = CFlint NModDiscreteLogPohligHellman

instance Storable CNModDiscreteLogPohligHellman where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size nmod_discrete_log_pohlig_hellman_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment nmod_discrete_log_pohlig_hellman_t}
  peek ptr = error "CNModDiscreteLogPohligHellman poke: Not defined"
  poke = error "CNMod.poke: Not defined"

-- Modular reduction and arithmetic --------------------------------------------

-- | Create a new `NMod` structure
newNMod n = do
  x <- mallocForeignPtr
  putStrLn $ "newNMod " ++ show x
  withForeignPtr x $ \x -> nmod_init x n
  return $ NMod x

-- | Use `Nmod` structure
{-# INLINE withNMod #-}
withNMod (NMod x) f = do
  withForeignPtr x $ \xp -> f xp >>= return . (NMod x,)

withNewNMod n f = do
  x <- newNMod n
  withNMod x $ \x -> f x

--------------------------------------------------------------------------------

-- | /nmod_init/ /mod/ /n/ 
-- 
-- Initialises the given @nmod_t@ structure for reduction modulo \(n\) with
-- a precomputed inverse.
foreign import ccall "nmod.h nmod_init"
  nmod_init :: Ptr CNMod -> CMpLimb -> IO ()

-- | /_nmod_add/ /a/ /b/ /mod/ 
-- 
-- Returns \(a + b\) modulo @mod.n@. It is assumed that @mod@ is no more
-- than @FLINT_BITS - 1@ bits. It is assumed that \(a\) and \(b\) are
-- already reduced modulo @mod.n@.
foreign import ccall "nmod.h _nmod_add"
  _nmod_add :: CMpLimb -> CMpLimb -> Ptr CNMod -> IO CMpLimb

-- | /nmod_add/ /a/ /b/ /mod/ 
-- 
-- Returns \(a + b\) modulo @mod.n@. No assumptions are made about @mod.n@.
-- It is assumed that \(a\) and \(b\) are already reduced modulo @mod.n@.
foreign import ccall "nmod.h nmod_add"
  nmod_add :: CMpLimb -> CMpLimb -> Ptr CNMod -> IO CMpLimb

-- | /_nmod_sub/ /a/ /b/ /mod/ 
-- 
-- Returns \(a - b\) modulo @mod.n@. It is assumed that @mod@ is no more
-- than @FLINT_BITS - 1@ bits. It is assumed that \(a\) and \(b\) are
-- already reduced modulo @mod.n@.
foreign import ccall "nmod.h _nmod_sub"
  _nmod_sub :: CMpLimb -> CMpLimb -> Ptr CNMod -> IO CMpLimb

-- | /nmod_sub/ /a/ /b/ /mod/ 
-- 
-- Returns \(a - b\) modulo @mod.n@. No assumptions are made about @mod.n@.
-- It is assumed that \(a\) and \(b\) are already reduced modulo @mod.n@.
foreign import ccall "nmod.h nmod_sub"
  nmod_sub :: CMpLimb -> CMpLimb -> Ptr CNMod -> IO CMpLimb

-- | /nmod_neg/ /a/ /mod/ 
-- 
-- Returns \(-a\) modulo @mod.n@. It is assumed that \(a\) is already
-- reduced modulo @mod.n@, but no assumptions are made about the latter.
foreign import ccall "nmod.h nmod_neg"
  nmod_neg :: CMpLimb -> Ptr CNMod -> IO CMpLimb

-- | /nmod_mul/ /a/ /b/ /mod/ 
-- 
-- Returns \(ab\) modulo @mod.n@. No assumptions are made about @mod.n@. It
-- is assumed that \(a\) and \(b\) are already reduced modulo @mod.n@.
foreign import ccall "nmod.h nmod_mul"
  nmod_mul :: CMpLimb -> CMpLimb -> Ptr CNMod -> IO CMpLimb

-- | /_nmod_mul_fullword/ /a/ /b/ /mod/ 
-- 
-- Returns \(ab\) modulo @mod.n@. Requires that @mod.n@ is exactly
-- @FLINT_BITS@ large. It is assumed that \(a\) and \(b\) are already
-- reduced modulo @mod.n@.
foreign import ccall "nmod.h _nmod_mul_fullword"
  _nmod_mul_fullword :: CMpLimb -> CMpLimb -> Ptr CNMod -> IO CMpLimb

-- | /nmod_inv/ /a/ /mod/ 
-- 
-- Returns \(a^{-1}\) modulo @mod.n@. The inverse is assumed to exist.
foreign import ccall "nmod.h nmod_inv"
  nmod_inv :: CMpLimb -> Ptr CNMod -> IO CMpLimb

-- | /nmod_div/ /a/ /b/ /mod/ 
-- 
-- Returns \(ab^{-1}\) modulo @mod.n@. The inverse of \(b\) is assumed to
-- exist. It is assumed that \(a\) is already reduced modulo @mod.n@.
foreign import ccall "nmod.h nmod_div"
  nmod_div :: CMpLimb -> CMpLimb -> Ptr CNMod -> IO CMpLimb

-- | /nmod_pow_ui/ /a/ /e/ /mod/ 
-- 
-- Returns \(a^e\) modulo @mod.n@. No assumptions are made about @mod.n@.
-- It is assumed that \(a\) is already reduced modulo @mod.n@.
foreign import ccall "nmod.h nmod_pow_ui"
  nmod_pow_ui :: CMpLimb -> CULong -> Ptr CNMod -> IO CMpLimb

-- Discrete Logarithms via Pohlig-Hellman --------------------------------------

-- | /nmod_discrete_log_pohlig_hellman_init/ /L/ 
-- 
-- Initialize @L@. Upon initialization @L@ is not ready for computation.
foreign import ccall "nmod.h nmod_discrete_log_pohlig_hellman_init"
  nmod_discrete_log_pohlig_hellman_init :: Ptr CNModDiscreteLogPohligHellman -> IO ()

-- | /nmod_discrete_log_pohlig_hellman_clear/ /L/ 
-- 
-- Free any space used by @L@.
foreign import ccall "nmod.h nmod_discrete_log_pohlig_hellman_clear"
  nmod_discrete_log_pohlig_hellman_clear :: Ptr CNModDiscreteLogPohligHellman -> IO ()

-- | /nmod_discrete_log_pohlig_hellman_precompute_prime/ /L/ /p/ 
-- 
-- Configure @L@ for discrete logarithms modulo @p@ to an internally chosen
-- base. It is assumed that @p@ is prime. The return is an estimate on the
-- number of multiplications needed for one run.
foreign import ccall "nmod.h nmod_discrete_log_pohlig_hellman_precompute_prime"
  nmod_discrete_log_pohlig_hellman_precompute_prime :: Ptr CNModDiscreteLogPohligHellman -> CMpLimb -> IO CDouble

-- | /nmod_discrete_log_pohlig_hellman_primitive_root/ /L/ 
-- 
-- Return the internally stored base.
foreign import ccall "nmod.h nmod_discrete_log_pohlig_hellman_primitive_root"
  nmod_discrete_log_pohlig_hellman_primitive_root :: Ptr CNModDiscreteLogPohligHellman -> IO CMpLimb

-- | /nmod_discrete_log_pohlig_hellman_run/ /L/ /y/ 
-- 
-- Return the logarithm of @y@ with respect to the internally stored base.
-- @y@ is expected to be reduced modulo the @p@. The function is undefined
-- if the logarithm does not exist.
foreign import ccall "nmod.h nmod_discrete_log_pohlig_hellman_run"
  nmod_discrete_log_pohlig_hellman_run :: Ptr CNModDiscreteLogPohligHellman -> CMpLimb -> IO CULong

