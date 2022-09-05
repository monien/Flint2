module Data.Number.Flint.NMod.Functions (
  -- * Modular reduction and arithmetic
    _nmod_add
  , nmod_add
  , _nmod_sub
  , nmod_sub
  , nmod_neg
  , nmod_mul
  , _nmod_mul_fullword
  , nmod_inv
  , nmod_div
  , nmod_pow_ui
  , nmod_pow_fmpz
  -- * Discrete Logarithms via Pohlig-Hellman
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

import Data.Number.Flint.Internal
import Data.Number.Flint.External

import Data.Number.Flint.Fmpz
import Data.Number.Flint.NMod.Struct

#include <flint/nmod.h>

-- Modular reduction and arithmetic --------------------------------------------

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

-- | /nmod_pow_fmpz/ /a/ /e/ /mod/ 
-- 
-- Returns \(a^e\) modulo @mod.n@. No assumptions are made about @mod.n@.
-- It is assumed that \(a\) is already reduced modulo @mod.n@ and that
-- \(e\) is not negative.
foreign import ccall "nmod.h nmod_pow_fmpz"
  nmod_pow_fmpz :: CMpLimb -> Ptr CFmpz -> Ptr CNMod -> IO CMpLimb

-- Discrete Logarithms via Pohlig-Hellman --------------------------------------

data NmodDiscreteLogPohligHellma = NmodDiscreteLogPohligHellma {-# UNPACK #-}
  !(ForeignPtr CNmodDiscreteLogPohligHellma)

typw CNmodDiscreteLogPohligHellma = CFlint NmodDiscreteLogPohligHellma

-- | /nmod_discrete_log_pohlig_hellman_init/ /L/ 
-- 
-- Initialize @L@. Upon initialization @L@ is not ready for computation.
foreign import ccall "nmod.h nmod_discrete_log_pohlig_hellman_init"
  nmod_discrete_log_pohlig_hellman_init :: Ptr CNmodDiscreteLogPohligHellman -> IO ()

-- | /nmod_discrete_log_pohlig_hellman_clear/ /L/ 
-- 
-- Free any space used by @L@.
foreign import ccall "nmod.h nmod_discrete_log_pohlig_hellman_clear"
  nmod_discrete_log_pohlig_hellman_clear :: Ptr CNmodDiscreteLogPohligHellman -> IO ()

-- | /nmod_discrete_log_pohlig_hellman_precompute_prime/ /L/ /p/ 
-- 
-- Configure @L@ for discrete logarithms modulo @p@ to an internally chosen
-- base. It is assumed that @p@ is prime. The return is an estimate on the
-- number of multiplications needed for one run.
foreign import ccall "nmod.h nmod_discrete_log_pohlig_hellman_precompute_prime"
  nmod_discrete_log_pohlig_hellman_precompute_prime :: Ptr CNmodDiscreteLogPohligHellman -> CMpLimb -> IO CDouble

-- | /nmod_discrete_log_pohlig_hellman_primitive_root/ /L/ 
-- 
-- Return the internally stored base.
foreign import ccall "nmod.h nmod_discrete_log_pohlig_hellman_primitive_root"
  nmod_discrete_log_pohlig_hellman_primitive_root :: Ptr CNmodDiscreteLogPohligHellman -> IO CMpLimb

-- | /nmod_discrete_log_pohlig_hellman_run/ /L/ /y/ 
-- 
-- Return the logarithm of @y@ with respect to the internally stored base.
-- @y@ is expected to be reduced modulo the @p@. The function is undefined
-- if the logarithm does not exist.
foreign import ccall "nmod.h nmod_discrete_log_pohlig_hellman_run"
  nmod_discrete_log_pohlig_hellman_run :: Ptr CNmodDiscreteLogPohligHellman -> CMpLimb -> IO CULong

