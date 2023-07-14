{-|
module      :  Data.Number.Flint.FFT.Small.FFI
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de
-}
module Data.Number.Flint.FFT.Small.FFI (
  -- * FFT modulo word-size primes
  -- * Integer multiplication
    MpnCtx (..)
  , CMpnCtx (..)
  , newMpnCtx
  , withMpnCtx
  , mpn_ctx_init
  , mpn_ctx_clear
  , get_default_mpn_ctx
  , mpn_ctx_mpn_mul
  , mpn_mul_default_mpn_ctx
  -- * Polynomial arithmetic
  , _nmod_poly_mul_mid_mpn_ctx
  , _nmod_poly_mul_mid_default_mpn_ctx
  , _fmpz_poly_mul_mid_mpn_ctx
  , _fmpz_poly_mul_mid_default_mpn_ctx
  -- , _nmod_poly_divrem_mpn_ctx
  -- -- * Preconditioned polynomial arithmetic
  -- , _mul_precomp_init
  -- , _mul_precomp_clear
  -- , _nmod_poly_mul_mid_precomp
  -- , _nmod_poly_divrem_precomp_init
  -- , _nmod_poly_divrem_precomp_clear
  -- , _nmod_poly_divrem_precomp
) where

-- FFT modulo word-size primes -------------------------------------------------

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.C.Types

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.NMod
import Data.Number.Flint.NMod.Poly

#include <flint/fft_small.h>

-- mpn_ctx_t -------------------------------------------------------------------

data MpnCtx = MpnCtx {-#UNPACK#-} !(ForeignPtr CMpnCtx)
type CMpnCtx = CFlint MpnCtx

newMpnCtx r = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> do
    mpn_ctx_init x r
  addForeignPtrFinalizer p_mpn_ctx_clear x
  return $ MpnCtx x

withMpnCtx (MpnCtx x) f = do
  withForeignPtr x $ \px -> (MpnCtx x,) <$> f px

instance Storable CMpnCtx where
  sizeOf    _ = #{size      mpn_ctx_t}
  alignment _ = #{alignment mpn_ctx_t}
  peek = undefined
  poke = undefined

-- Integer multiplication ------------------------------------------------------

-- | /mpn_ctx_init/ /R/ /p/ 
--
-- Initialize multiplication context object with initial prime @p@.
foreign import ccall "fft_small.h mpn_ctx_init"
  mpn_ctx_init :: Ptr CMpnCtx -> CULong -> IO ()

-- | /mpn_ctx_clear/ /R/ 
--
-- Free memory allocated by the context object.
foreign import ccall "fft_small.h mpn_ctx_clear"
  mpn_ctx_clear :: Ptr CMpnCtx -> IO ()

foreign import ccall "fft_small.h p_mpn_ctx_clear"
  p_mpn_ctx_clear :: FunPtr (Ptr CMpnCtx -> IO ())

-- | /get_default_mpn_ctx/ 
--
-- Return a pointer to a cached thread-local context object used by default
-- for multiplications. Calling @flint_cleanup@ or @flint_cleanup_master@
-- frees the cache.
foreign import ccall "fft_small.h get_default_mpn_ctx"
  get_default_mpn_ctx :: IO (Ptr CMpnCtx)

-- | /mpn_ctx_mpn_mul/ /R/ /r1/ /i1/ /n1/ /i2/ /n2/ 
foreign import ccall "fft_small.h mpn_ctx_mpn_mul"
  mpn_ctx_mpn_mul :: Ptr CMpnCtx -> Ptr CULong -> Ptr CULong -> CULong -> Ptr CULong -> CULong -> IO ()
  
-- | /mpn_mul_default_mpn_ctx/ /r1/ /i1/ /n1/ /i2/ /n2/ 
--
-- Writes to @r1@ the product of the integers @(i1, n1)@ and @(i2, n2)@.
-- Assumes that \(n_1 \ge n_2 \ge 1\), respectively using a given context
-- object @R@ or the default thread-local object.
foreign import ccall "fft_small.h mpn_mul_default_mpn_ctx"
  mpn_mul_default_mpn_ctx :: Ptr CMp -> Ptr CMp -> CMpSize -> Ptr CMp -> CMpSize -> IO ()

-- Polynomial arithmetic -------------------------------------------------------

-- | /_nmod_poly_mul_mid_mpn_ctx/ /z/ /zl/ /zh/ /a/ /an/ /b/ /bn/ /mod/ /R/ 
foreign import ccall "fft_small.h _nmod_poly_mul_mid_mpn_ctx"
  _nmod_poly_mul_mid_mpn_ctx :: Ptr CULong -> CULong -> CULong -> Ptr CULong -> CULong -> Ptr CULong -> CULong -> Ptr CNMod -> Ptr CMpnCtx -> IO ()
-- | /_nmod_poly_mul_mid_default_mpn_ctx/ /res/ /zl/ /zh/ /a/ /an/ /b/ /bn/ /mod/ 
--
-- Writes to @z@ the middle product containing coefficients in the range
-- \([zl, zh)\) of the product of the polynomials @(a, an)@ and @(b, bn)@,
-- respectively using a given context object @R@ or the default
-- thread-local object. Assumes that \(an \ge bn \ge 1\).
foreign import ccall "fft_small.h _nmod_poly_mul_mid_default_mpn_ctx"
  _nmod_poly_mul_mid_default_mpn_ctx :: Ptr CMp -> CLong -> CLong -> Ptr CMp -> CLong -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /_fmpz_poly_mul_mid_mpn_ctx/ /z/ /zl/ /zh/ /a/ /an/ /b/ /bn/ /R/ 
foreign import ccall "fft_small.h _fmpz_poly_mul_mid_mpn_ctx"
  _fmpz_poly_mul_mid_mpn_ctx :: Ptr CFmpz -> CULong -> CULong -> Ptr CFmpz -> CULong -> Ptr CFmpz -> CULong -> Ptr CMpnCtx -> IO CInt
-- | /_fmpz_poly_mul_mid_default_mpn_ctx/ /z/ /zl/ /zh/ /a/ /an/ /b/ /bn/ 
--
-- Like the @nmod@ functions. Performs the multiplication and returns 1 if
-- there are sufficiently many primes @R@ to compute the result; otherwise
-- returns 0 without touching the output.
foreign import ccall "fft_small.h _fmpz_poly_mul_mid_default_mpn_ctx"
  _fmpz_poly_mul_mid_default_mpn_ctx :: Ptr CFmpz -> CULong -> CULong -> Ptr CFmpz -> CULong -> Ptr CFmpz -> CULong -> IO CInt

-- | /_nmod_poly_divrem_mpn_ctx/ /q/ /r/ /a/ /an/ /b/ /bn/ /mod/ /R/ 
--
-- Polynomial division with remainder.
foreign import ccall "fft_small.h _nmod_poly_divrem_mpn_ctx"
  _nmod_poly_divrem_mpn_ctx :: Ptr CULong -> Ptr CULong -> Ptr CULong -> CULong -> Ptr CULong -> CULong -> Ptr CNMod -> Ptr CMpnCtx -> IO ()

-- Preconditioned polynomial arithmetic ----------------------------------------

-- -- | /_mul_precomp_init/ /M/ /b/ /bn/ /btrunc/ /depth/ /mod/ /R/ 
-- foreign import ccall "fft_small.h _mul_precomp_init"
--   _mul_precomp_init :: Ptr Ptr CMulPrecomp -> Ptr CULong -> CULong -> CULong -> CULong -> Ptr CNMod -> Ptr CMpnCtx -> IO ()
-- -- | /_mul_precomp_clear/ /M/ 
-- --
-- -- Represents @(b, bn)@ in transformed form for preconditioned
-- -- multiplication.
-- foreign import ccall "fft_small.h _mul_precomp_clear"
--   _mul_precomp_clear :: Ptr Ptr CMulPrecomp -> IO ()

-- -- | /_nmod_poly_mul_mid_precomp/ /z/ /zl/ /zh/ /a/ /an/ /M/ /mod/ /R/ 
-- --
-- -- Polynomial multiplication given a precomputed transform @M@. Returns 1
-- -- if successful, 0 if the precomputed transform is too short.
-- foreign import ccall "fft_small.h _nmod_poly_mul_mid_precomp"
--   _nmod_poly_mul_mid_precomp :: Ptr CULong -> CULong -> CULong -> Ptr CULong -> CULong -> Ptr Ptr CMulPrecomp -> Ptr CNMod -> Ptr CMpnCtx -> IO CInt

-- -- | /_nmod_poly_divrem_precomp_init/ /M/ /b/ /bn/ /Bn/ /mod/ /R/ 
-- foreign import ccall "fft_small.h _nmod_poly_divrem_precomp_init"
--   _nmod_poly_divrem_precomp_init :: Ptr Ptr CNModPolyDivremPrecomp -> Ptr CULong -> CULong -> CULong -> Ptr CNMod -> Ptr CMpnCtx -> IO ()
-- -- | /_nmod_poly_divrem_precomp_clear/ /M/ 
-- --
-- -- Represents @(b, bn)@ and its inverse in transformed form for
-- -- preconditioned multiplication.
-- foreign import ccall "fft_small.h _nmod_poly_divrem_precomp_clear"
--   _nmod_poly_divrem_precomp_clear :: Ptr (Ptr CNModPolyDivremPrecomp) -> IO ()

-- -- | /_nmod_poly_divrem_precomp/ /q/ /r/ /a/ /an/ /M/ /mod/ /R/ 
-- --
-- -- Polynomial multiplication given a precomputed transform @M@. Returns 1
-- -- if successful, 0 if the precomputed transform is too short.
-- foreign import ccall "fft_small.h _nmod_poly_divrem_precomp"
--   _nmod_poly_divrem_precomp :: Ptr CULong -> Ptr CULong -> Ptr CULong -> CULong -> Ptr (Ptr CNModPolyDivremPrecomp) -> Ptr CNMod -> Ptr CMpnCtx -> IO CInt

