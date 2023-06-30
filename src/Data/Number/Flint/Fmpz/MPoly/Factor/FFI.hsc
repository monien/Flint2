{-# language
    CApiFFI
  , FlexibleInstances
  , ForeignFunctionInterface
  , MultiParamTypeClasses
  , TupleSections
  , TypeFamilies
  #-}

module Data.Number.Flint.Fmpz.MPoly.Factor.FFI (
  -- * Factorisation of multivariate polynomials over the integers
  -- * Types
    FmpzMPolyFactor (..)
  , CFmpzMPolyFactor (..)
  , newFmpzMPolyFactor
  , withFmpzMPolyFactor
  -- * Memory management
  , fmpz_mpoly_factor_init
  , fmpz_mpoly_factor_clear
  -- * Basic manipulation
  , fmpz_mpoly_factor_swap
  , fmpz_mpoly_factor_length
  , fmpz_mpoly_factor_get_constant_fmpz
  , fmpz_mpoly_factor_get_base
  , fmpz_mpoly_factor_get_exp_si
  , fmpz_mpoly_factor_sort
  -- * Factorisation
  , fmpz_mpoly_factor_squarefree
  , fmpz_mpoly_factor
) where

-- Factorisation of multivariate polynomials over the integers -----------------

import Control.Monad

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, nullPtr, plusPtr )
import Foreign.Storable
import Foreign.Marshal ( free )
import Foreign.Marshal.Array ( advancePtr )

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.MPoly
import Data.Number.Flint.Fmpq
import Data.Number.Flint.MPoly

#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpq.h>
#include <flint/fmpz_mpoly.h>
#include <flint/fmpz_mpoly_factor.h>

-- Types -----------------------------------------------------------------------

data FmpzMPolyFactor =
  FmpzMPolyFactor {-# UNPACK #-} !(ForeignPtr CFmpzMPolyFactor)
data CFmpzMPolyFactor =
  CFmpzMPolyFactor (Ptr CFmpz) (Ptr CFmpz) (Ptr CFmpzMPoly)
                   (Ptr CFmpz) CLong CLong

instance Storable CFmpzMPolyFactor where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fmpz_mpoly_factor_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fmpz_mpoly_factor_t}
  peek ptr = CFmpzMPolyFactor
    <$> #{peek fmpz_mpoly_factor_struct, constant    } ptr
    <*> #{peek fmpz_mpoly_factor_struct, constant_den} ptr
    <*> #{peek fmpz_mpoly_factor_struct, poly        } ptr
    <*> #{peek fmpz_mpoly_factor_struct, exp         } ptr
    <*> #{peek fmpz_mpoly_factor_struct, num         } ptr
    <*> #{peek fmpz_mpoly_factor_struct, alloc       } ptr
  poke = error "CFmpzMPolyFactor.poke: Not defined"

newFmpzMPolyFactor ctx@(FmpzMPolyCtx pctx) = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> do
    withFmpzMPolyCtx ctx $ \ctx -> do
      fmpz_mpoly_factor_init x ctx
      addForeignPtrFinalizerEnv p_fmpz_mpoly_factor_clear x pctx
  return $ FmpzMPolyFactor x

withFmpzMPolyFactor (FmpzMPolyFactor p) f = do
  withForeignPtr p $ \fp -> f fp >>= return . (FmpzMPolyFactor p,)
  
-- Memory management -----------------------------------------------------------

-- | /fmpz_mpoly_factor_init/ /f/ /ctx/ 
-- 
-- Initialise /f/.
foreign import ccall "fmpz_mpoly_factor.h fmpz_mpoly_factor_init"
  fmpz_mpoly_factor_init :: Ptr CFmpzMPolyFactor -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_factor_clear/ /f/ /ctx/ 
-- 
-- Clear /f/.
foreign import ccall "fmpz_mpoly_factor.h fmpz_mpoly_factor_clear"
  fmpz_mpoly_factor_clear :: Ptr CFmpzMPolyFactor -> Ptr CFmpzMPolyCtx -> IO ()

foreign import ccall "fmpz_mpoly_factor.h &fmpz_mpoly_factor_clear"
  p_fmpz_mpoly_factor_clear :: FunPtr (Ptr CFmpzMPolyFactor -> Ptr CFmpzMPolyCtx -> IO ())

-- Basic manipulation ----------------------------------------------------------

-- | /fmpz_mpoly_factor_swap/ /f/ /g/ /ctx/ 
-- 
-- Efficiently swap /f/ and /g/.
foreign import ccall "fmpz_mpoly_factor.h fmpz_mpoly_factor_swap"
  fmpz_mpoly_factor_swap :: Ptr CFmpzMPolyFactor -> Ptr CFmpzMPolyFactor -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_factor_length/ /f/ /ctx/ 
-- 
-- Return the length of the product in /f/.
foreign import ccall "fmpz_mpoly_factor.h fmpz_mpoly_factor_length"
  fmpz_mpoly_factor_length :: Ptr CFmpzMPolyFactor -> Ptr CFmpzMPolyCtx -> IO CLong

-- | /fmpz_mpoly_factor_get_constant_fmpz/ /c/ /f/ /ctx/ 
-- 
-- Set \(c\) to the constant of /f/.
foreign import ccall "fmpz_mpoly_factor.h fmpz_mpoly_factor_get_constant_fmpz"
  fmpz_mpoly_factor_get_constant_fmpz :: Ptr CFmpz -> Ptr CFmpzMPolyFactor -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_factor_get_base/ /B/ /f/ /i/ /ctx/ 
-- 
-- Set (resp. swap) /B/ to (resp. with) the base of the term of index \(i\)
-- in /A/.
foreign import ccall "fmpz_mpoly_factor.h fmpz_mpoly_factor_get_base"
  fmpz_mpoly_factor_get_base :: Ptr CFmpzMPoly -> Ptr CFmpzMPolyFactor -> CLong -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_factor_get_exp_si/ /f/ /i/ /ctx/ 
-- 
-- Return the exponent of the term of index \(i\) in /A/. It is assumed to
-- fit an @slong@.
foreign import ccall "fmpz_mpoly_factor.h fmpz_mpoly_factor_get_exp_si"
  fmpz_mpoly_factor_get_exp_si :: Ptr CFmpzMPolyFactor -> CLong -> Ptr CFmpzMPolyCtx -> IO CLong

-- | /fmpz_mpoly_factor_sort/ /f/ /ctx/
-- 
-- Sort the product of /f/ first by exponent and then by base.
foreign import ccall "fmpz_mpoly_factor.h fmpz_mpoly_factor_sort"
  fmpz_mpoly_factor_sort :: Ptr CFmpzMPolyFactor -> Ptr CFmpzMPolyCtx -> IO ()

-- Factorisation ---------------------------------------------------------------

-- | /fmpz_mpoly_factor_squarefree/ /f/ /A/ /ctx/ 
-- 
-- Set /f/ to a factorization of /A/ where the bases are primitive and
-- pairwise relatively prime. If the product of all irreducible factors
-- with a given exponent is desired, it is recommended to call
-- @fmpz_mpoly_factor_sort@ and then multiply the bases with the desired
-- exponent.
foreign import ccall "fmpz_mpoly_factor.h fmpz_mpoly_factor_squarefree"
  fmpz_mpoly_factor_squarefree :: Ptr CFmpzMPolyFactor -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO CInt

-- | /fmpz_mpoly_factor/ /f/ /A/ /ctx/ 
-- 
-- Set /f/ to a factorization of /A/ where the bases are irreducible.
foreign import ccall "fmpz_mpoly_factor.h fmpz_mpoly_factor"
  fmpz_mpoly_factor :: Ptr CFmpzMPolyFactor -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO CInt

