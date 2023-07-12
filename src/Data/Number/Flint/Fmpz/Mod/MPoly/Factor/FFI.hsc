
module Data.Number.Flint.Fmpz.Mod.MPoly.Factor.FFI (
  -- * Factorisation of multivariate polynomials over the integers mod n
    FmpzModMPolyFactor (..)
  , CFmpzModMPolyFactor (..)
  , newFmpzModMPolyFactor
  , withFmpzModMPolyFactor
  -- * Memory management
  , fmpz_mod_mpoly_factor_init
  , fmpz_mod_mpoly_factor_clear
  -- * Basic manipulation
  , fmpz_mod_mpoly_factor_swap
  , fmpz_mod_mpoly_factor_length
  , fmpz_mod_mpoly_factor_get_constant_fmpz
  , fmpz_mod_mpoly_factor_get_base
  , fmpz_mod_mpoly_factor_swap_base
  , fmpz_mod_mpoly_factor_get_exp_si
  , fmpz_mod_mpoly_factor_sort
  -- * Factorisation
  , fmpz_mod_mpoly_factor_squarefree
  , fmpz_mod_mpoly_factor
) where

-- Factorisation of multivariate polynomials over the integers mod n -----------

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
import Data.Number.Flint.Fmpz.Poly
import Data.Number.Flint.Fmpq
import Data.Number.Flint.MPoly
import Data.Number.Flint.Fmpz.Mod
import Data.Number.Flint.Fmpz.Mod.MPoly

#include <flint/flint.h>
#include <flint/fmpz_mod_mpoly.h>
#include <flint/fmpz_mod_mpoly_factor.h>

-- fmpz_mod_mpoly_t ------------------------------------------------------------

data FmpzModMPolyFactor = FmpzModMPolyFactor {-# UNPACK #-} !(ForeignPtr CFmpzModMPolyFactor)
data CFmpzModMPolyFactor = CFmpzModMPolyFactor 

instance Storable CFmpzModMPolyFactor where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fmpz_mod_mpoly_factor_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fmpz_mod_mpoly_factor_t}
  peek = error "CFmpzModMPolyFactor.peek: Not defined"
  poke = error "CFmpzModMPolyFactor.poke: Not defined"

-- | Create a new `FmpzModMPolyFactor`
newFmpzModMPolyFactor ctx@(FmpzModMPolyCtx pctx) = do
  p <- mallocForeignPtr
  withForeignPtr p $ \p ->
    withFmpzModMPolyCtx ctx $ \ctx -> do 
      fmpz_mod_mpoly_factor_init p ctx
      addForeignPtrFinalizerEnv p_fmpz_mod_mpoly_factor_clear p pctx 
  return $ FmpzModMPolyFactor p

{-# INLINE withFmpzModMPolyFactor #-}
withFmpzModMPolyFactor (FmpzModMPolyFactor p) f = do
  withForeignPtr p $ \fp -> (FmpzModMPolyFactor p,) <$> f fp

-- Memory management -----------------------------------------------------------

-- | /fmpz_mod_mpoly_factor_init/ /f/ /ctx/ 
--
-- Initialise /f/.
foreign import ccall "fmpz_mod_mpoly_factor.h fmpz_mod_mpoly_factor_init"
  fmpz_mod_mpoly_factor_init :: Ptr CFmpzModMPolyFactor -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_factor_clear/ /f/ /ctx/ 
--
-- Clear /f/.
foreign import ccall "fmpz_mod_mpoly_factor.h fmpz_mod_mpoly_factor_clear"
  fmpz_mod_mpoly_factor_clear :: Ptr CFmpzModMPolyFactor -> Ptr CFmpzModMPolyCtx -> IO ()

foreign import ccall "fmpz_mod_mpoly_factor.h &fmpz_mod_mpoly_factor_clear"
  p_fmpz_mod_mpoly_factor_clear :: FunPtr (Ptr CFmpzModMPolyFactor -> Ptr CFmpzModMPolyCtx -> IO ())

-- Basic manipulation ----------------------------------------------------------

-- | /fmpz_mod_mpoly_factor_swap/ /f/ /g/ /ctx/ 
--
-- Efficiently swap /f/ and /g/.
foreign import ccall "fmpz_mod_mpoly_factor.h fmpz_mod_mpoly_factor_swap"
  fmpz_mod_mpoly_factor_swap :: Ptr CFmpzModMPolyFactor -> Ptr CFmpzModMPolyFactor -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_factor_length/ /f/ /ctx/ 
--
-- Return the length of the product in /f/.
foreign import ccall "fmpz_mod_mpoly_factor.h fmpz_mod_mpoly_factor_length"
  fmpz_mod_mpoly_factor_length :: Ptr CFmpzModMPolyFactor -> Ptr CFmpzModMPolyCtx -> IO CLong

-- | /fmpz_mod_mpoly_factor_get_constant_fmpz/ /c/ /f/ /ctx/ 
--
-- Set /c/ to the constant of /f/.
foreign import ccall "fmpz_mod_mpoly_factor.h fmpz_mod_mpoly_factor_get_constant_fmpz"
  fmpz_mod_mpoly_factor_get_constant_fmpz :: Ptr CFmpz -> Ptr CFmpzModMPolyFactor -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_factor_get_base/ /B/ /f/ /i/ /ctx/ 
foreign import ccall "fmpz_mod_mpoly_factor.h fmpz_mod_mpoly_factor_get_base"
  fmpz_mod_mpoly_factor_get_base :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyFactor -> CLong -> Ptr CFmpzModMPolyCtx -> IO ()
-- | /fmpz_mod_mpoly_factor_swap_base/ /B/ /f/ /i/ /ctx/ 
--
-- Set (resp. swap) /B/ to (resp. with) the base of the term of index /i/
-- in /f/.
foreign import ccall "fmpz_mod_mpoly_factor.h fmpz_mod_mpoly_factor_swap_base"
  fmpz_mod_mpoly_factor_swap_base :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyFactor -> CLong -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_factor_get_exp_si/ /f/ /i/ /ctx/ 
--
-- Return the exponent of the term of index /i/ in /f/. It is assumed to
-- fit an @slong@.
foreign import ccall "fmpz_mod_mpoly_factor.h fmpz_mod_mpoly_factor_get_exp_si"
  fmpz_mod_mpoly_factor_get_exp_si :: Ptr CFmpzModMPolyFactor -> CLong -> Ptr CFmpzModMPolyCtx -> IO CLong

-- | /fmpz_mod_mpoly_factor_sort/ /f/ /ctx/ 
--
-- Sort the product of /f/ first by exponent and then by base.
foreign import ccall "fmpz_mod_mpoly_factor.h fmpz_mod_mpoly_factor_sort"
  fmpz_mod_mpoly_factor_sort :: Ptr CFmpzModMPolyFactor -> Ptr CFmpzModMPolyCtx -> IO ()

-- Factorisation ---------------------------------------------------------------




-- | /fmpz_mod_mpoly_factor_squarefree/ /f/ /A/ /ctx/ 
--
-- Set /f/ to a factorization of /A/ where the bases are primitive and
-- pairwise relatively prime. If the product of all irreducible factors
-- with a given exponent is desired, it is recommended to call
-- @fmpz_mod_mpoly_factor_sort@ and then multiply the bases with the
-- desired exponent.
foreign import ccall "fmpz_mod_mpoly_factor.h fmpz_mod_mpoly_factor_squarefree"
  fmpz_mod_mpoly_factor_squarefree :: Ptr CFmpzModMPolyFactor -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO CInt

-- | /fmpz_mod_mpoly_factor/ /f/ /A/ /ctx/ 
--
-- Set /f/ to a factorization of /A/ where the bases are irreducible.
foreign import ccall "fmpz_mod_mpoly_factor.h fmpz_mod_mpoly_factor"
  fmpz_mod_mpoly_factor :: Ptr CFmpzModMPolyFactor -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO CInt

