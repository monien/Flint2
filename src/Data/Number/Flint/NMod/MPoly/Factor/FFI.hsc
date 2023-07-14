module Data.Number.Flint.NMod.MPoly.Factor.FFI (
  -- * Factorisation of multivariate polynomials over integers mod n
  -- (word-size n)
    NModMPolyFactor (..)
  , CNModMPolyFactor (..)
  , newNModMPolyFactor
  , withNModMPolyFactor
  -- * Memory managment
  , nmod_mpoly_factor_init
  , nmod_mpoly_factor_clear
  -- * Basic manipulation
  , nmod_mpoly_factor_swap
  , nmod_mpoly_factor_length
  , nmod_mpoly_factor_get_constant_ui
  , nmod_mpoly_factor_get_base
  , nmod_mpoly_factor_swap_base
  , nmod_mpoly_factor_get_exp_si
  , nmod_mpoly_factor_sort
  -- * Factorisation
  , nmod_mpoly_factor_squarefree
  , nmod_mpoly_factor
) where 

-- Factorisation of multivariate polynomials over integers mod n (word-size n) -

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
import Data.Number.Flint.MPoly
import Data.Number.Flint.NMod
import Data.Number.Flint.NMod.Types
import Data.Number.Flint.NMod.MPoly

#include <flint/flint.h>
#include <flint/nmod.h>
#include <flint/nmod_poly.h>
#include <flint/nmod_mpoly.h>

-- Types -----------------------------------------------------------------------

data NModMPolyFactor =
  NModMPolyFactor {-# UNPACK #-} !(ForeignPtr CNModMPolyFactor)
data CNModMPolyFactor =
  CNModMPolyFactor CMpLimb (Ptr CNModMPoly)
                   (Ptr CFmpz) CLong CLong

instance Storable CNModMPolyFactor where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size nmod_mpoly_factor_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment nmod_mpoly_factor_t}
  peek ptr = CNModMPolyFactor
    <$> #{peek nmod_mpoly_factor_struct, constant    } ptr
    <*> #{peek nmod_mpoly_factor_struct, poly        } ptr
    <*> #{peek nmod_mpoly_factor_struct, exp         } ptr
    <*> #{peek nmod_mpoly_factor_struct, num         } ptr
    <*> #{peek nmod_mpoly_factor_struct, alloc       } ptr
  poke = error "CNModMPolyFactor.poke: Not defined"

newNModMPolyFactor ctx@(NModMPolyCtx pctx) = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> do
    withNModMPolyCtx ctx $ \ctx -> do
      nmod_mpoly_factor_init x ctx
      addForeignPtrFinalizerEnv p_nmod_mpoly_factor_clear x pctx
  return $ NModMPolyFactor x

withNModMPolyFactor (NModMPolyFactor p) f = do
  withForeignPtr p $ \fp -> f fp >>= return . (NModMPolyFactor p,)
  
-- Memory management -----------------------------------------------------------

-- | /nmod_mpoly_factor_init/ /f/ /ctx/ 
--
-- Initialise /f/.
foreign import ccall "nmod_mpoly_factor.h nmod_mpoly_factor_init"
  nmod_mpoly_factor_init :: Ptr CNModMPolyFactor -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_factor_clear/ /f/ /ctx/ 
--
-- Clear /f/.
foreign import ccall "nmod_mpoly_factor.h nmod_mpoly_factor_clear"
  nmod_mpoly_factor_clear :: Ptr CNModMPolyFactor -> Ptr CNModMPolyCtx -> IO ()

foreign import ccall "nmod_mpoly_factor.h &nmod_mpoly_factor_clear"
  p_nmod_mpoly_factor_clear :: FunPtr (Ptr CNModMPolyFactor -> Ptr CNModMPolyCtx -> IO ())

-- Basic manipulation ----------------------------------------------------------

-- | /nmod_mpoly_factor_swap/ /f/ /g/ /ctx/ 
--
-- Efficiently swap /f/ and /g/.
foreign import ccall "nmod_mpoly_factor.h nmod_mpoly_factor_swap"
  nmod_mpoly_factor_swap :: Ptr CNModMPolyFactor -> Ptr CNModMPolyFactor -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_factor_length/ /f/ /ctx/ 
--
-- Return the length of the product in /f/.
foreign import ccall "nmod_mpoly_factor.h nmod_mpoly_factor_length"
  nmod_mpoly_factor_length :: Ptr CNModMPolyFactor -> Ptr CNModMPolyCtx -> IO CLong

-- | /nmod_mpoly_factor_get_constant_ui/ /f/ /ctx/ 
--
-- Return the constant of /f/.
foreign import ccall "nmod_mpoly_factor.h nmod_mpoly_factor_get_constant_ui"
  nmod_mpoly_factor_get_constant_ui :: Ptr CNModMPolyFactor -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_factor_get_base/ /p/ /f/ /i/ /ctx/ 
foreign import ccall "nmod_mpoly_factor.h nmod_mpoly_factor_get_base"
  nmod_mpoly_factor_get_base :: Ptr CNModMPoly -> Ptr CNModMPolyFactor -> CLong -> Ptr CNModMPolyCtx -> IO ()
-- | /nmod_mpoly_factor_swap_base/ /p/ /f/ /i/ /ctx/ 
--
-- Set (resp. swap) /B/ to (resp. with) the base of the term of index \(i\)
-- in /A/.
foreign import ccall "nmod_mpoly_factor.h nmod_mpoly_factor_swap_base"
  nmod_mpoly_factor_swap_base :: Ptr CNModMPoly -> Ptr CNModMPolyFactor -> CLong -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_factor_get_exp_si/ /f/ /i/ /ctx/ 
--
-- Return the exponent of the term of index \(i\) in /A/. It is assumed to
-- fit an @slong@.
foreign import ccall "nmod_mpoly_factor.h nmod_mpoly_factor_get_exp_si"
  nmod_mpoly_factor_get_exp_si :: Ptr CNModMPolyFactor -> CLong -> Ptr CNModMPolyCtx -> IO CLong

-- | /nmod_mpoly_factor_sort/ /f/ /ctx/ 
--
-- Sort the product of /f/ first by exponent and then by base.
foreign import ccall "nmod_mpoly_factor.h nmod_mpoly_factor_sort"
  nmod_mpoly_factor_sort :: Ptr CNModMPolyFactor -> Ptr CNModMPolyCtx -> IO ()

-- Factorisation ---------------------------------------------------------------

-- | /nmod_mpoly_factor_squarefree/ /f/ /A/ /ctx/ 
--
-- Set /f/ to a factorization of /A/ where the bases are primitive and
-- pairwise relatively prime. If the product of all irreducible factors
-- with a given exponent is desired, it is recommended to call
-- @nmod_mpoly_factor_sort@ and then multiply the bases with the desired
-- exponent.
foreign import ccall "nmod_mpoly_factor.h nmod_mpoly_factor_squarefree"
  nmod_mpoly_factor_squarefree :: Ptr CNModMPolyFactor -> Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO CInt

-- | /nmod_mpoly_factor/ /f/ /A/ /ctx/ 
--
-- Set /f/ to a factorization of /A/ where the bases are irreducible.
foreign import ccall "nmod_mpoly_factor.h nmod_mpoly_factor"
  nmod_mpoly_factor :: Ptr CNModMPolyFactor -> Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO CInt

