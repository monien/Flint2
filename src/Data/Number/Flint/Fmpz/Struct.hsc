{-# language
    CApiFFI
  , FlexibleInstances
  , ForeignFunctionInterface
  , TupleSections
  #-}

module Data.Number.Flint.Fmpz.Struct (
  -- * Flint integers
    Fmpz (..)
  , CFmpz (..)
  -- * Precomputed inverse
  , FmpzPreInvN (..)
  , CFmpzPreInvN (..)
  -- * Comb for multi CRT
  , FmpzComb (..)
  , CFmpzComb (..)
  , FmpzCombTemp (..)
  , CFmpzCombTemp (..)
  -- * Multi CRT
  , FmpzMultiCRT (..)
  , CFmpzMultiCRT(..)
  ) where

-- Types, macros and constants -------------------------------------------------

import System.IO.Unsafe

import Control.Monad

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr, nullPtr )
import Foreign.Storable
import Foreign.Marshal ( free )

import Numeric.GMP.Utils (withInInteger, withOutInteger_) 
import Numeric.GMP.Types (MPZ)

import Data.Number.Flint.Internal
import Data.Number.Flint.External
import Data.Number.Flint.Flint
import Data.Number.Flint.NMod.Struct

#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpz_factor.h>

-- fmpz_t ----------------------------------------------------------------------

-- | Integer (opaque pointer)
data Fmpz = Fmpz {-# UNPACK #-} !(ForeignPtr CFmpz)
type CFmpz = CFlint Fmpz

instance Storable CFmpz where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fmpz_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fmpz_t}
  peek = error "CFmpz.peek: Not defined"
  poke = error "CFmpz.poke: Not defined"
  
-- fmpz_preinv_t --------------------------------------------------

-- | Data structure containing the /CFmpz/ pointer
data FmpzPreInvN = FmpzPreInvN
  {-# UNPACK #-} !(ForeignPtr CFmpzPreInvN) 
type CFmpzPreInvN = CFlint FmpzPreInvN 

-- fmpz_comb_t -----------------------------------------------------------------

data FmpzComb = FmpzComb {-# UNPACK #-} !(ForeignPtr CFmpzComb)
type CFmpzComb = CFlint FmpzComb

instance Storable CFmpzComb where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fmpz_comb_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fmpz_comb_t}
  peek = error "CFmpzComb.peek: Not defined"
  poke = error "CFmpzComb.poke: Not defined"

-- fmpz_comb_temp_t ------------------------------------------------------------

data FmpzCombTemp = FmpzCombTemp {-# UNPACK #-} !(ForeignPtr CFmpzCombTemp)
type CFmpzCombTemp = CFlint FmpzCombTemp

instance Storable CFmpzCombTemp where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fmpz_comb_temp_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fmpz_comb_temp_t}
  peek = error "CFmpzCombTemp.peek: Not defined"
  poke = error "CFmpzCombTemp.poke: Not defined"

-- fmpz_multi_crt_t ------------------------------------------------------------

data FmpzMultiCRT = FmpzMultiCRT {-# UNPACK #-} !(ForeignPtr CFmpzMultiCRT)
type CFmpzMultiCRT = CFlint FmpzMultiCRT

instance Storable CFmpzMultiCRT where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fmpz_multi_crt_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fmpz_multi_crt_t}
  peek = error "CFmpzMultiCRT.peek: Not defined"
  poke = error "CFmpzMultiCRT.poke: Not defined"
