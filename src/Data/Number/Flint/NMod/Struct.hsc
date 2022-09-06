{-# language
    CApiFFI
  , FlexibleInstances
  , ForeignFunctionInterface
  , TupleSections
  #-}

module Data.Number.Flint.NMod.Struct (
  -- * Integers mod n (word-size n)
    NMod (..)
  , CNMod (..)
  , NModDiscreteLogPohligHellman (..)
  , CNModDiscreteLogPohligHellman (..)
  ) where
  
-- integers mod n (word-size n) ------------------------------------------------

import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr, nullPtr )
import Foreign.Storable

import Data.Number.Flint.Internal
import Data.Number.Flint.External
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
