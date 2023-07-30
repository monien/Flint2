{-|
module      :  Data.Number.Flint.Flint.External.GMP.FFI
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de
-}
module Data.Number.Flint.Flint.External.GMP.FFI where

import Data.Int
import Data.Word
import Foreign.ForeignPtr
import Foreign.C.Types
import Foreign.Storable

import Data.Number.Flint.Flint.Internal

#undef _LONG_LONG_LIMB

#include <gmp.h>

-- BUG: should be set by #type mp_limb_t
-- type MpLimb   = CULong
type CMpLimb   = #type mp_limb_t
type CMpSLimb  = #type mp_limb_signed_t
type CMpSize   = #type mp_size_t
type CMpBitCnt = #type mp_bitcnt_t

-- | Data structure containing the CMp pointer
data Mp = CMp {-# UNPACK #-} !(ForeignPtr CMp) 
type CMp = CFlint Mp

-- | Data structure containing the CMpz pointer
data Mpz = CMpz {-# UNPACK #-} !(ForeignPtr CMpz) 
type CMpz = CFlint Mpz

-- | Data structure containing the CMpq pointer
data Mpq = CMpq {-# UNPACK #-} !(ForeignPtr CMpq) 
type CMpq = CFlint Mpq

-- | Data structure containing the CMpf pointer
data Mpf = CMpf {-# UNPACK #-} !(ForeignPtr CMpf) 
type CMpf = CFlint Mpf

-- | Data structure containing the CGmpRandstate pointer
data GmpRandstate = GmpRandstate {-# UNPACK #-} !(ForeignPtr CGmpRandstate)
type CGmpRandstate = CFlint GmpRandstate

instance Storable CMpf where
  {-# INLINE sizeOf #-}
  sizeOf   _ = #{size       mpf_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment mpf_t}
  peek = undefined
  poke = undefined
