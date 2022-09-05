module Data.Number.Flint.External.GMP.FFI where

import Data.Int
import Data.Word
import Foreign.ForeignPtr
import Foreign.C.Types
import Data.Number.Flint.Internal

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
