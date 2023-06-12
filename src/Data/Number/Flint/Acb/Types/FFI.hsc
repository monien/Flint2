module Data.Number.Flint.Acb.Types.FFI where

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, nullPtr, plusPtr )
import Foreign.Storable
import Foreign.Marshal ( free )
import Foreign.Marshal.Array ( advancePtr )

import Data.Number.Flint.Flint.Internal
import Data.Number.Flint.Arb.Types

#include <flint/acb.h>

-- | Data structure containing the CMag pointer
data Acb = Acb {-# UNPACK #-} !(ForeignPtr CAcb)
data CAcb = CAcb Arb Arb
