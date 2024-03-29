{-|
module      :  Data.Number.Flint.Acb.Types.FFI
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de
-}
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

-- | An CArb consists of a pair of Arb:s. 
data Acb = Acb {-# UNPACK #-} !(ForeignPtr CAcb)
data CAcb = CAcb CArb CArb

-- | An Acf structure consists of a pair of arf_struct:s. An acf_t is
-- defined as an array of length one of type acf_struct, permitting an
-- acf_t to be passed by reference.
data Acf = Acf {-# UNPACK #-} !(ForeignPtr CAcf)
data CAcf = CAcf CArf CArf
