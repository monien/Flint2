{-# language
  TypeFamilies
#-}

module Data.Number.Flint.Internal.FFI (
    Flint (..)
  , CFlint (..)
) where

import Foreign.C.String (CString (..), peekCString)
import Foreign.C.Types
import Foreign.Marshal.Alloc (free)
import Foreign.Marshal.Array (advancePtr)
import Foreign.ForeignPtr 
import Foreign.Ptr 
import Foreign.Storable

#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpz_factor.h>

class Flint a where
  data CFlint a :: *