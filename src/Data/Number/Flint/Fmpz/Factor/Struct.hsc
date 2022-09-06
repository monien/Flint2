{-# language
    CApiFFI
  , FlexibleInstances
  , ForeignFunctionInterface
  , MultiParamTypeClasses
  , TupleSections
  , TypeFamilies
  #-}
  
module Data.Number.Flint.Fmpz.Factor.Struct (
  -- * Types
    FmpzFactor (..)
  , CFmpzFactor (..)
  , Ecm (..)
  , CEcm (..)
  ) where

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr )
import Foreign.Storable
import Foreign.Marshal ( free )

import Data.Number.Flint.External
import Data.Number.Flint.Internal
import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz.Struct

#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpz_factor.h>

-- fmpz_factor_t ---------------------------------------------------------------

data FmpzFactor = FmpzFactor {-# UNPACK #-} !(ForeignPtr CFmpzFactor)
data CFmpzFactor = CFmpzFactor CInt (Ptr CFmpz) (Ptr CULong) CLong CLong

instance Storable CFmpzFactor where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fmpz_factor_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fmpz_factor_t}
  peek ptr = CFmpzFactor
    <$> #{peek fmpz_factor_struct, sign } ptr
    <*> #{peek fmpz_factor_struct, p    } ptr
    <*> #{peek fmpz_factor_struct, exp  } ptr
    <*> #{peek fmpz_factor_struct, alloc} ptr
    <*> #{peek fmpz_factor_struct, num  } ptr
  poke = error "CFmpzFactor.poke: Not defined"

data Ecm = Ecm {-# UNPACK #-} !(ForeignPtr CEcm)
type CEcm = CFlint Ecm

