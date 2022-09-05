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
  , newFmpzFactor
  , withFmpzFactor
  , withNewFmpzFactor
  -- * Memory management
  , fmpz_factor_init
  , fmpz_factor_clear
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
    <*> #{peek fmpz_factor_struct, sign } ptr
    <*> #{peek fmpz_factor_struct, p    } ptr
    <*> #{peek fmpz_factor_struct, exp  } ptr
    <*> #{peek fmpz_factor_struct, alloc} ptr
    <*> #{peek fmpz_factor_struct, num  } ptr
  poke = error "CFmpzFactor.poke: Not defined"

newFmpzFactor = do
  p <- mallocForeignPtr
  withForeignPtr p fmpz_factor_init
  addForeignPtrFinalizer p_fmpz_factor_clear p
  return $ FmpzFactor p

{-# INLINE withFmpzFactor #-}
withFmpzFactor (FmpzFactor p) f = do
  withForeignPtr p $ \fp -> f fp >>= return . (FmpzFactor p,)

{-# INLINE withNewFmpzFactor #-}
withNewFmpzFactor f = do
  x <- newFmpzFactor
  withFmpzFactor x f

-- An integer may be represented in factored form using the @fmpz_factor_t@
-- data structure. This consists of two @fmpz@ vectors representing bases
-- and exponents, respectively. Canonically, the bases will be prime
-- numbers sorted in ascending order and the exponents will be positive. A
-- separate @int@ field holds the sign, which may be \(-1\), 0 or 1.
--
-- | /fmpz_factor_init/ /factor/ 
-- 
-- Initialises an @fmpz_factor_t@ structure.
foreign import capi "flint/fmpz.h fmpz_factor_init"
  fmpz_factor_init :: Ptr CFmpzFactor -> IO ()

-- | /fmpz_factor_clear/ /factor/ 
-- 
-- Clears an @fmpz_factor_t@ structure.
foreign import capi "flint/fmpz.h fmpz_factor_clear"
  fmpz_factor_clear :: Ptr CFmpzFactor -> IO ()

foreign import capi "flint/fmpz.h &fmpz_factor_clear"
  p_fmpz_factor_clear :: FunPtr (Ptr CFmpzFactor -> IO ())
