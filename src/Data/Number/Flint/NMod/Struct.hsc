{-# language 
  TupleSections
#-}

module Data.Number.Flint.NMod.Struct (
  -- * Integers mod n (word-size n)
    NMod (..)
  , CNMod (..)
  -- * Memory management
  , newNMod
  , withNMod
  , withNewNMod
  , nmod_init
  ) where
  
-- integers mod n (word-size n) ------------------------------------------------

import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr, nullPtr )
import Foreign.Storable

import Data.Number.Flint.Internal
import Data.Number.Flint.External

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

-- | Create a new `NMod` structure
newNMod n = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> nmod_init x n
  return $ NMod x

-- | Use `Nmod` structure
{-# INLINE withNMod #-}
withNMod (NMod x) f = do
  withForeignPtr x $ \xp -> f xp >>= return . (NMod x,)

withNewNMod n f = do
  x <- newNMod n
  withNMod x $ \x -> f x

--------------------------------------------------------------------------------

-- | /nmod_init/ /mod/ /n/ 
-- 
-- Initialises the given @nmod_t@ structure for reduction modulo \(n\) with
-- a precomputed inverse.
foreign import ccall "nmod.h nmod_init"
  nmod_init :: Ptr CNMod -> CMpLimb -> IO ()
