{-# language
    CApiFFI
  , FlexibleInstances
  , ForeignFunctionInterface
  , MultiParamTypeClasses
  , TupleSections
  , TypeFamilies
  , ScopedTypeVariables
  #-}

module Data.Number.Flint.NF.FFI (
  -- Number fields
    NF (..)
  , CNF (..)
  , newNF
  , withNF
  , nf_init
  , nf_clear
) where

-- Number fields ---------------------------------------------------------------

import Foreign.ForeignPtr
import Foreign.Ptr
import Foreign.Storable

import Data.Number.Flint.Fmpq.Poly

#include <flint/nf.h>

-- nf_t ------------------------------------------------------------------------

data NF = NF {-# UNPACK #-} !(ForeignPtr CNF)
data CNF = CNF

instance Storable CNF where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size nf_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment nf_t}
  peek = error "CNF.peek is not defined."
  poke = error "CNF.poke is not defined."

--------------------------------------------------------------------------------

-- | Create a new number field
newNF poly = do
  nf <- mallocForeignPtr
  withForeignPtr nf $ \nf ->
    withFmpqPoly poly $ \poly ->
      nf_init nf poly
  addForeignPtrFinalizer p_nf_clear nf 
  return $ NF nf

-- | Use number field
withNF (NF nf) f = do
  withForeignPtr nf $ \fp -> (NF nf,) <$> f fp

--------------------------------------------------------------------------------

-- | /nf_init/ /nf/ /pol/ 
-- 
-- Perform basic initialisation of a number field (for element arithmetic)
-- given a defining polynomial over \(\mathbb{Q}\).
foreign import ccall "nf.h nf_init"
  nf_init :: Ptr CNF -> Ptr CFmpqPoly -> IO ()

-- | /nf_clear/ /nf/ 
-- 
-- Release resources used by a number field object. The object will need
-- initialisation again before it can be used.
foreign import ccall "nf.h nf_clear"
  nf_clear :: Ptr CNF -> IO ()

foreign import ccall "nf.h &nf_clear"
  p_nf_clear :: FunPtr (Ptr CNF -> IO ())
