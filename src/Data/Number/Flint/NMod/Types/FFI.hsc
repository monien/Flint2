
module Data.Number.Flint.NMod.Types.FFI where

import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr
import Foreign.Storable

import Data.Number.Flint.Flint
import Data.Number.Flint.Flint.Internal
import Data.Number.Flint.NMod

#include <flint/nmod_types.h>

-- nmod_poly_t -----------------------------------------------------------------

data NModPoly = NModPoly {-# UNPACK #-} !(ForeignPtr CNModPoly)
type CNModPoly = CFlint NModPoly

instance Storable CNModPoly where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size nmod_poly_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment nmod_poly_t}
  peek = undefined
  poke = undefined

-- nmod_poly_factor_t ----------------------------------------------------------

data NModPolyFactor = NModPolyFactor {-# UNPACK #-}
  !(ForeignPtr CNModPolyFactor)
data CNModPolyFactor = CNModPolyFactor (Ptr CNModPoly) (Ptr CLong) CLong CLong

instance Storable CNModPolyFactor where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size nmod_poly_factor_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment nmod_poly_factor_t}
  peek ptr = do
    p     <- #{peek nmod_poly_factor_struct, p    } ptr
    exp   <- #{peek nmod_poly_factor_struct, exp  } ptr
    num   <- #{peek nmod_poly_factor_struct, num  } ptr
    alloc <- #{peek nmod_poly_factor_struct, alloc} ptr
    return $ CNModPolyFactor p exp num alloc
  poke = undefined

-- nmod_mat_t ------------------------------------------------------------------

data NModMat = NModMat {-# UNPACK #-} !(ForeignPtr CNModMat)
data CNModMat = CNModMat (Ptr CMpLimb) CLong CLong (Ptr (Ptr CMpLimb)) (Ptr CNMod)

instance Storable CNModMat where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size nmod_mat_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment nmod_mat_t}
  peek = undefined
  poke = undefined

-- nmod_poly_mat_t -------------------------------------------------------------

data NModPolyMat = NModPolyMat {-# UNPACK #-} !(ForeignPtr CNModPolyMat)
data CNModPolyMat = CNModPolyMat (Ptr CNModPoly) CLong CLong (Ptr (Ptr CNModPoly)) (Ptr CNMod)

instance Storable CNModPolyMat where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size nmod_poly_mat_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment nmod_poly_mat_t}
  peek ptr = CNModPolyMat
    <$> #{peek nmod_poly_mat_struct, entries} ptr
    <*> #{peek nmod_poly_mat_struct, r      } ptr
    <*> #{peek nmod_poly_mat_struct, c      } ptr
    <*> #{peek nmod_poly_mat_struct, rows   } ptr
    <*> #{peek nmod_poly_mat_struct, modulus} ptr
  poke = error "CNModPolyMat.poke: Not defined."
