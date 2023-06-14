{-# language
    CApiFFI
  , FlexibleInstances
  , ForeignFunctionInterface
  , MultiParamTypeClasses
  , TupleSections
  , TypeFamilies
  #-}

module Data.Number.Flint.NMod.Vec.FFI (
  -- * Vectors over integers mod n (word-size n)
  -- * Memory management
    _nmod_vec_init
  , _nmod_vec_clear
  -- * Random functions
  , _nmod_vec_randtest
  -- * Basic manipulation and comparison
  , _nmod_vec_set
  , _nmod_vec_zero
  , _nmod_vec_swap
  , _nmod_vec_reduce
  , _nmod_vec_max_bits
  , _nmod_vec_equal
  -- * Arithmetic operations
  , _nmod_vec_add
  , _nmod_vec_sub
  , _nmod_vec_neg
  , _nmod_vec_scalar_mul_nmod
  , _nmod_vec_scalar_mul_nmod_shoup
  , _nmod_vec_scalar_addmul_nmod
  -- * Dot products
  , _nmod_vec_dot_bound_limbs
  , _nmod_vec_dot
  , _nmod_vec_dot_rev
  , _nmod_vec_dot_ptr
) where

-- Vectors over integers mod n (word-size n) -----------------------------------

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr )
import Foreign.Storable
import Foreign.Marshal ( free )

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpq
import Data.Number.Flint.NMod

#include <flint/flint.h>
#include <flint/nmod_vec.h>

-- Memory management -----------------------------------------------------------

-- | /_nmod_vec_init/ /len/ 
-- 
-- Returns a vector of the given length. The entries are not necessarily
-- zero.
foreign import ccall "nmod_vec.h _nmod_vec_init"
  _nmod_vec_init :: CLong -> IO (Ptr CMp)

-- | /_nmod_vec_clear/ /vec/ 
-- 
-- Frees the memory used by the given vector.
foreign import ccall "nmod_vec.h _nmod_vec_clear"
  _nmod_vec_clear :: Ptr CMp -> IO ()

-- Random functions ------------------------------------------------------------

-- | /_nmod_vec_randtest/ /vec/ /state/ /len/ /mod/ 
-- 
-- Sets @vec@ to a random vector of the given length with entries reduced
-- modulo @mod.n@.
foreign import ccall "nmod_vec.h _nmod_vec_randtest"
  _nmod_vec_randtest :: Ptr CMp -> Ptr CFRandState -> CLong -> Ptr CNMod -> IO ()

-- Basic manipulation and comparison -------------------------------------------

-- | /_nmod_vec_set/ /res/ /vec/ /len/ 
-- 
-- Copies @len@ entries from the vector @vec@ to @res@.
foreign import ccall "nmod_vec.h _nmod_vec_set"
  _nmod_vec_set :: Ptr CMp -> Ptr CMp -> CLong -> IO ()

-- | /_nmod_vec_zero/ /vec/ /len/ 
-- 
-- Zeros the given vector of the given length.
foreign import ccall "nmod_vec.h _nmod_vec_zero"
  _nmod_vec_zero :: Ptr CMp -> CLong -> IO ()

-- | /_nmod_vec_swap/ /a/ /b/ /length/ 
-- 
-- Swaps the vectors @a@ and @b@ of length \(n\) by actually swapping the
-- entries.
foreign import ccall "nmod_vec.h _nmod_vec_swap"
  _nmod_vec_swap :: Ptr CMp -> Ptr CMp -> CLong -> IO ()

-- | /_nmod_vec_reduce/ /res/ /vec/ /len/ /mod/ 
-- 
-- Reduces the entries of @(vec, len)@ modulo @mod.n@ and set @res@ to the
-- result.
foreign import ccall "nmod_vec.h _nmod_vec_reduce"
  _nmod_vec_reduce :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /_nmod_vec_max_bits/ /vec/ /len/ 
-- 
-- Returns the maximum number of bits of any entry in the vector.
foreign import ccall "nmod_vec.h _nmod_vec_max_bits"
  _nmod_vec_max_bits :: Ptr CMp -> CLong -> IO CFBitCnt

-- | /_nmod_vec_equal/ /vec/ /vec2/ /len/ 
-- 
-- Returns~\`1\` if @(vec, len)@ is equal to @(vec2, len)@, otherwise
-- returns~\`0\`.
foreign import ccall "nmod_vec.h _nmod_vec_equal"
  _nmod_vec_equal :: Ptr CMp -> Ptr CMp -> CLong -> IO CInt

-- Arithmetic operations -------------------------------------------------------

-- | /_nmod_vec_add/ /res/ /vec1/ /vec2/ /len/ /mod/ 
-- 
-- Sets @(res, len)@ to the sum of @(vec1, len)@ and @(vec2, len)@.
foreign import ccall "nmod_vec.h _nmod_vec_add"
  _nmod_vec_add :: Ptr CMp -> Ptr CMp -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /_nmod_vec_sub/ /res/ /vec1/ /vec2/ /len/ /mod/ 
-- 
-- Sets @(res, len)@ to the difference of @(vec1, len)@ and @(vec2, len)@.
foreign import ccall "nmod_vec.h _nmod_vec_sub"
  _nmod_vec_sub :: Ptr CMp -> Ptr CMp -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /_nmod_vec_neg/ /res/ /vec/ /len/ /mod/ 
-- 
-- Sets @(res, len)@ to the negation of @(vec, len)@.
foreign import ccall "nmod_vec.h _nmod_vec_neg"
  _nmod_vec_neg :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /_nmod_vec_scalar_mul_nmod/ /res/ /vec/ /len/ /c/ /mod/ 
-- 
-- Sets @(res, len)@ to @(vec, len)@ multiplied by \(c\). The element \(c\)
-- and all elements of \(vec\) are assumed to be less than \(mod.n\).
foreign import ccall "nmod_vec.h _nmod_vec_scalar_mul_nmod"
  _nmod_vec_scalar_mul_nmod :: Ptr CMp -> Ptr CMp -> CLong -> CMpLimb -> Ptr CNMod -> IO ()

-- | /_nmod_vec_scalar_mul_nmod_shoup/ /res/ /vec/ /len/ /c/ /mod/ 
-- 
-- Sets @(res, len)@ to @(vec, len)@ multiplied by \(c\) using
-- @n_mulmod_shoup@. \(mod.n\) should be less than
-- \(2^{\mathtt{FLINT\_BITS} - 1}\). \(c\) and all elements of \(vec\)
-- should be less than \(mod.n\).
foreign import ccall "nmod_vec.h _nmod_vec_scalar_mul_nmod_shoup"
  _nmod_vec_scalar_mul_nmod_shoup :: Ptr CMp -> Ptr CMp -> CLong -> CMpLimb -> Ptr CNMod -> IO ()

-- | /_nmod_vec_scalar_addmul_nmod/ /res/ /vec/ /len/ /c/ /mod/ 
-- 
-- Adds @(vec, len)@ times \(c\) to the vector @(res, len)@. The element
-- \(c\) and all elements of \(vec\) are assumed to be less than \(mod.n\).
foreign import ccall "nmod_vec.h _nmod_vec_scalar_addmul_nmod"
  _nmod_vec_scalar_addmul_nmod :: Ptr CMp -> Ptr CMp -> CLong -> CMpLimb -> Ptr CNMod -> IO ()

-- Dot products ----------------------------------------------------------------

-- | /_nmod_vec_dot_bound_limbs/ /len/ /mod/ 
-- 
-- Returns the number of limbs (0, 1, 2 or 3) needed to represent the
-- unreduced dot product of two vectors of length @len@ having entries
-- modulo @mod.n@, assuming that @len@ is nonnegative and that @mod.n@ is
-- nonzero. The computed bound is tight. In other words, this function
-- returns the precise limb size of @len@ times @(mod.n - 1) ^ 2@.
foreign import ccall "nmod_vec.h _nmod_vec_dot_bound_limbs"
  _nmod_vec_dot_bound_limbs :: CLong -> Ptr CNMod -> IO CInt

-- | /_nmod_vec_dot/ /vec1/ /vec2/ /len/ /mod/ /nlimbs/ 
-- 
-- Returns the dot product of (@vec1@, @len@) and (@vec2@, @len@). The
-- @nlimbs@ parameter should be 0, 1, 2 or 3, specifying the number of
-- limbs needed to represent the unreduced result.
foreign import ccall "nmod_vec.h _nmod_vec_dot"
  _nmod_vec_dot :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CNMod -> CInt -> IO CMpLimb

-- | /_nmod_vec_dot_rev/ /vec1/ /vec2/ /len/ /mod/ /nlimbs/ 
-- 
-- The same as @_nmod_vec_dot@, but reverses @vec2@.
foreign import ccall "nmod_vec.h _nmod_vec_dot_rev"
  _nmod_vec_dot_rev :: Ptr CMp -> Ptr CMp -> CLong -> Ptr CNMod -> CInt -> IO CMpLimb

-- | /_nmod_vec_dot_ptr/ /vec1/ /vec2/ /offset/ /len/ /mod/ /nlimbs/ 
-- 
-- Returns the dot product of (@vec1@, @len@) and the values at
-- @vec2[i][offset]@. The @nlimbs@ parameter should be 0, 1, 2 or 3,
-- specifying the number of limbs needed to represent the unreduced result.
foreign import ccall "nmod_vec.h _nmod_vec_dot_ptr"
  _nmod_vec_dot_ptr :: Ptr CMp -> Ptr (Ptr CMp) -> CLong -> CLong -> Ptr CNMod -> CInt -> IO CMpLimb

