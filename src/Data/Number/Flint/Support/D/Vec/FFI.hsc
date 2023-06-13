module Data.Number.Flint.Support.D.Vec.FFI (
  -- * Double precision vectors
  -- * Memory management
    _d_vec_init
  , _d_vec_clear
  -- * Randomisation
  , _d_vec_randtest
  -- * Assignment and basic manipulation
  , _d_vec_set
  , _d_vec_zero
  -- * Comparison
  , _d_vec_equal
  , _d_vec_is_zero
  , _d_vec_is_approx_zero
  , _d_vec_approx_equal
  -- * Addition and subtraction
  , _d_vec_add
  , _d_vec_sub
  -- * Dot product and norm
  , _d_vec_dot
  , _d_vec_norm
  , _d_vec_dot_heuristic
  , _d_vec_dot_thrice
) where 

-- Double precision vectors ----------------------------------------------------

import Foreign.Ptr
import Foreign.C.Types

import Data.Number.Flint.Flint

-- Memory management -----------------------------------------------------------

-- | /_d_vec_init/ /len/ 
-- 
-- Returns an initialised vector of @double@s of given length. The entries
-- are not zeroed.
foreign import ccall "d_vec.h _d_vec_init"
  _d_vec_init :: CLong -> IO (Ptr CDouble)

-- | /_d_vec_clear/ /vec/ 
-- 
-- Frees the space allocated for @vec@.
foreign import ccall "d_vec.h _d_vec_clear"
  _d_vec_clear :: Ptr CDouble -> IO ()

-- Randomisation ---------------------------------------------------------------

-- | /_d_vec_randtest/ /f/ /state/ /len/ /minexp/ /maxexp/ 
-- 
-- Sets the entries of a vector of the given length to random signed
-- numbers with exponents between @minexp@ and @maxexp@ or zero.
foreign import ccall "d_vec.h _d_vec_randtest"
  _d_vec_randtest :: Ptr CDouble -> Ptr CFRandState -> CLong -> CLong -> CLong -> IO ()

-- Assignment and basic manipulation -------------------------------------------

-- | /_d_vec_set/ /vec1/ /vec2/ /len2/ 
-- 
-- Makes a copy of @(vec2, len2)@ into @vec1@.
foreign import ccall "d_vec.h _d_vec_set"
  _d_vec_set :: Ptr CDouble -> Ptr CDouble -> CLong -> IO ()

-- | /_d_vec_zero/ /vec/ /len/ 
-- 
-- Zeros the entries of @(vec, len)@.
foreign import ccall "d_vec.h _d_vec_zero"
  _d_vec_zero :: Ptr CDouble -> CLong -> IO ()

-- Comparison ------------------------------------------------------------------

-- | /_d_vec_equal/ /vec1/ /vec2/ /len/ 
-- 
-- Compares two vectors of the given length and returns \(1\) if they are
-- equal, otherwise returns \(0\).
foreign import ccall "d_vec.h _d_vec_equal"
  _d_vec_equal :: Ptr CDouble -> Ptr CDouble -> CLong -> IO CInt

-- | /_d_vec_is_zero/ /vec/ /len/ 
-- 
-- Returns \(1\) if @(vec, len)@ is zero, and \(0\) otherwise.
foreign import ccall "d_vec.h _d_vec_is_zero"
  _d_vec_is_zero :: Ptr CDouble -> CLong -> IO CInt

-- | /_d_vec_is_approx_zero/ /vec/ /len/ /eps/ 
-- 
-- Returns \(1\) if the entries of @(vec, len)@ are zero to within @eps@,
-- and \(0\) otherwise.
foreign import ccall "d_vec.h _d_vec_is_approx_zero"
  _d_vec_is_approx_zero :: Ptr CDouble -> CLong -> CDouble -> IO CInt

-- | /_d_vec_approx_equal/ /vec1/ /vec2/ /len/ /eps/ 
-- 
-- Compares two vectors of the given length and returns \(1\) if their
-- entries are within @eps@ of each other, otherwise returns \(0\).
foreign import ccall "d_vec.h _d_vec_approx_equal"
  _d_vec_approx_equal :: Ptr CDouble -> Ptr CDouble -> CLong -> CDouble -> IO CInt

-- Addition and subtraction ----------------------------------------------------

-- | /_d_vec_add/ /res/ /vec1/ /vec2/ /len2/ 
-- 
-- Sets @(res, len2)@ to the sum of @(vec1, len2)@ and @(vec2, len2)@.
foreign import ccall "d_vec.h _d_vec_add"
  _d_vec_add :: Ptr CDouble -> Ptr CDouble -> Ptr CDouble -> CLong -> IO ()

-- | /_d_vec_sub/ /res/ /vec1/ /vec2/ /len2/ 
-- 
-- Sets @(res, len2)@ to @(vec1, len2)@ minus @(vec2, len2)@.
foreign import ccall "d_vec.h _d_vec_sub"
  _d_vec_sub :: Ptr CDouble -> Ptr CDouble -> Ptr CDouble -> CLong -> IO ()

-- Dot product and norm --------------------------------------------------------

-- | /_d_vec_dot/ /vec1/ /vec2/ /len2/ 
-- 
-- Returns the dot product of @(vec1, len2)@ and @(vec2, len2)@.
foreign import ccall "d_vec.h _d_vec_dot"
  _d_vec_dot :: Ptr CDouble -> Ptr CDouble -> CLong -> IO CDouble

-- | /_d_vec_norm/ /vec/ /len/ 
-- 
-- Returns the square of the Euclidean norm of @(vec, len)@.
foreign import ccall "d_vec.h _d_vec_norm"
  _d_vec_norm :: Ptr CDouble -> CLong -> IO CDouble

-- | /_d_vec_dot_heuristic/ /vec1/ /vec2/ /len2/ /err/ 
-- 
-- Returns the dot product of @(vec1, len2)@ and @(vec2, len2)@ by adding
-- up the positive and negative products, and doing a single subtraction of
-- the two sums at the end. @err@ is a pointer to a double in which an
-- error bound for the operation will be stored.
foreign import ccall "d_vec.h _d_vec_dot_heuristic"
  _d_vec_dot_heuristic :: Ptr CDouble -> Ptr CDouble -> CLong -> Ptr CDouble -> IO CDouble

-- | /_d_vec_dot_thrice/ /vec1/ /vec2/ /len2/ /err/ 
-- 
-- Returns the dot product of @(vec1, len2)@ and @(vec2, len2)@ using
-- error-free floating point sums and products to compute the dot product
-- with three times (thrice) the working precision. @err@ is a pointer to a
-- double in which an error bound for the operation will be stored.
-- 
-- This implements the algorithm of Ogita-Rump-Oishi. See
-- <http://www.ti3.tuhh.de/paper/rump/OgRuOi05.pdf>.
foreign import ccall "d_vec.h _d_vec_dot_thrice"
  _d_vec_dot_thrice :: Ptr CDouble -> Ptr CDouble -> CLong -> Ptr CDouble -> IO CDouble

