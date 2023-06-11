{-# language
    CApiFFI
  , FlexibleInstances
  , ForeignFunctionInterface
  , MultiParamTypeClasses
  , TupleSections
  , TypeFamilies
#-}

module Data.Number.Flint.Fmpq.Vec.FFI (
  -- * Vectors over rational numbers
  -- * Memory management
    _fmpq_vec_init
  , _fmpq_vec_clear
  -- * Randomisation
  , _fmpq_vec_randtest
  , _fmpq_vec_randtest_uniq_sorted
  -- * Sorting
  , _fmpq_vec_sort
  -- * Conversions
  , _fmpq_vec_set_fmpz_vec
  , _fmpq_vec_get_fmpz_vec_fmpz
  -- * Dot product
  , _fmpq_vec_dot
  -- * Input and output
  , _fmpq_vec_get_str
  , _fmpq_vec_fprint
  , _fmpq_vec_print
) where 

-- vectors over rational numbers -----------------------------------------------

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr, nullPtr, castPtr )
import Foreign.Storable
import Foreign.Marshal ( free )

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpq

#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpz_vec.h>
#include <flint/fmpq_vec.h>

-- Memory management -----------------------------------------------------------

-- | /_fmpq_vec_init/ /n/ 
-- 
-- Initialises a vector of @fmpq@ values of length \(n\) and sets all
-- values to 0. This is equivalent to generating a @fmpz@ vector of length
-- \(2n\) with @_fmpz_vec_init@ and setting all denominators to 1.
foreign import ccall "fmpq_vec.h _fmpq_vec_init"
  _fmpq_vec_init :: CLong -> IO (Ptr CFmpq)

-- | /_fmpq_vec_clear/ /vec/ /n/ 
-- 
-- Frees an @fmpq@ vector.
foreign import ccall "fmpq_vec.h _fmpq_vec_clear"
  _fmpq_vec_clear :: Ptr CFmpq -> CLong -> IO ()

-- Randomisation ---------------------------------------------------------------

-- | /_fmpq_vec_randtest/ /f/ /state/ /len/ /bits/ 
-- 
-- Sets the entries of a vector of the given length to random rationals
-- with numerator and denominator having up to the given number of bits per
-- entry.
foreign import ccall "fmpq_vec.h _fmpq_vec_randtest"
  _fmpq_vec_randtest :: Ptr CFmpq -> Ptr CFRandState -> CLong -> CFBitCnt -> IO ()

-- | /_fmpq_vec_randtest_uniq_sorted/ /vec/ /state/ /len/ /bits/ 
-- 
-- Sets the entries of a vector of the given length to random distinct
-- rationals with numerator and denominator having up to the given number
-- of bits per entry. The entries in the vector are sorted.
foreign import ccall "fmpq_vec.h _fmpq_vec_randtest_uniq_sorted"
  _fmpq_vec_randtest_uniq_sorted :: Ptr CFmpq -> Ptr CFRandState -> CLong -> CFBitCnt -> IO ()

-- Sorting ---------------------------------------------------------------------

-- | /_fmpq_vec_sort/ /vec/ /len/ 
-- 
-- Sorts the entries of @(vec, len)@.
foreign import ccall "fmpq_vec.h _fmpq_vec_sort"
  _fmpq_vec_sort :: Ptr CFmpq -> CLong -> IO ()

-- Conversions -----------------------------------------------------------------

-- | /_fmpq_vec_set_fmpz_vec/ /res/ /vec/ /len/ 
-- 
-- Sets @(res, len)@ to @(vec, len)@.
foreign import ccall "fmpq_vec.h _fmpq_vec_set_fmpz_vec"
  _fmpq_vec_set_fmpz_vec :: Ptr CFmpq -> Ptr CFmpz -> CLong -> IO ()

-- | /_fmpq_vec_get_fmpz_vec_fmpz/ /num/ /den/ /a/ /len/ 
-- 
-- Find a common denominator @den@ of the entries of @a@ and set
-- @(num, len)@ to the corresponding numerators.
foreign import ccall "fmpq_vec.h _fmpq_vec_get_fmpz_vec_fmpz"
  _fmpq_vec_get_fmpz_vec_fmpz :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpq -> CLong -> IO ()

-- Dot product -----------------------------------------------------------------

-- | /_fmpq_vec_dot/ /res/ /vec1/ /vec2/ /len/ 
-- 
-- Sets @res@ to the dot product of the vectors @(vec1, len)@ and
-- @(vec2, len)@.
foreign import ccall "fmpq_vec.h _fmpq_vec_dot"
  _fmpq_vec_dot :: Ptr CFmpq -> Ptr CFmpq -> Ptr CFmpq -> CLong -> IO ()

-- Input and output ------------------------------------------------------------

foreign import ccall "fmpz_vec.h _fmpq_vec_get_str"
  _fmpq_vec_get_str :: CLong -> Ptr CFmpq -> IO (CString)

-- | /_fmpq_vec_fprint/ /file/ /vec/ /len/ 
-- 
-- Prints the vector of given length to the stream @file@. The format is
-- the length followed by two spaces, then a space separated list of
-- coefficients. If the length is zero, only \(0\) is printed.
-- 
-- In case of success, returns a positive value. In case of failure,
-- returns a non-positive value.
foreign import ccall "fmpq_vec.h _fmpq_vec_fprint"
  _fmpq_vec_fprint :: Ptr CFile -> Ptr CFmpq -> CLong -> IO CInt

-- | /_fmpq_vec_print/ /vec/ /len/ 
-- 
-- Prints the vector of given length to @stdout@.
-- 
-- For further details, see @_fmpq_vec_fprint()@.
_fmpq_vec_print :: Ptr CFmpq -> CLong -> IO CInt
_fmpq_vec_print x n = printCStr (_fmpq_vec_get_str n) x

