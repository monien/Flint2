{-|
module      :  Data.Number.Flint.Groups.Perm.FFI
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de
-}
module Data.Number.Flint.Groups.Perm.FFI (
  -- * Permutations
    _perm_init
  , _perm_clear
  -- * Assignment
  , _perm_set
  , _perm_set_one
  , _perm_inv
  -- * Composition
  , _perm_compose
  , _perm_power
  -- * Parity
  , _perm_parity
  -- * Randomisation
  , _perm_randtest
  -- * Input and output
  , _perm_print
  , _perm_print_pretty
  , _perm_fprint_pretty
  , _perm_get_str_pretty
  -- * Properties
  , _perm_order
) where 

-- permutations ----------------------------------------------------------------

import Control.Monad

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr )
import Foreign.Storable
import Foreign.Marshal ( free, peekArray )

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz

#include <flint/flint.h>
#include <flint/perm.h>

--------------------------------------------------------------------------------

-- | /_perm_init/ /n/ 
-- 
-- Initialises the permutation for use.
foreign import ccall "perm.h _perm_init"
  _perm_init :: CLong -> IO (Ptr CLong)

-- | /_perm_clear/ /vec/ 
-- 
-- Clears the permutation.
foreign import ccall "perm.h _perm_clear"
  _perm_clear :: Ptr CLong -> IO ()

-- Assignment ------------------------------------------------------------------

-- | /_perm_set/ /res/ /vec/ /n/ 
-- 
-- Sets the permutation @res@ to the same as the permutation @vec@.
foreign import ccall "perm.h _perm_set"
  _perm_set :: Ptr CLong -> Ptr CLong -> CLong -> IO ()

-- | /_perm_set_one/ /vec/ /n/ 
-- 
-- Sets the permutation to the identity permutation.
foreign import ccall "perm.h _perm_set_one"
  _perm_set_one :: Ptr CLong -> CLong -> IO ()

-- | /_perm_inv/ /res/ /vec/ /n/ 
-- 
-- Sets @res@ to the inverse permutation of @vec@. Allows aliasing of @res@
-- and @vec@.
foreign import ccall "perm.h _perm_inv"
  _perm_inv :: Ptr CLong -> Ptr CLong -> CLong -> IO ()

-- Composition -----------------------------------------------------------------

-- | /_perm_compose/ /res/ /vec1/ /vec2/ /n/ 
-- 
-- Forms the composition \(\pi_1 \circ \pi_2\) of two permutations
-- \(\pi_1\) and \(\pi_2\). Here, \(\pi_2\) is applied first, that is,
-- \((\pi_1 \circ \pi_2)(i) = \pi_1(\pi_2(i))\).
-- 
-- Allows aliasing of @res@, @vec1@ and @vec2@.
foreign import ccall "perm.h _perm_compose"
  _perm_compose :: Ptr CLong -> Ptr CLong -> Ptr CLong -> CLong -> IO ()

foreign import ccall "perm.h _perm_power"
  _perm_power :: Ptr CLong -> Ptr CLong -> CLong -> CLong -> IO ()

-- Parity ----------------------------------------------------------------------

-- | /_perm_parity/ /vec/ /n/ 
-- 
-- Returns the parity of @vec@, 0 if the permutation is even and 1 if the
-- permutation is odd.
foreign import ccall "perm.h _perm_parity"
  _perm_parity :: Ptr CLong -> CLong -> IO CInt

foreign import ccall "perm.h _perm_order"
  _perm_order :: Ptr CFmpz -> Ptr CLong -> CLong -> IO ()

-- Randomisation ---------------------------------------------------------------

-- | /_perm_randtest/ /vec/ /n/ /state/ 
-- 
-- Generates a random permutation vector of length \(n\) and returns its
-- parity, 0 or 1.
-- 
-- This function uses the Knuth shuffle algorithm to generate a uniformly
-- random permutation without retries.
foreign import ccall "perm.h _perm_randtest"
  _perm_randtest :: Ptr CLong -> CLong -> Ptr CFRandState -> IO CInt

-- Input and output ------------------------------------------------------------

-- | /_perm_print/ /vec/ /n/ 
-- 
-- Prints the permutation vector of length \(n\) to @stdout@.
_perm_print :: Ptr CLong -> CLong -> IO CInt
_perm_print p n = do
  a <- peekArray (fromIntegral n) p
  putStr $ show n ++ " "
  forM_ a $ \x -> putStr $ " " ++ show x
  return 1

-- | /_perm_get_str_pretty/ /vec/ /n/ 
--
-- Return a string representation of permutation vector of length \(n\)
-- in cycle representation.
foreign import ccall "perm.h _perm_get_str_pretty"
  _perm_get_str_pretty :: Ptr CLong -> CLong -> IO CString


-- | /_perm_print_pretty/ /vec/ /n/ 
--
-- Prints permutation vector of length \(n\) in cycle representation
-- to @stdout@.
_perm_print_pretty :: Ptr CLong -> CLong -> IO CInt
_perm_print_pretty p n = printCStr (flip _perm_get_str_pretty n) p

-- | /_perm_fprint_pretty/ /vec/ /n/ 
--
-- Prints permutation vector of length \(n\) in cycle representation
-- to @file@.
foreign import ccall "perm.h _perm_fprint_pretty"
  _perm_fprint_pretty :: Ptr CFile -> Ptr CLong -> CLong -> IO ()
