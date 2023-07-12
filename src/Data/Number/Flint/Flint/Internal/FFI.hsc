
module Data.Number.Flint.Flint.Internal.FFI (
    Flint (..)
  , CFlint (..)
  , printCStr
  , printCVec
  , CFBitCnt
) where

import Foreign.C.String (CString (..), peekCString)
import Foreign.C.Types
import Foreign.Marshal.Alloc (free)
import Foreign.Marshal.Array (advancePtr)
import Foreign.ForeignPtr 
import Foreign.Ptr 
import Foreign.Storable

import Control.Monad
import Data.Word

#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpz_factor.h>

class Flint a where
  data CFlint a :: *

-- output ----------------------------------------------------------------------

printCStr :: (Ptr a -> IO CString) -> Ptr a -> IO CInt
printCStr f x = do
  cs <- f x
  s <- peekCString cs
  free cs
  putStr s
  return 1

printCVec :: Storable a => (Ptr a -> IO CInt) -> Ptr a -> CLong -> IO CInt
printCVec f vec len = do
  putStr $ show len ++ "  "
  forM_ [0..fromIntegral len - 1] $ \j -> do
    f (vec `advancePtr` j)
    putStr " "
  return 1

--------------------------------------------------------------------------------

type CFBitCnt = #type flint_bitcnt_t
