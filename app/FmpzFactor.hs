module FmpzFactor where

import System.IO.Unsafe

import Foreign.Storable
import Foreign.C.Types
import Foreign.C.String
import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.Marshal.Alloc

import Data.Number.Flint

instance Show FmpzFactor where
  show x = snd $ unsafePerformIO $ do
    let base = 10 :: CInt
    withFmpzFactor x $ \x -> do
      cString <- fmpz_factor_get_str x
      result <- peekCString cString
      free cString
      return result
