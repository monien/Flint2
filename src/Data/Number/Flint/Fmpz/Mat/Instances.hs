module Data.Number.Flint.Fmpz.Mat.Instances where

import System.IO.Unsafe
import Foreign.C.String
import Foreign.Marshal.Alloc ( free )

import Data.Number.Flint.Fmpz.Mat

instance Show FmpzMat where
  show x = unsafePerformIO $ do
    (_, cs) <- withFmpzMat x fmpz_mat_get_str_pretty
    s <- peekCString cs
    free cs
    return s
      