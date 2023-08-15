module Data.Number.Flint.Groups.Bool.Mat.Instances where

import System.IO.Unsafe
import Foreign.C.String
import Foreign.Marshal.Alloc ( free )

import Data.Number.Flint.Groups.Bool.Mat

instance Show BoolMat where
  show x = unsafePerformIO $ do
    (_, cs) <- withBoolMat x bool_mat_get_str
    s <- peekCString cs
    free cs
    return s