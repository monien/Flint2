module Data.Number.Flint.Acb.Mat.Instances where

import System.IO.Unsafe
import Foreign.C.String
import Foreign.Marshal.Alloc ( free )

import Data.Number.Flint.Acb.Mat

instance Show AcbMat where
  show x = unsafePerformIO $ do
    (_, cs) <- withAcbMat x $ \x -> do acb_mat_get_strd x 16
    s <- peekCString cs
    free cs
    return s
