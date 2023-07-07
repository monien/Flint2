module Data.Number.Flint.Arb.Mat.Instances where

import System.IO.Unsafe
import Foreign.C.String
import Foreign.Marshal.Alloc ( free )

import Data.Number.Flint.Arb.Mat

instance Show ArbMat where
  show x = unsafePerformIO $ do
    (_, cs) <- withArbMat x $ \x -> do arb_mat_get_strd x 16
    s <- peekCString cs
    free cs
    return s
      