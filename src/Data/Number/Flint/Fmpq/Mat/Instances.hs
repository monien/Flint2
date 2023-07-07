{-# OPTIONS_HADDOCK hide, prune, ignore-exports #-}
module Data.Number.Flint.Fmpq.Mat.Instances where

import System.IO.Unsafe
import Foreign.C.String
import Foreign.Marshal.Alloc ( free )

import Data.Number.Flint.Fmpq.Mat

instance Show FmpqMat where
  show x = unsafePerformIO $ do
    (_, cs) <- withFmpqMat x fmpq_mat_get_str
    s <- peekCString cs
    free cs
    return s
      