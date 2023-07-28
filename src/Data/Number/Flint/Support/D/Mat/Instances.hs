{-# OPTIONS_HADDOCK hide, prune, ignore-exports #-}
module Data.Number.Flint.Support.D.Mat.Instances where

import System.IO.Unsafe
import Foreign.C.String
import Foreign.Marshal.Alloc ( free )

import Data.Number.Flint.Support.D.Mat

instance Show DMat where
  show x = unsafePerformIO $ do
    (_, cs) <- withDMat x d_mat_get_str
    s <- peekCString cs
    free cs
    return s
      
