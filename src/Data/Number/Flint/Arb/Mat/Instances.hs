{-# OPTIONS_HADDOCK hide, prune, ignore-exports #-}
module Data.Number.Flint.Arb.Mat.Instances where

import System.IO.Unsafe

import Foreign.C.String
import Foreign.Marshal.Alloc ( free )
import Foreign.Storable

import Data.Number.Flint.Arb
import Data.Number.Flint.Arb.Mat

instance Show ArbMat where
  show x = unsafePerformIO $ do
    (_, cs) <- withArbMat x $ \x -> do arb_mat_get_strn x 16 arb_str_no_radius
    s <- peekCString cs
    free cs
    return s
      
