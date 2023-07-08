{-# OPTIONS_HADDOCK hide, prune, ignore-exports #-}
module Data.Number.Flint.Acb.Instances where

import System.IO.Unsafe
import Foreign.C.String
import Foreign.Marshal.Alloc ( free )

import Data.Number.Flint.Arb
import Data.Number.Flint.Acb

instance Show Acb where
  show x = unsafePerformIO $ do
    (_, cs) <- withAcb x $ \x -> acb_get_strn x 16 arb_str_no_radius
    s <- peekCString cs
    free cs
    return s

