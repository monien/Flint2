{-# OPTIONS_HADDOCK hide, prune, ignore-exports #-}
module Data.Number.Flint.Groups.Qfb.Instances where

import System.IO.Unsafe
import Foreign.C.String
import Foreign.Marshal.Alloc ( free )

import Data.Number.Flint.Groups.Qfb

instance Show Qfb where
  show x = unsafePerformIO $ do
    (_, cs) <- withQfb x qfb_get_str
    s <- peekCString cs
    free cs
    return s

