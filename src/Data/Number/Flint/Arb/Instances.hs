module Data.Number.Flint.Arb.Instances (
  Arb (..)
) where

import Test.QuickCheck

import System.IO.Unsafe
import Foreign.C.String
import Foreign.Marshal.Alloc ( free )

import Data.Char
import Data.Number.Flint.Arb

instance Show Arb where
  show x = unsafePerformIO $ do
    (_, cs) <- withArb x $ \x -> arb_get_str x 16 arb_str_no_radius
    s <- peekCString cs
    free cs
    return s

  