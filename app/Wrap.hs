module Wrap where

import System.IO.Unsafe
import Foreign.Ptr
import Foreign.C.Types
import Foreign.Marshal.Utils
import Foreign.Marshal.Alloc
import Foreign.Storable

import Data.Complex
import Data.Number.Flint.Arb.FpWrap

type CC = Complex CDouble

main = do
  let z = 0:+1 :: CC
  p <- new z
  r <- malloc :: IO (Ptr CC)
  flag <- arb_fpwrap_cdouble_exp r p 0
  print flag
  print z
  res <- peek r
  print res
  free r
  free p

airy :: Double -> Double
airy x = unsafePerformIO $ do
  r <- malloc :: IO (Ptr CDouble)
  flag <- arb_fpwrap_double_airy_ai r (realToFrac x) 0
  res <- peek r
  free r
  return $ realToFrac res