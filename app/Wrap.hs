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
  print $ cexp z
  print $ airy_ai  1
  print $ airy_ai' 1

cexp =  liftC1 arb_fpwrap_cdouble_exp
airy_ai  = liftD1 arb_fpwrap_double_airy_ai
airy_ai' = liftD1 arb_fpwrap_double_airy_ai_prime

liftD1 :: (Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn)
       -> (Double -> Double)
liftD1 f x = unsafePerformIO $ do
  r <- malloc :: IO (Ptr CDouble)
  flag <- f r (realToFrac x) 0
  res <- peek r
  free r
  return $ realToFrac res

liftC1 :: (Ptr CC -> Ptr CC -> CInt -> IO FpWrapReturn)
       -> (CC -> CC)
liftC1 f z = unsafePerformIO $ do
  r <- malloc :: IO (Ptr CC)
  p <- new z
  flag <- f r p 0
  res <- peek r
  free r
  free p
  return $ res