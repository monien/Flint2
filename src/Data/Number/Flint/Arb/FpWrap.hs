{- |
__Warning:__ This module is experimental (as of Arb 2.21). It has not
been extensively tested, and interfaces may change in the future.

This module provides wrappers of Arb functions intended users who want
accurate floating-point mathematical functions without necessarily
caring about ball arithmetic. The wrappers take floating-point input,
give floating-point output, and automatically increase the internal
working precision to ensure that the output is accurate (in the rare
case of failure, they output NaN along with an error code).

Outputs are passed by reference so that we can return status flags and
so that the interface is uniform for functions with multiple outputs.

The Haskell version of the c-functions require Ptr for the complex values.
The functions can be wrapped to a regular Haskell function 

@
import System.IO.Unsafe
import Foreign.Ptr
import Foreign.C.Types

import Data.Number.Flint.Arb.FpWrap

main = do
  print $ airy_ai  1
  print $ airy_ai' 1

airy_ai  = liftD arb_fpwrap_double_airy_ai
airy_ai' = liftD arb_fpwrap_double_airy_ai_prime

liftD :: (Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn)
       -> (Double -> Double)
liftD f x = unsafePerformIO $ do
  r <- malloc :: IO (Ptr CDouble)
  flag <- f r (realToFrac x) 0
  res <- peek r
  free r
  return $ realToFrac res
@

Running main yields:

>>> main

0.13529241631288141
-0.1591474412967932
-}
module Data.Number.Flint.Arb.FpWrap (
  module Data.Number.Flint.Arb.FpWrap.FFI
  ) where

import Data.Number.Flint.Arb.FpWrap.FFI