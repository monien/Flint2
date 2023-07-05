{- |
This module provides wrappers of Arb functions intended users who want
accurate floating-point mathematical functions without necessarily
caring about ball arithmetic. The wrappers take floating-point input,
give floating-point output, and automatically increase the internal
working precision to ensure that the output is accurate (in the rare
case of failure, they output NaN along with an error code).

Outputs are passed by reference so that we can return status flags and
so that the interface is uniform for functions with multiple outputs.

__Warning:__ This module is experimental (as of Arb 2.21). It has not
been extensively tested, and interfaces may change in the future.
-}
module Data.Number.Flint.Arb.FpWrap (
  module Data.Number.Flint.Arb.FpWrap.FFI
  ) where

import Data.Number.Flint.Arb.FpWrap.FFI