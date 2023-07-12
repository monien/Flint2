{- | See [Data.Number.Flint.Acb.Hypgeom]("Data.Number.Flint.Acb.Hypgeom")
for the general implementation of hypergeometric functions.

For convenience, this module provides versions of the same functions for
real variables represented using @Arb@ and @ArbPoly@. Most methods
are simple wrappers around the complex versions, but some of the
functions in this module have been further optimized specifically for
real variables.

This module also provides certain functions exclusive to real variables,
such as functions for computing real roots of common special functions.
-}
module Data.Number.Flint.Arb.Hypgeom (
  module Data.Number.Flint.Arb.Hypgeom.FFI
  ) where

import Data.Number.Flint.Arb.Hypgeom.FFI
