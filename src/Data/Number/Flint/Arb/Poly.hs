{- |
An @ArbPoly@ represents a polynomial over the real numbers,
implemented as an array of coefficients of type @arb_struct@.

Most functions are provided in two versions: an underscore method which
operates directly on pre-allocated arrays of coefficients and generally
has some restrictions (such as requiring the lengths to be nonzero and
not supporting aliasing of the input and output arrays), and a
non-underscore method which performs automatic memory management and
handles degenerate cases.
-}
module Data.Number.Flint.Arb.Poly (
  module Data.Number.Flint.Arb.Poly.FFI
  ) where

import Data.Number.Flint.Arb.Poly.FFI