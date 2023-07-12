{- |
This module provides methods for FLINT polynomials with integer and
rational coefficients (@FmpzPoly@) and (@FmpqPoly@) requiring use
of Arb real or complex numbers.

Some methods output real or complex numbers while others use real and
complex numbers internally to produce an exact result. This module also
contains some useful helper functions not specifically related to real
and complex numbers.

Note that methods that combine Arb /polynomials/ and FLINT polynomials
are found in the respective Arb polynomial modules, such as
@arb_poly_set_fmpz_poly@ and @arb_poly_get_unique_fmpz_poly@.

-}
module Data.Number.Flint.Arb.Fmpz.Poly (
  module Data.Number.Flint.Arb.Fmpz.Poly.FFI
  ) where

import Data.Number.Flint.Arb.Fmpz.Poly.FFI
