{-|
module      :  Data.Number.Flint.Fmpz.MPoly.Q
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de


An @FmpzMPolyQ@ represents an element of :math:`\mathbb{Q}(x_1,ldots,x_n)`
for fixed /n/ as a pair of Flint multivariate polynomials
(@FmpzMPolyQ@). Instances are always kept in canonical form by
ensuring that the GCD of numerator and denominator is 1 and that the
coefficient of the leading term of the denominator is positive.

The user must create a multivariate polynomial context
(@FmpzMPolyCtx@) specifying the number of variables /n/ and the
monomial ordering.

-}
module Data.Number.Flint.Fmpz.MPoly.Q (
  module Data.Number.Flint.Fmpz.MPoly.Q.FFI
  ) where

import Data.Number.Flint.Fmpz.MPoly.Q.FFI
