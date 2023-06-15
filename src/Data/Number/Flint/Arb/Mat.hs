{- |
An @ArbMat@ represents a dense matrix over the real numbers,
implemented as an array of entries of type @arb_struct@. The dimension
(number of rows and columns) of a matrix is fixed at initialization, and
the user must ensure that inputs and outputs to an operation have
compatible dimensions. The number of rows or columns in a matrix can be
zero.
-}
module Data.Number.Flint.Arb.Mat (
  module Data.Number.Flint.Arb.Mat.FFI
  ) where

import Data.Number.Flint.Arb.Mat.FFI