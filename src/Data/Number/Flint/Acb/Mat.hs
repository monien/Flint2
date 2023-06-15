{- |
An @AcbMat@ represents a dense matrix over the complex numbers,
implemented as an array of entries of type @Acb@. The dimension
(number of rows and columns) of a matrix is fixed at initialization, and
the user must ensure that inputs and outputs to an operation have
compatible dimensions. The number of rows or columns in a matrix can be
zero.
-}

module Data.Number.Flint.Acb.Mat (
  module Data.Number.Flint.Acb.Mat.FFI
  ) where

import Data.Number.Flint.Acb.Mat.FFI