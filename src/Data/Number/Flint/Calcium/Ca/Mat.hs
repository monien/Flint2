{-|
module      :  Data.Number.Flint.Calcium.Ca.Mat
copyright   :  (c) 2023 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de


-- A @CaMat@ represents a dense matrix over the real or complex numbers,
-- implemented as an array of entries of type @Ca@. The dimension
-- (number of rows and columns) of a matrix is fixed at initialization, and
-- the user must ensure that inputs and outputs to an operation have
-- compatible dimensions. The number of rows or columns in a matrix can be
-- zero.
--

-}
module Data.Number.Flint.Calcium.Ca.Mat (
  module Data.Number.Flint.Calcium.Ca.Mat.FFI
  ) where
  
import Data.Number.Flint.Calcium.Ca.Mat.FFI
