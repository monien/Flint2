{-|
module      :  Data.Number.Flint.Groups.Bool.Mat
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de

A `BoolMat` represents a dense matrix over the boolean 
semiring \(\left<\{0,1\},\vee,\wedge\right>\),
implemented as an array of entries of type `CInt`.

The dimension (number of rows and columns) of a matrix is fixed at
initialization, and the user must ensure that inputs and outputs to an
operation have compatible dimensions. The number of rows or columns in
a matrix can be zero.

== Example

@
import Control.Monad

import Data.Number.Flint

main = do
  a <- newBoolMat 3 5
  withBoolMat a $ \\a -> do
    forM_ [0..2] $ \\j -> do
      bool_mat_set_entry a j j 1
      bool_mat_set_entry a j (j+2) 1
  print a
@

Running main yields:

>>> main 
[1, 0, 1, 0, 0]
[0, 1, 0, 1, 0]
[0, 0, 1, 0, 1]
-}

module Data.Number.Flint.Groups.Bool.Mat (
  module Data.Number.Flint.Groups.Bool.Mat.FFI
) where

import Data.Number.Flint.Groups.Bool.Mat.FFI

