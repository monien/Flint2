{- | 
module      :  Data.Number.Flint.Fmpz.Mat
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de

An @FmpzMat@ represents an matrix over integer.
This module implements operations on matrices over integers.

== Basic usage 

Create a 3x3 matrix over integers, set it to the unit matrix and print it.

@
import Data.Number.Flint

main = do
  withNewFmpzMat 3 2 $ \\a -> do
    fmpz_mat_one a
    fmpz_mat_print a
    putStr "\\n"
@

Running main yields:

>>> main 
3 3  1 0 0 0 1 0 0 0 1
-}

module Data.Number.Flint.Fmpz.Mat (
  module Data.Number.Flint.Fmpz.Mat.FFI,
) where

import Data.Number.Flint.Fmpz.Mat.FFI
