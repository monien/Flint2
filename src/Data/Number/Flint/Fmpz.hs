{- | 
module      : Data.Number.Flint.Fmpz
copyright   : (c) 2020 Hartmut Monien
license     : BSD-style (see LICENSE)
maintainer  : hmonien@uni-bonn.de

An @Fmpz@ represents an integer.
This module implements operations on integers.

== Basic usage 

@
import Data.Number.Flint

main = do 
  x <- newFmpz
  withFmpz x $ \\x -> do
    fmpz_set_ui x 7
    fmpz_mul x x x
    fmpz_print x
@

Running main yields:

>>> main 
49
-}

module Data.Number.Flint.Fmpz (
  module Data.Number.Flint.Fmpz.FFI
) where

import Data.Number.Flint.Fmpz.FFI