{- | 
module      : Data.Number.Flint.Fmpz
copyright   : (c) 2020 Hartmut Monien
license     : BSD-style (see LICENSE)
maintainer  : hmonien@uni-bonn.de

An @Fmpz@ represents an integer.
This module implements operations on integers.

== Basic usage 

__Warning__: Instances like `Show` and `Num` are only
avaible for some types without context.

@
import Data.Number.Flint

main = do 
  let x = 7 :: Fmpz
  print $ x*x
@

Running main yields:

>>> main 
49

== Using the @Flint@ library directly

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
