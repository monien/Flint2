{-|
module      :  Data.Number.Flint.Fmpz
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de

An @Fmpz@ represents an integer.
This module implements operations on integers.

== Example

__Warning__: Instances like `Show` and `Num` are only
avaible for some types without context.

@
import Data.Number.Flint

main = do 
  let x, y :: Fmpz
      x = 7
      y = 8
      z = x * y
  print z
  print $ factor z
@

Running main yields:

>>> main 
56
[(2,3),(7,1)]

== Using the @Flint@ library directly

@
import Data.Number.Flint

main = do 
  x <- newFmpz
  y <- newFmpz
  z <- newFmpz
  withFmpz x $ \\x -> do
    withFmpz y $ \\y -> do
      withFmpz z $ \\z -> do
        fmpz_set_ui x 7
        fmpz_set_ui y 8
        fmpz_mul z x y
        fmpz_print z
        fac <- newFmpzFactor
        withFmpzFactor fac $ \\fac -> do
           fmpz_factor fac z
           fmpz_factor_print fac
           putStr "\n"
@

Running main yields:

>>> main 
49


-}

module Data.Number.Flint.Fmpz (
    module Data.Number.Flint.Fmpz.FFI
) where

import Data.Number.Flint.Fmpz.FFI
