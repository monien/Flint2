{- | 
module      : Data.Number.Flint.Padic
copyright   :  (c) 2023 Hartmut Monien
license     :  BSD-style (see LICENSE)
maintainer  : hmonien@uni-bonn.de

= P-adic numbers

A @Padic@ represents a p-adic number.
This module implements operations p-adic numbers.

== Basic usage 

Calculate a solution of \(x^2-2=0\) over \(\mathbb Q_7\) using default
precision (20 digits).

@
import Data.Number.Flint

main = do
  p <- newFmpz
  withFmpz p $ \\p ->
    fmpz_set_ui p 7
  withNewPadicCtx p 1 20 padic_series $ \\ctx -> 
    withNewPadic $ \\x -> do
      padic_set_si x 2 ctx
      padic_sqrt x x ctx 
      padic_print x ctx
      putStr "\\n"
@

Running main yields:

>>> main 
3 + 1*7^1 + 2*7^2 + 6*7^3 + 1*7^4 + 2*7^5 + 1*7^6 + 2*7^7 + 4*7^8 + 6*7^9 + 6*7^10 + 2*7^11 + 1*7^12 + 1*7^13 + 2*7^15 + 1*7^16 + 1*7^17 + 4*7^18 + 6*7^19
-}

module Data.Number.Flint.Padic (
  module Data.Number.Flint.Padic.FFI,
) where

import Data.Number.Flint.Padic.FFI

