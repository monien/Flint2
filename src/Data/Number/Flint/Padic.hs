{-|
module      :  Data.Number.Flint.Padic
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de

= p-adic numbers

A @Padic@ represents a p-adic number.
This module implements operations p-adic numbers.

== Basic usage 

Calculate a solution of \(x^2-2=0\) over \(\mathbb Q_7\) using default
precision (20 digits).

@
import Data.Number.Flint

main = do
  withNewPadicCtx 7 1 20 padic_series $ \\ctx -> 
    withNewPadic $ \\x -> do
      padic_set_ui x 2 ctx
      padic_sqrt x x ctx 
      padic_print x ctx
      putStr "\\n"
@

Running main yields:

>>> main 
3 + 1*7^1 + 2*7^2 + 6*7^3 + 1*7^4 + 2*7^5 + 1*7^6 + 2*7^7 + 4*7^8 + 6*7^9 + 6*7^10 + 2*7^11 + 1*7^12 + 1*7^13 + 2*7^15 + 1*7^16 + 1*7^17 + 4*7^18 + 6*7^19

== Introduction

The @Padic@ data type represents elements of \(\mathbb{Q}_p\) to
precision \(N\), stored in the form \(x = p^v u\) 
with \(u, v \in \mathbb{Z}\). Arithmetic operations can be carried out with
respect to a context containing the prime number \(p\) and various
pieces of pre-computed data.

Independent of the context, we consider a \(p\)-adic number x = u p^v to
be in canonical form whenever either p nmid u or \(u = v = 0\), and we
say it is reduced if, in addition, for non-zero \(u\), \(u \in (0, p^{N-v})\).

We briefly describe the interface:

The functions in this module expect arguments of type @Padic@, and
each variable carries its own precision. The functions have an interface
that is similar to the MPFR functions. In particular, they have the same
semantics, specified as follows: Compute the requested operation exactly
and then reduce the result to the precision of the output variable.
-}

module Data.Number.Flint.Padic (
  module Data.Number.Flint.Padic.FFI,
) where

import Data.Number.Flint.Padic.FFI

