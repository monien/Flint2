{- | 
module      : Data.Number.Flint.Arb.FFI
copyright   : (c) 2023 Hartmut Monien
license     : BSD-style (see LICENSE)
maintainer  : hmonien@uni-bonn.de

An @Arb@ represents a ball over the real numbers, that is, an interval
\([m \pm r] \equiv [m-r, m+r]\) where the midpoint \(m\) and the radius
\(r\) are (extended) real numbers and \(r\) is nonnegative (possibly
infinite). The result of an (approximate) operation done on @arb_t@
variables is a ball which contains the result of the (mathematically
exact) operation applied to any choice of points in the input balls. In
general, the output ball is not the smallest possible.

The precision parameter passed to each function roughly indicates the
precision to which calculations on the midpoint are carried out
(operations on the radius are always done using a fixed, small
precision.)

For arithmetic operations, the precision parameter currently simply
specifies the precision of the corresponding @arf_t@ operation. In the
future, the arithmetic might be made faster by incorporating sloppy
rounding (typically equivalent to a loss of 1-2 bits of effective
working precision) when the result is known to be inexact (while still
propagating errors rigorously, of course). Arithmetic operations done on
exact input with exactly representable output are always guaranteed to
produce exact output.

For more complex operations, the precision parameter indicates a minimum
working precision (algorithms might allocate extra internal precision to
attempt to produce an output accurate to the requested number of bits,
especially when the required precision can be estimated easily, but this
is not generally required).

If the precision is increased and the inputs either are exact or are
computed with increased accuracy as well, the output should converge
proportionally, absent any bugs. The general intended strategy for using
ball arithmetic is to add a few guard bits, and then repeat the
calculation as necessary with an exponentially increasing number of
guard bits (Ziv\'s strategy) until the result is exact enough for one\'s
purposes (typically the first attempt will be successful).

The following balls with an infinite or NaN component are permitted, and
may be returned as output from functions.

-}

module Data.Number.Flint.Arb (
  module Data.Number.Flint.Arb.FFI
  ) where

import Data.Number.Flint.Arb.FFI

