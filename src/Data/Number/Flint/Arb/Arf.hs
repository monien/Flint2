{-|
module      :  Data.Number.Flint.Arb.Arf
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de

A variable of type @Arf@ holds an arbitrary-precision binary
floating-point number: that is, a rational number of the form \(x c\dot 2^y\)
where \(x, y \in \mathbb{Z}\) and \(x\) is odd, or one of the special
values zero, plus infinity, minus infinity, or NaN (not-a-number). There
is currently no support for negative zero, unsigned infinity, or a NaN
with a payload.

The /exponent/ of a finite and nonzero floating-point number can be
defined in different ways: for example, as the component /y/ above, or
as the unique integer /e/ such that \(x cdot 2^y = m cdot 2^e\) 
where \(0.5 \le |m| < 1\). The internal representation of an @Arf@ stores
the exponent in the latter format.
-}

module Data.Number.Flint.Arb.Arf (
  module Data.Number.Flint.Arb.Arf.FFI
  ) where

import Data.Number.Flint.Arb.Arf.FFI

