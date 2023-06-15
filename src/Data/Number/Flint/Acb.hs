{- | 
module      : Data.Number.Flint.Acb.FFI
copyright   : (c) 2023 Hartmut Monien
license     : BSD-style (see LICENSE)
maintainer  : hmonien@uni-bonn.de


An @Acb@ represents a complex number with error bounds. An @Arb@
consists of a pair of real number balls of type @Arb@,
representing the real and imaginary part with separate error bounds.

An @Acb@ thus represents a 
rectangle \([m_1-r_1, m_1+r_1] + [m_2-r_2, m_2+r_2] i\) in the complex plane. 
This is used instead of a disk or
square representation (consisting of a complex floating-point midpoint
with a single radius), since it allows implementing many operations more
conveniently by splitting into ball operations on the real and imaginary
parts. It also allows tracking when complex numbers have an exact (for
example exactly zero) real part and an inexact imaginary part, or vice
versa.

The interface for the @Acb@ type is slightly less developed than that
for the @Arb@ type. In many cases, the user can easily perform missing
operations by directly manipulating the real and imaginary parts.

-}

module Data.Number.Flint.Acb (
  module Data.Number.Flint.Acb.FFI
  ) where

import Data.Number.Flint.Acb.FFI

