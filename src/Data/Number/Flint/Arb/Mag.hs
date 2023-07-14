{-|
module      :  Data.Number.Flint.Arb.Mag
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de


The @mag_t@ type holds an unsigned floating-point number with a
fixed-precision mantissa (30 bits) and an arbitrary-precision exponent
(represented as an @fmpz_t@), suited for representing magnitude bounds.
The special values zero and positive infinity are supported, but not
NaN.

Operations that involve rounding will always produce a valid upper
bound, or a lower bound if the function name has the suffix /lower/. For
performance reasons, no attempt is made to compute the best possible
bounds: in general, a bound may be several ulps larger\/smaller than the
optimal bound. Some functions such as @mag_set@ and @mag_mul_2exp_si@
are always exact and therefore do not require separate /lower/ versions.
--
A common mistake is to forget computing a lower bound for the argument
of a decreasing function that is meant to be bounded from above, or vice
versa. For example, to compute an upper bound for \((x+1)/(y+1)\), the
parameter /x/ should initially be an upper bound while /y/ should be a
lower bound, and one should do:

For a lower bound of the same expression, /x/ should be a lower bound
while /y/ should be an upper bound, and one should do:

Applications requiring floating-point arithmetic with more flexibility
(such as correct rounding, or higher precision) should use the @arf_t@
type instead. For calculations where a complex alternation between upper
and lower bounds is necessary, it may be cleaner to use @arb_t@
arithmetic and convert to a @mag_t@ bound only in the end.
-}

module Data.Number.Flint.Arb.Mag (
  module Data.Number.Flint.Arb.Mag.FFI
  ) where

import Data.Number.Flint.Arb.Mag.FFI
