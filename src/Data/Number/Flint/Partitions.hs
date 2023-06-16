{- |
This module implements the asymptotically fast algorithm for evaluating
the integer partition function \(p(n)\) described in < [Joh2012]>. The
idea is to evaluate a truncation of the Hardy-Ramanujan-Rademacher
series using tight precision estimates, and symbolically factoring the
occurring exponential sums.

An implementation based on floating-point arithmetic can also be found
in FLINT. That version relies on some numerical subroutines that have
not been proved correct.

The implementation provided here uses ball arithmetic throughout to
guarantee a correct error bound for the numerical approximation 
of \(p(n)\). Optionally, hardware double arithmetic can be used for
low-precision terms. This gives a significant speedup for 
small (e.g.\(n < 10^6\)).
-}
module Data.Number.Flint.Partitions (
    module Data.Number.Flint.Partitions.FFI
) where

import Data.Number.Flint.Partitions.FFI

