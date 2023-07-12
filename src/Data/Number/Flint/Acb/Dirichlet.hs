{- |
This module allows working with values of Dirichlet characters,
Dirichlet L-functions, and related functions. A Dirichlet L-function is
the analytic continuation of an L-series

\[L(s,\chi) = \sum_{k=1}^\infty \frac{\chi(k)}{k^s}\]

where \(\chi(k)\) is a Dirichlet character. The trivial character chi(k)
= 1 gives the Riemann zeta function. Working with Dirichlet characters
is documented in [Dirichlet]("Data.Number.Flint.Groups.Dirichlet").

The code in other modules for computing the Riemann zeta function,
Hurwitz zeta function and polylogarithm will possibly be migrated to
this module in the future.
-}

module Data.Number.Flint.Acb.Dirichlet (
  module Data.Number.Flint.Acb.Dirichlet.FFI
  ) where

import Data.Number.Flint.Acb.Dirichlet.FFI
