{- |
module      : Data.Number.Flint.DLog
copyright   :  (c) 2023 Hartmut Monien
license     :  BSD-style (see LICENSE)
maintainer  : hmonien@uni-bonn.de

-- This module implements discrete logarithms, with the application to
Dirichlet characters in mind.

In particular, this module defines a @dlog_precomp_t@ structure
permitting to describe a discrete log problem in some subgroup of
\((\mathbb Z/p^e \mathbb Z)^\times\) for primepower moduli \(p^e\), and
store precomputed data for faster computation of several such discrete
logarithms.

When initializing this data, the user provides both a group description
and the expected number of subsequent discrete logarithms calls. The
choice of algorithm and the amount of stored data depend both on the
structure of the group and this number.

No particular effort has been made towards single discrete logarithm
computation. Currently only machine size primepower moduli are
supported.

-}

module Data.Number.Flint.Groups.DLog (
  module Data.Number.Flint.Groups.DLog.FFI,
) where

import Data.Number.Flint.Groups.DLog.FFI

