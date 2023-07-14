{-|
module      :  Data.Number.Flint.Bernoulli
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de

This module provides helper functions for exact or approximate
calculation of the Bernoulli numbers, which are defined by the
exponential generating function

\[\frac{x}{e^x-1} = \sum_{n=0}^{\infty} B_n \frac{x^n}{n!}.\]

Efficient algorithms are implemented for both multi-evaluation and
calculation of isolated Bernoulli numbers. A global (or thread-local)
cache is also provided, to support fast repeated evaluation of various
special functions that depend on the Bernoulli numbers (including the
gamma function and the Riemann zeta function).
-}

module Data.Number.Flint.Bernoulli (
    module Data.Number.Flint.Bernoulli.FFI
) where

import Data.Number.Flint.Bernoulli.FFI

