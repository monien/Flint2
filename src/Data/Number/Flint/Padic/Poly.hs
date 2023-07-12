{- | 
module      : Data.Number.Flint.Padic.Poly
copyright   :  (c) 2023 Hartmut Monien
license     :  BSD-style (see LICENSE)
maintainer  : hmonien@uni-bonn.de

= Polynomials over p-adics

  We represent a polynomial
  in \(\mathbb{Q}_p[x]\) as a product \(p^v f(x)\), where \(p\) is a
  prime number, \(v \in \mathbb{Z}\) and \(f(x) \in \mathbb{Z}[x]\). As a
  data structure, we call this polynomial /normalised/ if the
  polynomial \(f(x)\) is /normalised/, that is, if the top
  coefficient is non-zero. We say this polynomial is in 
  /canonical form/ if one of the coefficients of \(f(x)\) is a \(p\)-adic
  unit. If \(f(x)\) is the zero polynomial, we require that \(v =
  0\). We say this polynomial is /reduced/ modulo \(p^N\) if it is
  canonical form and if all coefficients lie in the range \([0, p^N)\).
-}

module Data.Number.Flint.Padic.Poly (
  module Data.Number.Flint.Padic.Poly.FFI,
) where

import Data.Number.Flint.Padic.Poly.FFI
