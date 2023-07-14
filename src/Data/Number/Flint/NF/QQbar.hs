{-|
module      :  Data.Number.Flint.NF.QQbar
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de

= Algebraic numbers

A @QQbar@ represents a real or complex algebraic number 
(an element of \(\overline{\mathbb{Q}}\)) by its unique reduced 
minimal polynomial in \(\mathbb{Z}[x]\) and an isolating complex interval. 
The precision of isolating intervals is maintained automatically to ensure 
that all operations on @QQbar@ instances are exact.

This representation is useful for working with individual algebraic
numbers of moderate degree (up to 100, say). Arithmetic in this
representation is expensive: an arithmetic operation on numbers of
degrees /m/ and /n/ involves computing and then factoring an
annihilating polynomial of degree /mn/ and potentially also performing
numerical root-finding. For doing repeated arithmetic, it is generally
more efficient to work with the @CA@ type in a fixed number field. The
@QQbar@ type is used internally by the @CA@ type to represent the
embedding of number fields in \(\mathbb{R}\) or \(\mathbb{C}\) and to decide
predicates for algebraic numbers.
-}
module Data.Number.Flint.NF.QQbar (
  module Data.Number.Flint.NF.QQbar.FFI,
) where

import Data.Number.Flint.NF.QQbar.FFI

