{- | 
module      : Data.Number.Flint.Fmpz.Poly
copyright   : (c) 2020 Hartmut Monien
license     : BSD-style (see LICENSE)
maintainer  : hmonien@uni-bonn.de

An `FmpzPoly` represents an element of \(\mathbb{Z}[x]\).
This module implements operations on univariate polynomials over the integers.

== Example

__Warning__: Instances like `Show`, `Num` and `IsList` are only
avaible for some types.

@
import Data.Number.Flint

main = do 
  let poly = fromList [35,24,16,4,1] :: FmpzPoly
  print poly
  mapM_ print $ factor poly
@

Running main yields:

>>> main 
x^4+4*x^3+16*x^2+24*x+35
(x^2+2*x+7,1)
(x^2+2*x+5,1)
-}
module Data.Number.Flint.Fmpz.Poly (
  module Data.Number.Flint.Fmpz.Poly.FFI
  ) where
  
import GHC.Exts
import Data.Number.Flint.Fmpz.Poly.FFI
