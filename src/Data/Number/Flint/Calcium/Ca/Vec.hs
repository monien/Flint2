{-|
module      :  Data.Number.Flint.Calcium.Ca
copyright   :  (c) 2023 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de

A @CaVec@ represents a vector of real or complex numbers, implemented
as an array of coefficients of type @CCa@.

Most functions are provided in two versions: an underscore method
which operates directly on pre-allocated arrays of coefficients
(taking @Ptr CCa@ arguments), and a non-underscore method which
takes @CaVec@ input and performs automatic memory management.

Unlike @CaPoly@, a @CaVec@ is not normalised by removing zero
coefficients; it retains the exact length assigned by the user.
-}
module Data.Number.Flint.Calcium.Ca.Vec (
  module Data.Number.Flint.Calcium.Ca.Vec.FFI
  ) where
  
import GHC.Exts
import Data.Number.Flint.Calcium.Ca.Vec.FFI
