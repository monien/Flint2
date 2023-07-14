{-| 
module      :  Data.Number.Flint.UFD
copyright   :  (c) 2023 Hartmut Monien
license     :  BSD-style (see LICENSE)
maintainer  :  hmonien@uni-bonn.de
= Unique factorization domain

Specifically, a UFD is an integral domain (a nontrivial commutative ring in which the product of any two non-zero elements is non-zero) in which every non-zero non-unit element can be written as a product of prime elements (or irreducible elements), uniquely up to order and units.
-}
module Data.Number.Flint.UFD where

class (Num a) => UFD a where
  -- | factor /x/ 
  --
  -- factor /x/ into `prime` factors \(x = p_1^{e_1}\ldots p_n^{e_n}\) 
  -- with the representation \([(p_1, e_1) \ldots (p_n, e_n)]\)
  --
  factor :: a -> [(a, Int)]
  unfactor :: [(a, Int)] -> a
  unfactor x = product $ map (uncurry (^)) x
