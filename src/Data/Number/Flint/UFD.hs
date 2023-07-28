{-|
module      :  Data.Number.Flint.UFD
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de

= Unique factorization domain

Specifically, a UFD is an integral domain (a nontrivial commutative ring in which the product of any two non-zero elements is non-zero) in which every non-zero non-unit element can be written as a product of prime elements (or irreducible elements), uniquely up to order and units.
-}
module Data.Number.Flint.UFD where

class (Num a) => UFD a where
  -- | factor /x/ 
  --
  -- Factor /x/ into `prime` factors \(x = p_1^{e_1}\ldots p_n^{e_n}\) 
  -- with the representation \([(p_1, e_1) \ldots (p_n, e_n)]\)
  --
  factor :: a -> [(a, Int)]
  -- | unfactor /f/
  --
  -- Find /x/ which has the unique factorization /f/.
  unfactor :: [(a, Int)] -> a
  unfactor x = product $ map (uncurry (^)) x
