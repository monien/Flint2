{-|
module      :  Data.Number.Flint.Quotient
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de

== Quotients
-}

module Data.Number.Flint.Quotient where

class Quotient a b | a -> b where
  -- | /x/ \/\/ /y/
  --
  -- Construct an /quotient/ from numerator /x/ and denominator /y/.
  (//) :: b -> b -> a
  -- | /numerator/ /x/
  --
  -- Return the numerator of /x/
  numerator   :: a -> b
  -- | /denominator/ /x/
  --
  -- Return the denominator of /x/
  denominator :: a -> b

infixl 7 //
