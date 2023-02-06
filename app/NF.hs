{-# LANGUAGE 
    GADTs
  , ScopedTypeVariables
  , UndecidableInstances
  , DataKinds
  , TypeFamilies
  , TypeApplications
  , TypeOperators
  , PolyKinds
  , NoStarIsType #-}
  
module NF where

import GHC.TypeLits
import Data.Proxy

import System.IO.Unsafe
import Data.Number.Flint

import FmpzPoly
import FmpqPoly


main = do
  putStrLn "Numberfield with polynomial:"
  print $ polynomial (undefined :: F)
  let x = F (fromList [1,1])
  print $ x^12
  let a = x^5
      b = x^7
  print $ a * b
  print $ ctx (undefined :: GF 11)

instance NumberField F where
  polynomial _ = fromList [18,-19,-26,4,14,0,14,-30,24,-11,-11,1]

newtype F = F FmpzPoly deriving Show

instance Num F where
  (+) (F x) (F y) = F (x + y)
  (*) (F x) (F y) = F $ unsafePerformIO $ do
    result <- newFmpzPoly
    withFmpzPoly result $ \result -> do
      withFmpzPoly x $ \x ->
        withFmpzPoly y $ \ y ->
          withFmpzPoly (polynomial (undefined :: F)) $ \poly -> do
            fmpz_poly_mul result x y
            fmpz_poly_rem result result poly
    return result
  negate (F x) = F (negate x)
  fromInteger x = F (fromInteger x)
  abs = undefined
  signum = undefined
  
class (Num a) => NumberField a where
  polynomial :: a -> FmpzPoly

class FiniteField a where
  ctx :: a -> Integer
  
newtype GF (p :: Nat) = GF Integer

instance forall p. KnownNat p => FiniteField (GF p) where
  ctx _ = natVal (Proxy :: Proxy p)