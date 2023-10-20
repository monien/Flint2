module Data.Number.Flint.Fmpz.Poly.Q.Instances (
    FmpzPolyQ (..)
) where

import Test.QuickCheck

import GHC.Exts

import System.IO.Unsafe
import Control.Monad

import Foreign.Ptr
import Foreign.C.String
import Foreign.Storable
import Foreign.Marshal.Alloc (free)
import Foreign.Marshal.Array (advancePtr)

import Data.Number.Flint.Quotient
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Instances
import Data.Number.Flint.Fmpz.Poly
import Data.Number.Flint.Fmpz.Poly.Factor
import Data.Number.Flint.Fmpz.Poly.Q

instance Show FmpzPolyQ where
  show p = snd $ unsafePerformIO $ do
    withFmpzPolyQ p $ \p -> do
      withCString "x" $ \x -> do
        cs <- fmpz_poly_q_get_str_pretty p x
        s <- peekCString cs
        free cs
        return s

instance Quotient FmpzPolyQ FmpzPoly where
  (//) x y = fst $ unsafePerformIO $ do
    withNewFmpzPolyQ $ \poly -> do
      withFmpzPoly x $ \x -> do
        withFmpzPoly y $ \y -> do
          CFmpzPolyQ p q <- peek poly
          fmpz_poly_set p x
          fmpz_poly_set q y
  numerator q = fst $ unsafePerformIO $ do
    withNewFmpzPoly $ \poly -> do 
      withFmpzPolyQ q $ \q -> do
        CFmpzPolyQ num _ <- peek q
        fmpz_poly_set poly num
  denominator q = fst $ unsafePerformIO $ do
    withNewFmpzPoly $ \poly -> do 
      withFmpzPolyQ q $ \q -> do
        CFmpzPolyQ _ den <- peek q
        fmpz_poly_set poly den

instance Num FmpzPolyQ where
  (*) = lift2 fmpz_poly_q_mul
  (+) = lift2 fmpz_poly_q_add
  (-) = lift2 fmpz_poly_q_sub
  abs = undefined
  signum = undefined
  fromInteger x = unsafePerformIO $ do
    result <- newFmpzPolyQ
    withFmpzPolyQ result $ \result -> 
      fmpz_poly_q_set_si result (fromIntegral x)
    return result

instance Eq FmpzPolyQ where
  (==) x y = snd $ snd $ unsafePerformIO $ do
    withFmpzPolyQ x $ \x ->
      withFmpzPolyQ y $ \y -> do
        f <- fmpz_poly_q_equal x y
        return $ f == 1

instance Ord FmpzPolyQ where
  compare = undefined
  
instance Real FmpzPolyQ where
  toRational = undefined

instance Enum FmpzPolyQ where
  toEnum = undefined
  fromEnum = undefined

lift2 f x y = unsafePerformIO $ do
  result <- newFmpzPolyQ
  withFmpzPolyQ result $ \result -> do
    withFmpzPolyQ x $ \x -> do
      withFmpzPolyQ y $ \y -> do
        f result x y
  return result

lift1 f x = unsafePerformIO $ do
  result <- newFmpzPolyQ
  withFmpzPolyQ result $ \result ->
    withFmpzPolyQ x $ \x ->
    f result x
  return result
