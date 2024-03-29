{-|
module      :  Data.Number.Flint.Fmpz.Poly.Instances
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de
-}
module Data.Number.Flint.Fmpz.Poly.Instances (
    FmpzPoly (..)
  , module GHC.Exts
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
import Text.ParserCombinators.ReadP

import Data.Bits
import Data.Char

import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Instances
import Data.Number.Flint.Fmpz.Poly
import Data.Number.Flint.Fmpz.Poly.Factor

import Data.Number.Flint.UFD

instance Show FmpzPoly where
  show p = snd $ unsafePerformIO $ do
    withFmpzPoly p $ \p -> do
      withCString "x" $ \x -> do
        cs <- fmpz_poly_get_str_pretty p x
        s <- peekCString cs
        free cs
        return s

instance Read FmpzPoly where
  readsPrec _ = readP_to_S parseFmpzPoly

instance Num FmpzPoly where
  (*) = lift2 fmpz_poly_mul
  (+) = lift2 fmpz_poly_add
  (-) = lift2 fmpz_poly_sub
  abs = undefined
  signum = undefined
  fromInteger x = unsafePerformIO $ do
    let tmp = fromInteger x :: Fmpz
    result <- newFmpzPoly
    withFmpzPoly result $ \result -> 
      withFmpz tmp $ \tmp -> do
      fmpz_poly_set_fmpz result tmp
      return result
    return result

instance Semigroup FmpzPoly where
  (<>) = lift2 fmpz_poly_compose

instance Eq FmpzPoly where
  (==) x y = snd $ snd $ unsafePerformIO $ do
    withFmpzPoly x $ \x ->
      withFmpzPoly y $ \y -> do
        f <- fmpz_poly_equal x y
        return $ f == 1

instance Ord FmpzPoly where
  compare = undefined
  
instance Real FmpzPoly where
  toRational = undefined

instance Enum FmpzPoly where
  toEnum = undefined
  fromEnum = undefined
  
instance Integral FmpzPoly where
  toInteger = undefined
  div x y = unsafePerformIO $ do
    p <- newFmpzPoly
    q <- newFmpzPoly
    withFmpzPoly x $ \x ->
      withFmpzPoly y $ \y ->
        withFmpzPoly q $ \q ->
          fmpz_poly_div q x y
    return q
  quotRem x y = unsafePerformIO $ do
    p <- newFmpzPoly
    q <- newFmpzPoly
    withFmpzPoly x $ \x ->
      withFmpzPoly y $ \y ->
        withFmpzPoly p $ \p ->
          withFmpzPoly q $ \q ->
            fmpz_poly_divrem p q x y
    return (p, q)

instance UFD FmpzPoly where
  factor x = snd $ snd $ unsafePerformIO $ do
    withFmpzPoly x $ \x -> do
      f <- newFmpzPolyFactor
      withFmpzPolyFactor f $ \f -> do
        fmpz_poly_factor f x
        CFmpzPolyFactor c d e n alloc <- peek f
        prefactor <- newFmpz
        withFmpz prefactor $ \prefactor -> fmpz_set prefactor c 
        let pre = (fromList [prefactor] :: FmpzPoly, 1)
        fac <- forM [0..fromIntegral n-1] $ \j -> do
          m <- peek (e `advancePtr` j)
          r <- newFmpzPoly
          withFmpzPoly r $ \r -> fmpz_poly_set r (d `advancePtr` j)
          return (r, fromIntegral m)
        return $ if prefactor == 1 then fac else pre : fac
        
instance Arbitrary FmpzPoly where
  arbitrary = do
    c <- listOf arbitrary
    return $ fromList (c ++ [1])

instance IsList FmpzPoly where
  type Item FmpzPoly = Fmpz
  fromList c = unsafePerformIO $ do
    p <- newFmpzPoly
    withFmpzPoly p $ \p -> 
      forM_ [0..length c-1] $ \j ->
        withFmpz (c!!j) $ \a -> 
          fmpz_poly_set_coeff_fmpz p (fromIntegral j) a
    return p
  toList p = snd $ unsafePerformIO $ 
    withFmpzPoly p $ \p -> do
      d <- fmpz_poly_degree p
      forM [0..d] $ \j -> do
        c <- newFmpz
        withFmpz c $ \c -> fmpz_poly_get_coeff_fmpz c p j
        return c

lift2 f x y = unsafePerformIO $ do
  result <- newFmpzPoly
  withFmpzPoly result $ \result -> do
    withFmpzPoly x $ \x -> do
      withFmpzPoly y $ \y -> do
        f result x y
  return result

lift1 f x = unsafePerformIO $ do
  result <- newFmpzPoly
  withFmpzPoly result $ \result ->
    withFmpzPoly x $ \x ->
    f result x
  return result

parseFmpzPoly :: ReadP FmpzPoly
parseFmpzPoly = do
  n <- parseItemNumber
  v <- count n parseItem 
  return $ fromList v
  where
    parseItemNumber = read <$> munch1 isNumber <* char ' '
    parseItem = read <$> (char ' ' *> parseFmpz)
    parseFmpz = do
      s <- munch (\x -> x == '+' || x == '-')
      skipSpaces
      d <- munch1 isNumber
      return $ s ++ d
  
