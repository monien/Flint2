{-# OPTIONS_HADDOCK hide, prune, ignore-exports #-}
{-# language TypeFamilies #-}
module Data.Number.Flint.NMod.Poly.Instances (
    NModPoly (..)
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

import Data.Number.Flint.NMod.Poly
import Data.Number.Flint.NMod.Poly.Factor

import Data.Number.Flint.UFD

instance Show NModPoly where
  show p = snd $ unsafePerformIO $ do
    withNModPoly p $ \p -> do
      withCString "x" $ \x -> do
        cs <- nmod_poly_get_str_pretty p x
        s <- peekCString cs
        free cs
        return s

instance Num NModPoly where
  (*) = lift2 nmod_poly_mul
  (+) = lift2 nmod_poly_add
  (-) = lift2 nmod_poly_sub
  abs = undefined
  signum = undefined
  fromInteger = undefined
  
instance Semigroup NModPoly where
  (<>) = lift2 nmod_poly_compose

instance Eq NModPoly where
  (==) x y = snd $ snd $ unsafePerformIO $ do
    withNModPoly x $ \x ->
      withNModPoly y $ \y -> do
        f <- nmod_poly_equal x y
        return $ f == 1

instance Ord NModPoly where
  compare = undefined
  
instance Real NModPoly where
  toRational = undefined

instance Enum NModPoly where
  toEnum = undefined
  fromEnum = undefined
  
instance Integral NModPoly where
  toInteger = undefined
  div x y = unsafePerformIO $ do
    (_, n) <- withNModPoly x nmod_poly_modulus
    (_, m) <- withNModPoly y nmod_poly_modulus
    when (n /= m) $ error "modulus does not agree."
    p <- newNModPoly n
    q <- newNModPoly n
    withNModPoly x $ \x ->
      withNModPoly y $ \y ->
        withNModPoly q $ \q ->
          nmod_poly_div q x y
    return q
  quotRem x y = unsafePerformIO $ do
    (_, n) <- withNModPoly x nmod_poly_modulus
    (_, m) <- withNModPoly y nmod_poly_modulus
    when (n /= m) $ error "modulus does not agree."
    p <- newNModPoly n 
    q <- newNModPoly n
    withNModPoly x $ \x ->
      withNModPoly y $ \y ->
        withNModPoly p $ \p ->
          withNModPoly q $ \q ->
            nmod_poly_divrem p q x y
    return (p, q)

instance UFD NModPoly where
  factor x = snd $ snd $ unsafePerformIO $ do
    withNModPoly x $ \x -> do
      m <- nmod_poly_modulus x
      f <- newNModPolyFactor
      withNModPolyFactor f $ \f -> do
        nmod_poly_factor f x
        (CNModPolyFactor d e n alloc) <- peek f
        forM [0..fromIntegral n-1] $ \j -> do
          m <- peek (e `advancePtr` j)
          r <- newNModPoly (fromIntegral m)
          withNModPoly r $ \r -> nmod_poly_set r (d `advancePtr` j)
          return (r, fromIntegral m)

lift2 f x y = unsafePerformIO $ do
  (_, n) <- withNModPoly x nmod_poly_modulus
  (_, m) <- withNModPoly y nmod_poly_modulus
  when (n /= m) $ error "modulus does not agree."
  result <- newNModPoly n
  withNModPoly result $ \result -> do
    withNModPoly x $ \x -> do
      withNModPoly y $ \y -> do
        f result x y
  return result

lift1 f x = unsafePerformIO $ do
  (_, n) <- withNModPoly x nmod_poly_modulus
  result <- newNModPoly n
  withNModPoly result $ \result ->
    withNModPoly x $ \x ->
    f result x
  return result

