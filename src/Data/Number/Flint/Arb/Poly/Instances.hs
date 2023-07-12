{-# OPTIONS_HADDOCK hide, prune, ignore-exports #-}
module Data.Number.Flint.Arb.Poly.Instances (
    ArbPoly (..)
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

import Data.Number.Flint.Arb
import Data.Number.Flint.Arb.Instances
import Data.Number.Flint.Arb.Poly

import Data.Number.Flint.UFD

instance Show ArbPoly where
  show p = snd $ unsafePerformIO $ do
    withArbPoly p $ \p -> do
      cs <- arb_poly_get_strd p 16
      s <- peekCString cs
      free cs
      return s

instance IsList ArbPoly where
  type Item ArbPoly = Arb
  fromList c = unsafePerformIO $ do
    p <- newArbPoly
    withArbPoly p $ \p -> 
      forM_ [0..length c-1] $ \j ->
        withArb (c!!j) $ \a -> 
          arb_poly_set_coeff_arb p (fromIntegral j) a
    return p
  toList p = snd $ unsafePerformIO $ 
    withArbPoly p $ \p -> do
      d <- arb_poly_degree p
      forM [0..d] $ \j -> do
        c <- newArb
        withArb c $ \c -> arb_poly_get_coeff_arb c p j
        return c

lift2 f x y = unsafePerformIO $ do
  result <- newArbPoly
  withArbPoly result $ \result -> do
    withArbPoly x $ \x -> do
      withArbPoly y $ \y -> do
        f result x y
  return result

lift1 f x = unsafePerformIO $ do
  result <- newArbPoly
  withArbPoly result $ \result ->
    withArbPoly x $ \x ->
    f result x
  return result
