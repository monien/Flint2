{-# OPTIONS_HADDOCK hide, prune, ignore-exports #-}
module Data.Number.Flint.Acb.Poly.Instances (
    AcbPoly (..)
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

import Data.Number.Flint.Acb
import Data.Number.Flint.Acb.Instances
import Data.Number.Flint.Acb.Poly

import Data.Number.Flint.UFD

instance Show AcbPoly where
  show p = snd $ unsafePerformIO $ do
    withAcbPoly p $ \p -> do
      cs <- acb_poly_get_strd p 16
      s <- peekCString cs
      free cs
      return s

instance IsList AcbPoly where
  type Item AcbPoly = Acb
  fromList c = unsafePerformIO $ do
    p <- newAcbPoly
    withAcbPoly p $ \p -> 
      forM_ [0..length c-1] $ \j ->
        withAcb (c!!j) $ \a -> 
          acb_poly_set_coeff_acb p (fromIntegral j) a
    return p
  toList p = snd $ unsafePerformIO $ 
    withAcbPoly p $ \p -> do
      d <- acb_poly_degree p
      forM [0..d] $ \j -> do
        c <- newAcb
        withAcb c $ \c -> acb_poly_get_coeff_acb c p j
        return c

lift2 f x y = unsafePerformIO $ do
  result <- newAcbPoly
  withAcbPoly result $ \result -> do
    withAcbPoly x $ \x -> do
      withAcbPoly y $ \y -> do
        f result x y
  return result

lift1 f x = unsafePerformIO $ do
  result <- newAcbPoly
  withAcbPoly result $ \result ->
    withAcbPoly x $ \x ->
    f result x
  return result
