module Polynomial where

import System.IO.Unsafe
import Control.Monad

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.Storable
import Foreign.Marshal.Array

import GHC.TypeLits
import GHC.Exts

import Data.Proxy

import qualified Data.Vector as Vector
import Data.Vector (Vector, (!))
import Data.Vector.Algorithms.Intro (sort)

import Data.Number.Flint

class Polynomial a b where
  roots :: a -> b

instance Polynomial FmpzPoly (Vector Fmpz) where
  roots poly = snd $ snd $ unsafePerformIO $ do
    withFmpzPoly poly $ \poly -> do
      f <- newFmpzPolyFactor
      withFmpzPolyFactor f $ \f -> do
        fmpz_poly_factor f poly
        CFmpzPolyFactor c d e n alloc <- peek f
        fac <- forM [0..fromIntegral n-1] $ \j -> do
          m <- peek (e `advancePtr` j)
          a <- newFmpz
          let r = d `advancePtr` j
          fmpz_poly_neg r r
          withFmpz a $ \a -> do
            fmpz_zero a
            fmpz_poly_evaluate_fmpz a r a
          deg <- fmpz_poly_degree r
          return (a, deg)
        return $ Vector.fromList (map fst $ filter ((==1) . snd) fac)
            
instance forall n. KnownNat n => Polynomial FmpzPoly (Vector (CF n)) where
  roots poly = snd $ unsafePerformIO $ do
    let prec = fromInteger $ natVal (Proxy :: Proxy n)
        maxIter = 100
    withNewAcbPolyFromFmpzPoly poly prec $ \cpoly -> do
      m <- acb_poly_degree cpoly
      roots <- _acb_vec_init m
      found <- acb_poly_find_roots roots cpoly nullPtr maxIter prec
      Vector.generateM (fromIntegral found) $ \j -> do
        z <- newAcb
        withAcb z $ \z -> acb_set z (roots `advancePtr` (fromIntegral j))
        return $ CF z 

instance forall n. KnownNat n => Polynomial FmpqPoly (Vector (CF n)) where
  roots poly = snd $ unsafePerformIO $ do
    let prec = fromInteger $ natVal (Proxy :: Proxy n)
        maxIter = 100
    withNewAcbPolyFromFmpqPoly poly prec $ \cpoly -> do
      m <- acb_poly_degree cpoly
      roots <- _acb_vec_init m
      found <- acb_poly_find_roots roots cpoly nullPtr maxIter prec
      Vector.generateM (fromIntegral found) $ \j -> do
        z <- newAcb
        withAcb z $ \z -> acb_set z (roots `advancePtr` (fromIntegral j))
        return $ CF z 
