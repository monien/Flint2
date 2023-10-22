module Data.Number.Flint.Arb.Mag.Instances (
  Mag (..)
) where

import System.IO.Unsafe
import Foreign.C.String
import Foreign.Marshal.Alloc

import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Instances
import Data.Number.Flint.Arb.Mag

instance Show Mag where
  show x = unsafePerformIO $ do
    (_, cs) <- withMag x mag_get_str
    s <- peekCString cs
    free cs
    return s

instance Eq Mag where
  (==) x y = snd $ snd $ unsafePerformIO $ do
    withMag x $ \x -> do
      withMag y $ \y -> do
        f <- mag_equal x y
        return $ f == 1

instance Ord Mag where
  compare x y = snd $ snd $ unsafePerformIO $ do
    withMag x $ \x -> do
      withMag y $ \y -> do
        f <- mag_cmp x y
        return $ f `compare` 0

instance Num Mag where
  (+) = lift2 mag_add
  (-) = lift2 mag_sub
  (*) = lift2 mag_mul
  abs = undefined
  signum = undefined
  fromInteger x = unsafePerformIO $ do
    let tmp = fromInteger x :: Fmpz
    result <- newMag
    withMag result $ \p -> do
      withFmpz tmp $ \tmp -> do
        mag_set_fmpz p tmp
    return result

instance Fractional Mag where
  (/) = lift2 mag_div
  recip = lift1 mag_inv
  fromRational = undefined
  
lift1 f x = fst $ unsafePerformIO $ 
  withNewMag $ \result -> 
    withMag x $ \x ->
      f result x
 
lift2 f x y = unsafePerformIO $ do
  result <- newMag
  withMag result $ \result -> do
    withMag x $ \x -> do
      withMag y $ \y -> do
        f result x y
  return result


 
