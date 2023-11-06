module Data.Number.Flint.Calcium.Fexpr.Instances where

import System.IO.Unsafe

import Foreign.Ptr
import Foreign.C.String
import Foreign.Storable
import Foreign.Marshal.Alloc (free)
import Foreign.Marshal.Array (advancePtr)

import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Instances
import Data.Number.Flint.Calcium.Fexpr

instance Show Fexpr where
  show x = snd $ unsafePerformIO $ do
    withFexpr x $ \x -> do
      cs <- fexpr_get_str x
      s <- peekCString cs
      free cs
      return s

instance Num Fexpr where
  {-# INLINE (+) #-}
  (+) = lift2 fexpr_add
  {-# INLINE (-) #-}
  (-) = lift2 fexpr_sub
  {-# INLINE (*) #-}
  (*) = lift2 fexpr_mul
  negate = lift1 fexpr_neg
  abs    = undefined
  fromInteger x = unsafePerformIO $ do
    expr <- newFexpr
    withFexpr expr $ \expr -> do
      withFmpz (fromInteger x) $ \tmp -> do
        fexpr_set_fmpz expr tmp
    return expr
  signum = undefined

lift1 f x = unsafePerformIO $ do
  z <- newFexpr
  withFexpr x $ \x ->
    withFexpr z $ \z -> f z x
  return z
  
lift2 f x y = unsafePerformIO $ do
  z <- newFexpr
  withFexpr x $ \x ->
    withFexpr y $ \y ->
      withFexpr z $ \z -> f z x y
  return z

