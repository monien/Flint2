module Fmpz (
  Fmpz (..)
, UFD (..)
) where

import Test.QuickCheck
import System.IO.Unsafe
import Control.Monad

import Data.Ratio

import Foreign.Storable
import Foreign.C.Types
import Foreign.C.String
import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.Marshal.Alloc
import Foreign.Marshal.Array (advancePtr)

import Data.Number.Flint
import UFD

instance Show Fmpz where
  show x = snd $ unsafePerformIO $ do
    let base = 10 :: CInt
    withFmpz x $ \x -> do
      cString <- fmpz_get_str nullPtr base x
      result <- peekCString cString
      free cString
      return result

instance Read Fmpz where
  readsPrec d s = unsafePerformIO $ do
    let [(n, r)] = readsPrec d s
    result <- toFmpz n
    return [(result, r)]

instance Eq Fmpz where
  (==) x y = snd $ snd $ unsafePerformIO $ 
    withFmpz x $ \x ->
      withFmpz y $ \y -> do
        result <- fmpz_equal x y
        return $ result == 1

instance Ord Fmpz where
  compare x y = snd $ snd $ unsafePerformIO $
    withFmpz x $ \x ->
      withFmpz y $ \y -> do
        ord <- fmpz_cmp x y
        return $ if ord > 0 then GT else (if ord < 0 then LT else EQ)

instance Enum Fmpz where
  toEnum x = unsafePerformIO $ toFmpz $ fromIntegral x
  fromEnum x = unsafePerformIO $ do
    y <- fromFmpz x
    return $ fromIntegral y
  succ x = unsafePerformIO $ do
    y <- newFmpz 
    withFmpz x $ \x -> withFmpz y $ \y -> fmpz_add_ui y x 1
    return y
    
instance Num Fmpz where
  {-# INLINE (+) #-}
  (+) = lift2 fmpz_add
  {-# INLINE (-) #-}
  (-) = lift2 fmpz_sub
  {-# INLINE (*) #-}
  (*) = lift2 fmpz_mul
  negate = lift1 fmpz_neg
  abs    = lift1 fmpz_abs
  fromInteger x = unsafePerformIO $ toFmpz x
  signum = lift1 sgn where
    sgn result x = do
      s <- fmpz_sgn x
      fmpz_set_si result (fromIntegral s)

instance Real Fmpz where
  toRational x = unsafePerformIO $ do
    n <- fromFmpz x
    return $ n % 1

instance Integral Fmpz where
  quotRem x y = unsafePerformIO $ do
    quot <- newFmpz
    rem <- newFmpz
    withFmpz x $ \x -> 
      withFmpz y $ \y -> 
        withFmpz quot $ \quot -> 
          withFmpz rem $ \rem -> 
            fmpz_tdiv_qr quot rem x y
    return (quot, rem)
  toInteger x = unsafePerformIO $ fromFmpz x

instance UFD Fmpz where
  factor x = snd $ snd $ unsafePerformIO $
    withFmpz x $ \y -> do
      f <- newFmpzFactor
      withFmpzFactor f $ \f -> do
        fmpz_factor f y
        (CFmpzFactor _ d e _ n) <- peek f
        forM [0 .. fromIntegral n-1] $ \j -> do
          f <- newFmpz
          m <- peek (e `advancePtr` j)
          withFmpz f $ \f -> fmpz_set f (d `advancePtr` j)
          return (f, fromIntegral m)

instance Arbitrary Fmpz where
  arbitrary = do
    x <- arbitrary
    return $ fromInteger x
    
-- fac x = snd $ snd $ unsafePerformIO $ do
--   y <- toFmpz x
--   withFmpz y $ \y -> do
--     f <- newFmpzFactor
--     withFmpzFactor f $ \f -> do
--       fmpz_factor f y
--       (CFmpzFactor _ d e _ n) <- peek f
--       forM [0 .. fromIntegral n-1] $ \j -> do
--         f <- withOutInteger_ $ \y -> fmpz_get_mpz y (d `advancePtr` j)
--         m <- peek (e `advancePtr` j)
--         return (f, fromIntegral m)
      
lift1 f x = unsafePerformIO $ do
  z <- newFmpz
  withFmpz x $ \x ->
    withFmpz z $ \z -> f z x
  return z
  
lift2 f x y = unsafePerformIO $ do
  z <- newFmpz
  withFmpz x $ \x ->
    withFmpz y $ \y ->
      withFmpz z $ \z -> f z x y
  return z

-- lift1Integer f x = unsafePerformIO $ do
--   x' <- toFmpz x
--   let result = f x'
--   fromFmpz result

-- withInteger x f = do
--   x' <- toFmpz x
--   withFmpz x' $ \x' -> f x'