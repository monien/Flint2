{-# OPTIONS_HADDOCK hide, prune, ignore-exports #-}
module Data.Number.Flint.Fmpz.Instances (
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

import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Factor
import Data.Number.Flint.UFD

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
    let n :: Integer
        [(n, r)] = readsPrec d s
    result <- newFmpz
    (_, flag) <- withFmpz result $ \result -> 
      withCString (show n) $ \s -> 
        fmpz_set_str result s 10
    if flag == 0 then 
      return [(result, r)]
    else
      return []

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
  toEnum = fromInteger . fromIntegral
  fromEnum = fromIntegral . toInteger
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
  fromInteger x = read (show x) :: Fmpz
  signum = lift1 sgn where
    sgn result x = do
      s <- fmpz_sgn x
      fmpz_set_si result (fromIntegral s)

instance Real Fmpz where
  toRational x = (toInteger x) % 1

instance Integral Fmpz where
  mod x y = unsafePerformIO $ do
    result <- newFmpz
    withFmpz result $ \result ->
      withFmpz x $ \x ->
        withFmpz y $ \y -> fmpz_mod result x y
    return result
  quotRem x y = unsafePerformIO $ do
    quot <- newFmpz
    rem <- newFmpz
    withFmpz x $ \x -> 
      withFmpz y $ \y -> 
        withFmpz quot $ \quot -> 
          withFmpz rem $ \rem -> 
            fmpz_tdiv_qr quot rem x y
    return (quot, rem)
  toInteger x = read (show x) :: Integer

instance UFD Fmpz where
  factor x = snd $ snd $ unsafePerformIO $
    withFmpz x $ \y -> do
      is_one <- fmpz_is_one y
      f <- newFmpzFactor
      withFmpzFactor f $ \f -> do
        if not (is_one == 1) then do
          fmpz_factor f y
          CFmpzFactor s d e _ n <- peek f
          result <- forM [0 .. fromIntegral n-1] $ \j -> do
            f <- newFmpz
            m <- peek (e `advancePtr` j)
            withFmpz f $ \f -> fmpz_set f (d `advancePtr` j)
            return (f, fromIntegral m)
          return $ if s < 1 then (-1, 1) : result else result
        else do
          return [(1, 1)]


instance Arbitrary Fmpz where
  arbitrary = do
    x <- arbitrary
    return $ fromInteger x
      
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