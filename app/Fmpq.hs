module Fmpq (
  numerator
, denominator
, harmonicSum
) where

import System.IO.Unsafe
import Control.Monad

import Data.Ratio

import Foreign.Storable
import Foreign.C.Types
import Foreign.C.String
import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.Marshal.Alloc

import Data.Number.Flint

import Fmpz

instance Show Fmpq where
  show x = snd $ unsafePerformIO $ do
    let base = 10 :: CInt
    withFmpq x $ \x -> do
      cs <- fmpq_get_str nullPtr 10 x
      s <- peekCString cs
      free cs
      return s

instance Eq Fmpq where
  (==) x y = snd $ snd $ unsafePerformIO $ 
    withFmpq x $ \x ->
      withFmpq y $ \y -> do
        result <- fmpq_equal x y
        return $ result == 1

instance Ord Fmpq where
  compare x y = snd $ snd $ unsafePerformIO $ 
    withFmpq x $ \x ->
      withFmpq y $ \y -> do
        ord <- fmpq_cmp x y
        return $ if ord > 0 then GT else (if ord < 0 then LT else EQ)
    
instance Num Fmpq where
  {-# INLINE (+) #-}
  (+) = lift2 fmpq_add
  {-# INLINE (-) #-}
  (-) = lift2 fmpq_sub
  {-# INLINE (*) #-}
  (*) = lift2 fmpq_mul
  negate = lift1 fmpq_neg
  abs    = lift1 fmpq_abs
  fromInteger x = unsafePerformIO $ do
    let n = fromInteger x 
        d = 1 :: Fmpz
    result <- newFmpq
    withFmpz n $ \n ->
      withFmpz d $ \d ->
        withFmpq result $ \result -> do
          fmpz_one d
          fmpq_set_fmpz_frac result n d
          fmpq_canonicalise result
    return result
  signum = lift1 sgn where
    sgn result x = do
      s <- fmpq_sgn x
      fmpq_set_si result (fromIntegral s) 1

instance Fractional Fmpq where
  (/) = lift2 fmpq_div
  recip = lift1 fmpq_inv
  fromRational x = unsafePerformIO $ do
    result <- newFmpq
    let n = fromInteger $ numerator x
        d = fromInteger $ denominator x
    withFmpz n $ \n ->
      withFmpz d $ \d ->
        withFmpq result $ \result -> do
          fmpq_set_fmpz_frac result n d
          fmpq_canonicalise result
    return result

lift1 f x = fst $ unsafePerformIO $ 
  withNewFmpq $ \result -> 
    withFmpq x $ \x ->
      f result x
  
lift2 f x y = fst $ unsafePerformIO $ 
  withNewFmpq $ \result ->
    withFmpq x $ \x ->
      withFmpq y $ \y ->
        f result x y

harmonicSum k = fst $ unsafePerformIO $ do
  h <- newFmpq
  withFmpq h $ \h -> do
    fmpq_harmonic_ui h (fromIntegral k)
    
-- bernoulli k = fst $ unsafePerformIO $ do
--   withNewFmpq $ flip arith_bernoulli_number (fromIntegral k)
  
-- fraction x = unsafePerformIO $ do
--   n <- newFmpz
--   d <- newFmpz
--   withFmpq x $ \x ->
--     withFmpz n $ \n ->
--       withFmpz d $ \d -> 
--         fmpq_get_fmpz_frac n d x
--   return (n, d)

-- checkBernoulli n = do
--   let k = 2*n
--       b = bernoulli k
--   print b
--   forM_ [2..k+1] $ \p -> do
--     a <- n_is_prime p
--     when (a == 1 && k `mod` (p-1) == 0) $ do
--       let x :: Fmpq;
--           x = recip $ fromIntegral p 
--       withFmpq x $ \x -> 
--         withFmpq b $ \b -> 
--           fmpq_add b b x
--       return ()
--   print b

-- bernoulliDenominator k = do
--   let d = 1 :: Fmpz
--   forM_ [2..k+1] $ \p -> do
--     a <- n_is_prime p
--     when (a == 1 && k `mod` (p-1) == 0) $ do
--       withFmpz d $ \d -> fmpz_mul_ui d d p
--       return ()
--   return d