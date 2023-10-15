{-# OPTIONS_HADDOCK hide, prune, ignore-exports #-}
module Data.Number.Flint.Fmpq.Instances (
  Fmpq (..)
) where

import System.IO.Unsafe
import Control.Monad

import qualified Data.Ratio as Ratio
import Data.Ratio ((%))

import Foreign.Storable
import Foreign.C.Types
import Foreign.C.String
import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.Marshal.Alloc

import Data.Char
import Text.Read
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Instances
import Data.Number.Flint.Fmpq
import Data.Number.Flint.Quotient ((//))

instance Show Fmpq where
  show x = snd $ unsafePerformIO $ do
    let base = 10 :: CInt
    withFmpq x $ \x -> do
      cs <- fmpq_get_str nullPtr 10 x
      s <- peekCString cs
      free cs
      return s

instance Read Fmpq where
  readPrec = parens $
               (prec app_prec $ do
                  x <- step readPrec
                  Symbol "/" <- lexP
                  y <- step readPrec
                  return (x // y))
           +++ (prec up_prec $ do
                  x <- step readPrec
                  return (x // 1))
          where app_prec = 10
                up_prec = 5
       
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
    let n = fromInteger $ Ratio.numerator x
        d = fromInteger $ Ratio.denominator x
    withFmpz n $ \n ->
      withFmpz d $ \d ->
        withFmpq result $ \result -> do
          fmpq_set_fmpz_frac result n d
          fmpq_canonicalise result
    return result

instance Real Fmpq where
  toRational x = unsafePerformIO $ do
    p <- newFmpz
    q <- newFmpz
    withFmpq x $ \x -> do
      withFmpz p $ \p -> do
        withFmpz q $ \q -> do
          fmpq_get_fmpz_frac p q x
    return $ (toInteger p) % (toInteger q)

instance RealFrac Fmpq where
  properFraction x =  unsafePerformIO $ do
    p <- newFmpz
    q <- newFmpz
    r <- newFmpq
    withFmpq x $ \x -> do
      withFmpz p $ \p -> do
        withFmpz q $ \q -> do
          withFmpq r $ \r -> do
            withNewFmpz $ \tmp -> do
              fmpq_get_fmpz_frac p q x
              fmpz_tdiv_qr p tmp p q
              fmpq_set_fmpz_frac r tmp q
    return (fromIntegral p, r)
   
lift1 f x = fst $ unsafePerformIO $ 
  withNewFmpq $ \result -> 
    withFmpq x $ \x ->
      f result x
  
lift2 f x y = fst $ unsafePerformIO $ 
  withNewFmpq $ \result ->
    withFmpq x $ \x ->
      withFmpq y $ \y ->
        f result x y

