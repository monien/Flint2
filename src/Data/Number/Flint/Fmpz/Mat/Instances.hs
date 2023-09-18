{-# OPTIONS_HADDOCK hide, prune, ignore-exports #-}
module Data.Number.Flint.Fmpz.Mat.Instances where

import System.IO.Unsafe

import Foreign.C.String
import Foreign.Marshal.Alloc ( free )
import Foreign.Storable

import Data.Number.Flint.Fmpz.Mat

instance Show FmpzMat where
  show x = unsafePerformIO $ do
    (_, cs) <- withFmpzMat x fmpz_mat_get_str_pretty
    s <- peekCString cs
    free cs
    return s

instance Eq FmpzMat where
  (==) x y = unsafePerformIO $ do
    (_, (_, flag)) <- withFmpzMat x $ \x -> do
      withFmpzMat y $ \y -> do
        fmpz_mat_equal x y
    return $ flag == 1

instance Num FmpzMat where
  (+) = lift2 fmpz_mat_add
  (-) = lift2 fmpz_mat_sub
  (*) = lift2 fmpz_mat_mul
  negate = lift1 fmpz_mat_neg
  fromInteger = undefined
  signum = undefined
  abs = undefined

instance Semigroup FmpzMat where
  (<>) = (*)

lift1 f x = unsafePerformIO $ do
  (_, (nx, mx)) <- withFmpzMat x $ \x -> do
    CFmpzMat _ nx mx _ <- peek x
    return (nx, mx)
  result <- newFmpzMat nx mx
  withFmpzMat x $ \x -> do
    withFmpzMat result $ \result -> do
      f result x
  return result
    
lift2 f x y = unsafePerformIO $ do
  (_, (nx, mx)) <- withFmpzMat x $ \x -> do
    CFmpzMat _ nx mx _ <- peek x
    return (nx, mx)
  (_, (ny, my)) <- withFmpzMat y $ \y -> do 
     CFmpzMat _ ny my _ <- peek y
     return (ny, my)
  result <- newFmpzMat nx my
  withFmpzMat result $ \z -> do
    withFmpzMat x $ \x -> do
      withFmpzMat y $ \y -> do
        f z x y
  return result