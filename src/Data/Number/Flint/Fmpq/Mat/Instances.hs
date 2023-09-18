{-# OPTIONS_HADDOCK hide, prune, ignore-exports #-}
module Data.Number.Flint.Fmpq.Mat.Instances where

import System.IO.Unsafe

import Foreign.C.String
import Foreign.Marshal.Alloc ( free )
import Foreign.Storable

import Data.Number.Flint.Fmpq.Mat

instance Show FmpqMat where
  show x = unsafePerformIO $ do
    (_, cs) <- withFmpqMat x fmpq_mat_get_str
    s <- peekCString cs
    free cs
    return s
      
instance Eq FmpqMat where
  (==) x y = unsafePerformIO $ do
    (_, (_, flag)) <- withFmpqMat x $ \x -> do
      withFmpqMat y $ \y -> do
        fmpq_mat_equal x y
    return $ flag == 1

instance Num FmpqMat where
  (+) = lift2 fmpq_mat_add
  (-) = lift2 fmpq_mat_sub
  (*) = lift2 fmpq_mat_mul
  negate = lift1 fmpq_mat_neg
  fromInteger = undefined
  signum = undefined
  abs = undefined

instance Fractional FmpqMat where
  recip x = unsafePerformIO $ do
    (_, (nx, mx)) <- withFmpqMat x $ \x -> do
      CFmpqMat _ nx mx _ <- peek x
      return (nx, mx)
    result <- newFmpqMat nx mx
    (_, (_, flag)) <- withFmpqMat x $ \x -> do
      withFmpqMat result $ \result -> do
        flag <- fmpq_mat_inv result x
        return flag
    return result
  fromRational = undefined

instance Semigroup FmpqMat where
  (<>) = (*)
  
lift1 f x = unsafePerformIO $ do
  (_, (nx, mx)) <- withFmpqMat x $ \x -> do
    CFmpqMat _ nx mx _ <- peek x
    return (nx, mx)
  result <- newFmpqMat nx mx
  withFmpqMat x $ \x -> do
    withFmpqMat result $ \result -> do
      f result x
  return result
    
lift2 f x y = unsafePerformIO $ do
  (_, (nx, mx)) <- withFmpqMat x $ \x -> do
    CFmpqMat _ nx mx _ <- peek x
    return (nx, mx)
  (_, (ny, my)) <- withFmpqMat y $ \y -> do 
     CFmpqMat _ ny my _ <- peek y
     return (ny, my)
  result <- newFmpqMat nx my
  withFmpqMat result $ \z -> do
    withFmpqMat x $ \x -> do
      withFmpqMat y $ \y -> do
        f z x y
  return result
