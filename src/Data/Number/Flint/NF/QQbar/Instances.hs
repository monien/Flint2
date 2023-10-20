module Data.Number.Flint.NF.QQbar.Instances where

import System.IO.Unsafe
import Foreign.C.String
import Foreign.Marshal.Alloc ( free )

import Data.Number.Flint.NF.QQbar

instance Show QQbar where
  show x = unsafePerformIO $ do
    (_, cs) <- withQQbar x qqbar_get_str
    s <- peekCString cs
    free cs
    return s

instance Eq QQbar where
  (==) x y = snd $ snd $ unsafePerformIO $ 
    withQQbar x $ \x ->
      withQQbar y $ \y -> do
        result <- qqbar_equal x y
        return $ result == 1

instance Num QQbar where
  {-# INLINE (+) #-}
  (+) = lift2 qqbar_add
  {-# INLINE (-) #-}
  (-) = lift2 qqbar_sub
  {-# INLINE (*) #-}
  (*) = lift2 qqbar_mul
  negate = lift1 qqbar_neg
  abs    = undefined
  fromInteger x = unsafePerformIO $ do
    result <- newQQbar
    withQQbar result $ \result -> do
      qqbar_set_si result (fromInteger x)
    return result
  signum = undefined

lift1 f x = fst $ unsafePerformIO $ 
  withNewQQbar $ \result -> 
    withQQbar x $ \x ->
      f result x
  
lift2 f x y = fst $ unsafePerformIO $ 
  withNewQQbar $ \result ->
    withQQbar x $ \x ->
      withQQbar y $ \y ->
        f result x y

