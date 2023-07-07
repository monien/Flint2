module Data.Number.Flint.NF.Fmpzi.Instances where

import System.IO.Unsafe
import Foreign.C.String
import Foreign.Marshal.Alloc ( free )

import Data.Number.Flint.NF.Fmpzi

instance Show Fmpzi where
  show x = unsafePerformIO $ do
    (_, cs) <- withFmpzi x fmpzi_get_str
    s <- peekCString cs
    free cs
    return s

instance Eq Fmpzi where
  (==) x y = snd $ snd $ unsafePerformIO $ 
    withFmpzi x $ \x ->
      withFmpzi y $ \y -> do
        result <- fmpzi_equal x y
        return $ result == 1

instance Num Fmpzi where
  {-# INLINE (+) #-}
  (+) = lift2 fmpzi_add
  {-# INLINE (-) #-}
  (-) = lift2 fmpzi_sub
  {-# INLINE (*) #-}
  (*) = lift2 fmpzi_mul
  negate = lift1 fmpzi_neg
  abs    = undefined
  fromInteger x = unsafePerformIO $ do
    result <- newFmpzi
    withFmpzi result $ \result -> do
      fmpzi_set_si_si result (fromInteger x) 1
    return result
  signum = undefined

lift1 f x = fst $ unsafePerformIO $ 
  withNewFmpzi $ \result -> 
    withFmpzi x $ \x ->
      f result x
  
lift2 f x y = fst $ unsafePerformIO $ 
  withNewFmpzi $ \result ->
    withFmpzi x $ \x ->
      withFmpzi y $ \y ->
        f result x y

