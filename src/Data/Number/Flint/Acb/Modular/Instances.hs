{-|
module      :  Data.Number.Flint.Acb.Modular.Instances
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de
-}

module Data.Number.Flint.Acb.Modular.Instances where

import System.IO.Unsafe

import Foreign.C.String
import Foreign.Marshal.Alloc (free)

import Data.Group

import Data.Number.Flint.Acb.Modular

instance Show PSL2Z where
  show x = unsafePerformIO $ do
    (_, cs) <- withPSL2Z x psl2z_get_str
    s <- peekCString cs
    free cs
    return s

instance Eq PSL2Z where
  (==) x y =  snd $ snd $ unsafePerformIO $ do
    withPSL2Z x $ \x -> do
      withPSL2Z y $ \y -> do
        flag <- psl2z_equal x y
        return $ flag == 1
        
instance Monoid PSL2Z where
  mempty = unsafePerformIO $ do
    result <- newPSL2Z
    return result
  
instance Semigroup PSL2Z where
  (<>) x y = fst $ unsafePerformIO $ do
    withNewPSL2Z $ \result -> do 
      withPSL2Z x $ \x -> do
        withPSL2Z y $ \y -> do
          psl2z_mul result x y
          
instance Group PSL2Z where
  invert x = fst $ unsafePerformIO $ do
    withNewPSL2Z $ \result -> do
      withPSL2Z x $ \x -> do
        psl2z_inv result x

instance Show PSL2ZWord where
  show x = unsafePerformIO $ do
    (_, cs) <- withPSL2ZWord x psl2z_word_get_str_pretty
    s <- peekCString cs
    free cs
    return s