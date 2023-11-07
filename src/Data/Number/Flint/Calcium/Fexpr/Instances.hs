module Data.Number.Flint.Calcium.Fexpr.Instances where

import System.IO.Unsafe

import Foreign.Ptr
import Foreign.C.Types
import Foreign.C.String
import Foreign.Storable
import Foreign.Marshal.Alloc (free)
import Foreign.Marshal.Array (advancePtr)

import qualified Data.Map as Map
import Data.Map (Map, (!), (!?))

import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpq
import Data.Number.Flint.Fmpz.Instances
import Data.Number.Flint.Arb.Arf
import Data.Number.Flint.Calcium.Fexpr
import Data.Number.Flint.Calcium.Fexpr.Builtin

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

class FlintExpression a where
  toFexpr :: a -> IO Fexpr

instance FlintExpression FEXR_Builtin where
  toFexpr x = do
    result <- newFexpr
    withFexpr result $ \result -> do
      fexpr_set_symbol_builtin result (fexpr_builtin_hash ! x)
    return result

instance FlintExpression Fmpz where
  toFexpr x = do
    result <- newFexpr
    withFexpr result $ \expr -> do
      withFmpz x $ \x -> do
        fexpr_set_fmpz expr x
    return result

instance FlintExpression Fmpq where
  toFexpr x = do
    result <- newFexpr
    withFexpr result $ \expr -> do
      withFmpq x $ \x -> do
        fexpr_set_fmpq expr x
    return result

instance FlintExpression CDouble where
  toFexpr = liftTo fexpr_set_d

instance FlintExpression CLong where
  toFexpr = liftTo fexpr_set_si

instance FlintExpression CULong where
  toFexpr = liftTo fexpr_set_ui

instance FlintExpression Arf where
  toFexpr x = do
    result <- newFexpr
    withFexpr result $ \expr -> do
      withArf x $ \x -> do
        fexpr_set_arf expr x
    return result

instance FlintExpression String where
  toFexpr name = do
    result <- newFexpr
    withFexpr result $ \result -> do
      withCString name $ \name -> do
        fexpr_set_symbol_str result name
    return result

--------------------------------------------------------------------------------

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

liftTo f x = do
    result <- newFexpr
    withFexpr result $ \expr -> f expr x
    return result

