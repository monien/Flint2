{-# language
    TupleSections
  , TypeSynonymInstances
  , FlexibleInstances
#-}

module Data.Number.Flint.Support.Mpfr.Mat.FFI (
  -- * Matrices of MPFR floating-point numbers
    MpfrMat (..)
  , CMpfrMat (..)
  , newMpfrMat
  , withMpfrMat
  , withNewMpfrMat
  -- * Memory management
  , mpfr_mat_init
  , mpfr_mat_clear
  -- * Basic manipulation
  , mpfr_mat_entry
  , mpfr_mat_swap
  , mpfr_mat_swap_entrywise
  , mpfr_mat_set
  , mpfr_mat_zero
  -- * Comparison
  , mpfr_mat_equal
  -- * Randomisation
  , mpfr_mat_randtest
  -- * Basic arithmetic
  , mpfr_mat_mul_classical
) where

-- Matrices of MPFR floating-point numbers -------------------------------------

import Foreign.C.Types
import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.Storable

import Data.Number.Flint.Flint

#include <flint/flint.h>
#include <flint/mpfr_mat.h>

-- mpfr_mat_t ------------------------------------------------------------------

data MpfrMat = MpfrMat {-# UNPACK #-} !(ForeignPtr CMpfrMat)
type CMpfrMat = CFlint MpfrMat

instance Storable CMpfrMat where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size mpfr_mat_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment mpfr_mat_t}
  peek = error "CMpfrMat.peek: Not defined."
  poke = error "CMpfrMat.poke: Not defined."

newMpfrMat rows cols prec = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> mpfr_mat_init x rows cols prec
  addForeignPtrFinalizer p_mpfr_mat_clear x
  return $ MpfrMat x

{-# INLINE withMpfrMat #-}
withMpfrMat (MpfrMat x) f = do
  withForeignPtr x $ \px -> f px >>= return . (MpfrMat x,)

withNewMpfrMat rows cols prec f = do
  x <- newMpfrMat rows cols prec
  withMpfrMat x f
  
-- Memory management -----------------------------------------------------------

-- | /mpfr_mat_init/ /mat/ /rows/ /cols/ /prec/ 
-- 
-- Initialises a matrix with the given number of rows and columns and the
-- given precision for use. The precision is the exact precision of the
-- entries.
foreign import ccall "mpfr_mat.h mpfr_mat_init"
  mpfr_mat_init :: Ptr CMpfrMat -> CLong -> CLong -> Ptr CMpfrPrec -> IO ()

-- | /mpfr_mat_clear/ /mat/ 
-- 
-- Clears the given matrix.
foreign import ccall "mpfr_mat.h mpfr_mat_clear"
  mpfr_mat_clear :: Ptr CMpfrMat -> IO ()

foreign import ccall "mpfr_mat.h &mpfr_mat_clear"
  p_mpfr_mat_clear :: FunPtr (Ptr CMpfrMat -> IO ())

-- Basic manipulation ----------------------------------------------------------

-- | /mpfr_mat_entry/ /mat/ /i/ /j/ 
-- 
-- Return a reference to the entry at row \(i\) and column \(j\) of the
-- given matrix. The values \(i\) and \(j\) must be within the bounds for
-- the matrix. The reference can be used to either return or set the given
-- entry.
foreign import ccall "mpfr_mat.h mpfr_mat_entry"
  mpfr_mat_entry :: Ptr CMpfrMat -> CLong -> CLong -> IO (Ptr (Ptr CMpfr))

-- | /mpfr_mat_swap/ /mat1/ /mat2/ 
-- 
-- Efficiently swap matrices @mat1@ and @mat2@.
foreign import ccall "mpfr_mat.h mpfr_mat_swap"
  mpfr_mat_swap :: Ptr CMpfrMat -> Ptr CMpfrMat -> IO ()

-- | /mpfr_mat_swap_entrywise/ /mat1/ /mat2/ 
-- 
-- Swaps two matrices by swapping the individual entries rather than
-- swapping the contents of the structs.
foreign import ccall "mpfr_mat.h mpfr_mat_swap_entrywise"
  mpfr_mat_swap_entrywise :: Ptr CMpfrMat -> Ptr CMpfrMat -> IO ()

-- | /mpfr_mat_set/ /mat1/ /mat2/ 
-- 
-- Set @mat1@ to the value of @mat2@.
foreign import ccall "mpfr_mat.h mpfr_mat_set"
  mpfr_mat_set :: Ptr CMpfrMat -> Ptr CMpfrMat -> IO ()

-- | /mpfr_mat_zero/ /mat/ 
-- 
-- Set @mat@ to the zero matrix.
foreign import ccall "mpfr_mat.h mpfr_mat_zero"
  mpfr_mat_zero :: Ptr CMpfrMat -> IO ()

-- Comparison ------------------------------------------------------------------

-- | /mpfr_mat_equal/ /mat1/ /mat2/ 
-- 
-- Return \(1\) if the two given matrices are equal, otherwise return
-- \(0\).
foreign import ccall "mpfr_mat.h mpfr_mat_equal"
  mpfr_mat_equal :: Ptr CMpfrMat -> Ptr CMpfrMat -> IO CInt

-- Randomisation ---------------------------------------------------------------

-- | /mpfr_mat_randtest/ /mat/ /state/ 
-- 
-- Generate a random matrix with random number of rows and columns and
-- random entries for use in test code.
foreign import ccall "mpfr_mat.h mpfr_mat_randtest"
  mpfr_mat_randtest :: Ptr CMpfrMat -> Ptr CFRandState -> IO ()

-- Basic arithmetic ------------------------------------------------------------

-- | /mpfr_mat_mul_classical/ /C/ /A/ /B/ /rnd/ 
-- 
-- Set \(C\) to the product of \(A\) and \(B\) with the given rounding
-- mode, using the classical algorithm.
foreign import ccall "mpfr_mat.h mpfr_mat_mul_classical"
  mpfr_mat_mul_classical :: Ptr CMpfrMat -> Ptr CMpfrMat -> Ptr CMpfrMat -> CMpfrRnd -> IO ()

