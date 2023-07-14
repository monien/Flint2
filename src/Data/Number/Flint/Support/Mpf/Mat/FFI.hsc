module Data.Number.Flint.Support.Mpf.Mat.FFI (
  -- * Matrices of MPF floating-point numbers
    MpfMat (..)
  , CMpfMat (..)
  , newMpfMat
  , withMpfMat
  , withNewMpfMat
  -- * Memory management
  , mpf_mat_init
  , mpf_mat_clear
  -- * Basic assignment and manipulation
  , mpf_mat_set
  , mpf_mat_swap
  , mpf_mat_swap_entrywise
  , mpf_mat_entry
  , mpf_mat_zero
  , mpf_mat_one
  -- * Random matrix generation
  , mpf_mat_randtest
  -- * Input and output
  , mpf_mat_print
  -- * Comparison
  , mpf_mat_equal
  , mpf_mat_approx_equal
  , mpf_mat_is_zero
  , mpf_mat_is_empty
  , mpf_mat_is_square
  -- * Matrix multiplication
  , mpf_mat_mul
  -- * Gram-Schmidt Orthogonalisation and QR Decomposition
  , mpf_mat_gso
  , mpf_mat_qr
) where 

-- matrices of MPF floating-point numbers --------------------------------------

import Foreign.C.Types
import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.Storable

import Data.Number.Flint.Flint

#include <flint/flint.h>
#include <flint/mpf_mat.h>

-- mpf_mat_t -------------------------------------------------------------------

data MpfMat = MpfMat {-# UNPACK #-} !(ForeignPtr CMpfMat)
type CMpfMat = CFlint MpfMat

instance Storable CMpfMat where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size mpf_mat_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment mpf_mat_t}
  peek = error "CMpfMat.peek: Not defined."
  poke = error "CMpfMat.poke: Not defined."

newMpfMat rows cols prec = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> mpf_mat_init x rows cols prec
  addForeignPtrFinalizer p_mpf_mat_clear x
  return $ MpfMat x

{-# INLINE withMpfMat #-}
withMpfMat (MpfMat x) f = do
  withForeignPtr x $ \px -> f px >>= return . (MpfMat x,)

withNewMpfMat rows cols prec f = do
  x <- newMpfMat rows cols prec
  withMpfMat x f
  
-- Memory management -----------------------------------------------------------

-- | /mpf_mat_init/ /mat/ /rows/ /cols/ /prec/ 
-- 
-- Initialises a matrix with the given number of rows and columns and the
-- given precision for use. The precision is at least the precision of the
-- entries.
foreign import ccall "mpf_mat.h mpf_mat_init"
  mpf_mat_init :: Ptr CMpfMat -> CLong -> CLong -> CFBitCnt -> IO ()

-- | /mpf_mat_clear/ /mat/ 
-- 
-- Clears the given matrix.
foreign import ccall "mpf_mat.h mpf_mat_clear"
  mpf_mat_clear :: Ptr CMpfMat -> IO ()

foreign import ccall "mpf_mat.h &mpf_mat_clear"
  p_mpf_mat_clear :: FunPtr (Ptr CMpfMat -> IO ())

-- Basic assignment and manipulation -------------------------------------------

-- | /mpf_mat_set/ /mat1/ /mat2/ 
-- 
-- Sets @mat1@ to a copy of @mat2@. The dimensions of @mat1@ and @mat2@
-- must be the same.
foreign import ccall "mpf_mat.h mpf_mat_set"
  mpf_mat_set :: Ptr CMpfMat -> Ptr CMpfMat -> IO ()

-- | /mpf_mat_swap/ /mat1/ /mat2/ 
-- 
-- Swaps two matrices. The dimensions of @mat1@ and @mat2@ are allowed to
-- be different.
foreign import ccall "mpf_mat.h mpf_mat_swap"
  mpf_mat_swap :: Ptr CMpfMat -> Ptr CMpfMat -> IO ()

-- | /mpf_mat_swap_entrywise/ /mat1/ /mat2/ 
-- 
-- Swaps two matrices by swapping the individual entries rather than
-- swapping the contents of the structs.
foreign import ccall "mpf_mat.h mpf_mat_swap_entrywise"
  mpf_mat_swap_entrywise :: Ptr CMpfMat -> Ptr CMpfMat -> IO ()

-- | /mpf_mat_entry/ /mat/ /i/ /j/ 
-- 
-- Returns a reference to the entry of @mat@ at row \(i\) and column \(j\).
-- Both \(i\) and \(j\) must not exceed the dimensions of the matrix. The
-- return value can be used to either retrieve or set the given entry.
foreign import ccall "mpf_mat.h mpf_mat_entry"
  mpf_mat_entry :: Ptr CMpfMat -> CLong -> CLong -> IO (Ptr CMpf)

-- | /mpf_mat_zero/ /mat/ 
-- 
-- Sets all entries of @mat@ to 0.
foreign import ccall "mpf_mat.h mpf_mat_zero"
  mpf_mat_zero :: Ptr CMpfMat -> IO ()

-- | /mpf_mat_one/ /mat/ 
-- 
-- Sets @mat@ to the unit matrix, having ones on the main diagonal and
-- zeroes elsewhere. If @mat@ is nonsquare, it is set to the truncation of
-- a unit matrix.
foreign import ccall "mpf_mat.h mpf_mat_one"
  mpf_mat_one :: Ptr CMpfMat -> IO ()

-- Random matrix generation ----------------------------------------------------

-- | /mpf_mat_randtest/ /mat/ /state/ /bits/ 
-- 
-- Sets the entries of @mat@ to random numbers in the interval \([0, 1)\)
-- with @bits@ significant bits in the mantissa or less if their precision
-- is smaller.
foreign import ccall "mpf_mat.h mpf_mat_randtest"
  mpf_mat_randtest :: Ptr CMpfMat -> Ptr CFRandState -> CFBitCnt -> IO ()

-- Input and output ------------------------------------------------------------

-- | /mpf_mat_print/ /mat/ 
-- 
-- Prints the given matrix to the stream @stdout@.
foreign import ccall "mpf_mat.h mpf_mat_print"
  mpf_mat_print :: Ptr CMpfMat -> IO ()

-- Comparison ------------------------------------------------------------------

-- | /mpf_mat_equal/ /mat1/ /mat2/ 
-- 
-- Returns a non-zero value if @mat1@ and @mat2@ have the same dimensions
-- and entries, and zero otherwise.
foreign import ccall "mpf_mat.h mpf_mat_equal"
  mpf_mat_equal :: Ptr CMpfMat -> Ptr CMpfMat -> IO CInt

-- | /mpf_mat_approx_equal/ /mat1/ /mat2/ /bits/ 
-- 
-- Returns a non-zero value if @mat1@ and @mat2@ have the same dimensions
-- and the first @bits@ bits of their entries are equal, and zero
-- otherwise.
foreign import ccall "mpf_mat.h mpf_mat_approx_equal"
  mpf_mat_approx_equal :: Ptr CMpfMat -> Ptr CMpfMat -> CFBitCnt -> IO CInt

-- | /mpf_mat_is_zero/ /mat/ 
-- 
-- Returns a non-zero value if all entries @mat@ are zero, and otherwise
-- returns zero.
foreign import ccall "mpf_mat.h mpf_mat_is_zero"
  mpf_mat_is_zero :: Ptr CMpfMat -> IO CInt

-- | /mpf_mat_is_empty/ /mat/ 
-- 
-- Returns a non-zero value if the number of rows or the number of columns
-- in @mat@ is zero, and otherwise returns zero.
foreign import ccall "mpf_mat.h mpf_mat_is_empty"
  mpf_mat_is_empty :: Ptr CMpfMat -> IO CInt

-- | /mpf_mat_is_square/ /mat/ 
-- 
-- Returns a non-zero value if the number of rows is equal to the number of
-- columns in @mat@, and otherwise returns zero.
foreign import ccall "mpf_mat.h mpf_mat_is_square"
  mpf_mat_is_square :: Ptr CMpfMat -> IO CInt

-- Matrix multiplication -------------------------------------------------------

-- | /mpf_mat_mul/ /C/ /A/ /B/ 
-- 
-- Sets @C@ to the matrix product \(C = A B\). The matrices must have
-- compatible dimensions for matrix multiplication (an exception is raised
-- otherwise). Aliasing is allowed.
foreign import ccall "mpf_mat.h mpf_mat_mul"
  mpf_mat_mul :: Ptr CMpfMat -> Ptr CMpfMat -> Ptr CMpfMat -> IO ()

-- Gram-Schmidt Orthogonalisation and QR Decomposition -------------------------

-- | /mpf_mat_gso/ /B/ /A/ 
-- 
-- Takes a subset of \(R^m\) \(S = {a_1, a_2, \ldots ,a_n}\) (as the
-- columns of a \(m x n\) matrix @A@) and generates an orthonormal set
-- \(S' = {b_1, b_2, \ldots ,b_n}\) (as the columns of the \(m x n\) matrix
-- @B@) that spans the same subspace of \(R^m\) as \(S\).
-- 
-- This uses an algorithm of Schwarz-Rutishauser. See pp. 9 of
-- <https://people.inf.ethz.ch/gander/papers/qrneu.pdf>
foreign import ccall "mpf_mat.h mpf_mat_gso"
  mpf_mat_gso :: Ptr CMpfMat -> Ptr CMpfMat -> IO ()

-- | /mpf_mat_qr/ /Q/ /R/ /A/ 
-- 
-- Computes the \(QR\) decomposition of a matrix @A@ using the Gram-Schmidt
-- process. (Sets @Q@ and @R@ such that \(A = QR\) where @R@ is an upper
-- triangular matrix and @Q@ is an orthogonal matrix.)
-- 
-- This uses an algorithm of Schwarz-Rutishauser. See pp. 9 of
-- <https://people.inf.ethz.ch/gander/papers/qrneu.pdf>
foreign import ccall "mpf_mat.h mpf_mat_qr"
  mpf_mat_qr :: Ptr CMpfMat -> Ptr CMpfMat -> Ptr CMpfMat -> IO ()

