module Data.Number.Flint.Support.D.Mat.FFI (
  -- * Double precision matrices
    DMat (..)
  , CDMat (..)
  , newDMat
  , withDMat
  , withNewDMat
  -- * Memory management
  , d_mat_init
  , d_mat_clear
  -- * Basic assignment and manipulation
  , d_mat_set
  , d_mat_swap
  , d_mat_swap_entrywise
  , d_mat_entry
  , d_mat_get_entry
  , d_mat_entry_ptr
  , d_mat_zero
  , d_mat_one
  -- * Random matrix generation
  , d_mat_randtest
  -- * Input and output
  , d_mat_print
  -- * Comparison
  , d_mat_equal
  , d_mat_approx_equal
  , d_mat_is_zero
  , d_mat_is_approx_zero
  , d_mat_is_empty
  , d_mat_is_square
  -- * Transpose
  , d_mat_transpose
  -- * Matrix multiplication
  , d_mat_mul_classical
  -- * Gram-Schmidt Orthogonalisation and QR Decomposition
  , d_mat_gso
  , d_mat_qr
) where 

-- double precision matrices ---------------------------------------------------

import Foreign.C.Types
import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.Storable
import Foreign.Marshal.Array

import Data.Number.Flint.Flint

#include <flint/d_mat.h>

-- d_mat_t ---------------------------------------------------------------------

data DMat = DMat {-# UNPACK #-} !(ForeignPtr CDMat)
data CDMat = CDMat (Ptr CDouble) CLong CLong (Ptr (Ptr CDouble))

instance Storable CDMat where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size d_mat_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment d_mat_t}
  peek ptr = CDMat
    <$> #{peek d_mat_struct, entries} ptr
    <*> #{peek d_mat_struct, r      } ptr
    <*> #{peek d_mat_struct, c      } ptr
    <*> #{peek d_mat_struct, rows   } ptr
  poke = error "CDMat.poke: Not defined."

newDMat rows cols = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> d_mat_init x rows cols
  addForeignPtrFinalizer p_d_mat_clear x
  return $ DMat x

{-# INLINE withDMat #-}
withDMat (DMat x) f = do
  withForeignPtr x $ \px -> f px >>= return . (DMat x,)

withNewDMat rows cols f = do
  x <- newDMat rows cols
  withDMat x f
  
-- Memory management -----------------------------------------------------------

-- | /d_mat_init/ /mat/ /rows/ /cols/ 
-- 
-- Initialises a matrix with the given number of rows and columns for use.
foreign import ccall "d_mat.h d_mat_init"
  d_mat_init :: Ptr CDMat -> CLong -> CLong -> IO ()

-- | /d_mat_clear/ /mat/ 
-- 
-- Clears the given matrix.
foreign import ccall "d_mat.h d_mat_clear"
  d_mat_clear :: Ptr CDMat -> IO ()

foreign import ccall "d_mat.h &d_mat_clear"
  p_d_mat_clear :: FunPtr (Ptr CDMat -> IO ())

-- Basic assignment and manipulation -------------------------------------------

-- | /d_mat_set/ /mat1/ /mat2/ 
-- 
-- Sets @mat1@ to a copy of @mat2@. The dimensions of @mat1@ and @mat2@
-- must be the same.
foreign import ccall "d_mat.h d_mat_set"
  d_mat_set :: Ptr CDMat -> Ptr CDMat -> IO ()

-- | /d_mat_swap/ /mat1/ /mat2/ 
-- 
-- Swaps two matrices. The dimensions of @mat1@ and @mat2@ are allowed to
-- be different.
foreign import ccall "d_mat.h d_mat_swap"
  d_mat_swap :: Ptr CDMat -> Ptr CDMat -> IO ()

-- | /d_mat_swap_entrywise/ /mat1/ /mat2/ 
-- 
-- Swaps two matrices by swapping the individual entries rather than
-- swapping the contents of the structs.
foreign import ccall "d_mat.h d_mat_swap_entrywise"
  d_mat_swap_entrywise :: Ptr CDMat -> Ptr CDMat -> IO ()

-- | /d_mat_entry/ /mat/ /i/ /j/ 
-- 
-- Returns the entry of @mat@ at row \(i\) and column \(j\). Both \(i\) and
-- \(j\) must not exceed the dimensions of the matrix. This function is
-- implemented as a macro.
d_mat_entry :: Ptr CDMat -> CLong -> CLong -> IO CDouble
d_mat_entry mat i j = do
  CDMat _ r c rows <- peek mat
  row_i <- peek (rows `advancePtr` (fromIntegral i))
  result <- peek (row_i `advancePtr` (fromIntegral j))
  return result
  
-- | /d_mat_get_entry/ /mat/ /i/ /j/ 
-- 
-- Returns the entry of @mat@ at row \(i\) and column \(j\). Both \(i\) and
-- \(j\) must not exceed the dimensions of the matrix.
foreign import ccall "d_mat.h d_mat_get_entry"
  d_mat_get_entry :: Ptr CDMat -> CLong -> CLong -> IO CDouble

-- | /d_mat_entry_ptr/ /mat/ /i/ /j/ 
-- 
-- Returns a pointer to the entry of @mat@ at row \(i\) and column \(j\).
-- Both \(i\) and \(j\) must not exceed the dimensions of the matrix.
foreign import ccall "d_mat.h d_mat_entry_ptr"
  d_mat_entry_ptr :: Ptr CDMat -> CLong -> CLong -> IO (Ptr CDouble)

-- | /d_mat_zero/ /mat/ 
-- 
-- Sets all entries of @mat@ to 0.
foreign import ccall "d_mat.h d_mat_zero"
  d_mat_zero :: Ptr CDMat -> IO ()

-- | /d_mat_one/ /mat/ 
-- 
-- Sets @mat@ to the unit matrix, having ones on the main diagonal and
-- zeroes elsewhere. If @mat@ is nonsquare, it is set to the truncation of
-- a unit matrix.
foreign import ccall "d_mat.h d_mat_one"
  d_mat_one :: Ptr CDMat -> IO ()

-- Random matrix generation ----------------------------------------------------

-- | /d_mat_randtest/ /mat/ /state/ /minexp/ /maxexp/ 
-- 
-- Sets the entries of @mat@ to random signed numbers with exponents
-- between @minexp@ and @maxexp@ or zero.
foreign import ccall "d_mat.h d_mat_randtest"
  d_mat_randtest :: Ptr CDMat -> Ptr CFRandState -> CLong -> CLong -> IO ()

-- Input and output ------------------------------------------------------------

-- | /d_mat_print/ /mat/ 
-- 
-- Prints the given matrix to the stream @stdout@.
foreign import ccall "d_mat.h d_mat_print"
  d_mat_print :: Ptr CDMat -> IO ()

-- Comparison ------------------------------------------------------------------

-- | /d_mat_equal/ /mat1/ /mat2/ 
-- 
-- Returns a non-zero value if @mat1@ and @mat2@ have the same dimensions
-- and entries, and zero otherwise.
foreign import ccall "d_mat.h d_mat_equal"
  d_mat_equal :: Ptr CDMat -> Ptr CDMat -> IO CInt

-- | /d_mat_approx_equal/ /mat1/ /mat2/ /eps/ 
-- 
-- Returns a non-zero value if @mat1@ and @mat2@ have the same dimensions
-- and entries within @eps@ of each other, and zero otherwise.
foreign import ccall "d_mat.h d_mat_approx_equal"
  d_mat_approx_equal :: Ptr CDMat -> Ptr CDMat -> CDouble -> IO CInt

-- | /d_mat_is_zero/ /mat/ 
-- 
-- Returns a non-zero value if all entries @mat@ are zero, and otherwise
-- returns zero.
foreign import ccall "d_mat.h d_mat_is_zero"
  d_mat_is_zero :: Ptr CDMat -> IO CInt

-- | /d_mat_is_approx_zero/ /mat/ /eps/ 
-- 
-- Returns a non-zero value if all entries @mat@ are zero to within @eps@
-- and otherwise returns zero.
foreign import ccall "d_mat.h d_mat_is_approx_zero"
  d_mat_is_approx_zero :: Ptr CDMat -> CDouble -> IO CInt

-- | /d_mat_is_empty/ /mat/ 
-- 
-- Returns a non-zero value if the number of rows or the number of columns
-- in @mat@ is zero, and otherwise returns zero.
foreign import ccall "d_mat.h d_mat_is_empty"
  d_mat_is_empty :: Ptr CDMat -> IO CInt

-- | /d_mat_is_square/ /mat/ 
-- 
-- Returns a non-zero value if the number of rows is equal to the number of
-- columns in @mat@, and otherwise returns zero.
foreign import ccall "d_mat.h d_mat_is_square"
  d_mat_is_square :: Ptr CDMat -> IO CInt

-- Transpose -------------------------------------------------------------------

-- | /d_mat_transpose/ /B/ /A/ 
-- 
-- Sets \(B\) to \(A^T\), the transpose of \(A\). Dimensions must be
-- compatible. \(A\) and \(B\) are allowed to be the same object if \(A\)
-- is a square matrix.
foreign import ccall "d_mat.h d_mat_transpose"
  d_mat_transpose :: Ptr CDMat -> Ptr CDMat -> IO ()

-- Matrix multiplication -------------------------------------------------------

-- | /d_mat_mul_classical/ /C/ /A/ /B/ 
-- 
-- Sets @C@ to the matrix product \(C = A B\). The matrices must have
-- compatible dimensions for matrix multiplication (an exception is raised
-- otherwise). Aliasing is allowed.
foreign import ccall "d_mat.h d_mat_mul_classical"
  d_mat_mul_classical :: Ptr CDMat -> Ptr CDMat -> Ptr CDMat -> IO ()

-- Gram-Schmidt Orthogonalisation and QR Decomposition -------------------------

-- | /d_mat_gso/ /B/ /A/ 
-- 
-- Takes a subset of \(R^m\) \(S = {a_1, a_2, \ldots, a_n}\) (as the
-- columns of a \(m x n\) matrix @A@) and generates an orthonormal set
-- \(S' = {b_1, b_2, \ldots, b_n}\) (as the columns of the \(m x n\) matrix
-- @B@) that spans the same subspace of \(R^m\) as \(S\).
-- 
-- This uses an algorithm of Schwarz-Rutishauser. See pp. 9 of
-- <https://people.inf.ethz.ch/gander/papers/qrneu.pdf>
foreign import ccall "d_mat.h d_mat_gso"
  d_mat_gso :: Ptr CDMat -> Ptr CDMat -> IO ()

-- | /d_mat_qr/ /Q/ /R/ /A/ 
-- 
-- Computes the \(QR\) decomposition of a matrix @A@ using the Gram-Schmidt
-- process. (Sets @Q@ and @R@ such that \(A = QR\) where @R@ is an upper
-- triangular matrix and @Q@ is an orthogonal matrix.)
-- 
-- This uses an algorithm of Schwarz-Rutishauser. See pp. 9 of
-- <https://people.inf.ethz.ch/gander/papers/qrneu.pdf>
foreign import ccall "d_mat.h d_mat_qr"
  d_mat_qr :: Ptr CDMat -> Ptr CDMat -> Ptr CDMat -> IO ()

