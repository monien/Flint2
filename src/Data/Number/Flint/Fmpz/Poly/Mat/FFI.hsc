module Data.Number.Flint.Fmpz.Poly.Mat.FFI (
  -- * Matrices of polynomials over the integers
    FmpzPolyMat (..)
  , CFmpzPolyMat (..)
  , newFmpzPolyMat
  , withFmpzPolyMat
  , withNewFmpzPolyMat
  -- * Memory management
  , fmpz_poly_mat_init
  , fmpz_poly_mat_init_set
  , fmpz_poly_mat_clear
  -- * Basic properties
  , fmpz_poly_mat_nrows
  , fmpz_poly_mat_ncols
  -- * Basic assignment and manipulation
  , fmpz_poly_mat_entry
  , fmpz_poly_mat_set
  , fmpz_poly_mat_swap
  , fmpz_poly_mat_swap_entrywise
  -- * Input and output
  , fmpz_poly_mat_print
  -- * Random matrix generation
  , fmpz_poly_mat_randtest
  , fmpz_poly_mat_randtest_unsigned
  , fmpz_poly_mat_randtest_sparse
  -- * Special matrices
  , fmpz_poly_mat_zero
  , fmpz_poly_mat_one
  -- * Basic comparison and properties
  , fmpz_poly_mat_equal
  , fmpz_poly_mat_is_zero
  , fmpz_poly_mat_is_one
  , fmpz_poly_mat_is_empty
  , fmpz_poly_mat_is_square
  -- * Norms
  , fmpz_poly_mat_max_bits
  , fmpz_poly_mat_max_length
  -- * Transpose
  , fmpz_poly_mat_transpose
  -- * Evaluation
  , fmpz_poly_mat_evaluate_fmpz
  -- * Arithmetic
  , fmpz_poly_mat_scalar_mul_fmpz_poly
  , fmpz_poly_mat_scalar_mul_fmpz
  , fmpz_poly_mat_add
  , fmpz_poly_mat_sub
  , fmpz_poly_mat_neg
  , fmpz_poly_mat_mul
  , fmpz_poly_mat_mul_classical
  , fmpz_poly_mat_mul_KS
  , fmpz_poly_mat_mullow
  , fmpz_poly_mat_sqr
  , fmpz_poly_mat_sqr_classical
  , fmpz_poly_mat_sqr_KS
  , fmpz_poly_mat_sqrlow
  , fmpz_poly_mat_pow
  , fmpz_poly_mat_pow_trunc
  , fmpz_poly_mat_prod
  -- * Row reduction
  , fmpz_poly_mat_find_pivot_any
  , fmpz_poly_mat_find_pivot_partial
  , fmpz_poly_mat_fflu
  , fmpz_poly_mat_rref
  -- * Trace
  , fmpz_poly_mat_trace
  -- * Determinant and rank
  , fmpz_poly_mat_det
  , fmpz_poly_mat_det_fflu
  , fmpz_poly_mat_det_interpolate
  , fmpz_poly_mat_rank
  -- * Inverse
  , fmpz_poly_mat_inv
  -- * Nullspace
  , fmpz_poly_mat_nullspace
  -- * Solving
  , fmpz_poly_mat_solve
  , fmpz_poly_mat_solve_fflu
  , fmpz_poly_mat_solve_fflu_precomp
) where

-- Matrices of polynomials over the integers -----------------------------------

import System.IO.Unsafe

import Control.Monad

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, nullPtr, plusPtr )
import Foreign.Storable
import Foreign.Marshal ( free )
import Foreign.Marshal.Array ( advancePtr )

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Poly
import Data.Number.Flint.Fmpz.Mat
import Data.Number.Flint.Fmpq
import Data.Number.Flint.NMod.Types
import Data.Number.Flint.Support.D.Mat
import Data.Number.Flint.Support.Mpf.Mat

#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpz_mat.h>
#include <flint/fmpz_poly.h>
#include <flint/fmpz_poly_mat.h>
#include <flint/fmpq.h>

-- fmpz_poly_mat_t -------------------------------------------------------------

data FmpzPolyMat = FmpzPolyMat {-# UNPACK #-} !(ForeignPtr CFmpzPolyMat) 
data CFmpzPolyMat = CFmpzPolyMat (Ptr CFmpzPoly) CLong CLong (Ptr (Ptr CFmpzPoly)) 

instance Storable CFmpzPolyMat where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fmpz_poly_mat_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fmpz_poly_mat_t}
  peek ptr = CFmpzPolyMat
    <$> #{peek fmpz_poly_mat_struct, entries} ptr
    <*> #{peek fmpz_poly_mat_struct, r      } ptr
    <*> #{peek fmpz_poly_mat_struct, c      } ptr
    <*> #{peek fmpz_poly_mat_struct, rows   } ptr
  poke = error "CFmpzPolyMat.poke: Not defined."
 
newFmpzPolyMat rows cols = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> fmpz_poly_mat_init x rows cols
  addForeignPtrFinalizer p_fmpz_poly_mat_clear x
  return $ FmpzPolyMat x

{-# INLINE withFmpzPolyMat #-}
withFmpzPolyMat (FmpzPolyMat x) f = do
  withForeignPtr x $ \px -> f px >>= return . (FmpzPolyMat x,)

{-# INLINE withNewFmpzPolyMat #-}
withNewFmpzPolyMat rows cols f = do
  x <- newFmpzPolyMat rows cols
  withFmpzPolyMat x f
  
-- Memory management -----------------------------------------------------------

-- | /fmpz_poly_mat_init/ /mat/ /rows/ /cols/ 
--
-- Initialises a matrix with the given number of rows and columns for use.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_init"
  fmpz_poly_mat_init :: Ptr CFmpzPolyMat -> CLong -> CLong -> IO ()

-- | /fmpz_poly_mat_init_set/ /mat/ /src/ 
--
-- Initialises a matrix @mat@ of the same dimensions as @src@, and sets it
-- to a copy of @src@.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_init_set"
  fmpz_poly_mat_init_set :: Ptr CFmpzPolyMat -> Ptr CFmpzPolyMat -> IO ()

-- | /fmpz_poly_mat_clear/ /mat/ 
--
-- Frees all memory associated with the matrix. The matrix must be
-- reinitialised if it is to be used again.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_clear"
  fmpz_poly_mat_clear :: Ptr CFmpzPolyMat -> IO ()

foreign import ccall "fmpz_poly_mat.h &fmpz_poly_mat_clear"
  p_fmpz_poly_mat_clear :: FunPtr (Ptr CFmpzPolyMat -> IO ())

-- Basic properties ------------------------------------------------------------

-- | /fmpz_poly_mat_nrows/ /mat/ 
--
-- Returns the number of rows in @mat@.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_nrows"
  fmpz_poly_mat_nrows :: Ptr CFmpzPolyMat -> IO CLong

-- | /fmpz_poly_mat_ncols/ /mat/ 
--
-- Returns the number of columns in @mat@.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_ncols"
  fmpz_poly_mat_ncols :: Ptr CFmpzPolyMat -> IO CLong

-- Basic assignment and manipulation -------------------------------------------

-- | /fmpz_poly_mat_entry/ /mat/ /i/ /j/ 
--
-- Gives a reference to the entry at row @i@ and column @j@. The reference
-- can be passed as an input or output variable to any @fmpz_poly@ function
-- for direct manipulation of the matrix element. No bounds checking is
-- performed.
fmpz_poly_mat_entry :: Ptr CFmpzPolyMat -> CLong -> CLong -> IO (Ptr CFmpzPoly)
fmpz_poly_mat_entry mat i j = do
  CFmpzPolyMat entries r c rows <- peek mat
  return $ entries `advancePtr` (fromIntegral (i*c+j))
  
-- | /fmpz_poly_mat_set/ /mat1/ /mat2/ 
--
-- Sets @mat1@ to a copy of @mat2@.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_set"
  fmpz_poly_mat_set :: Ptr CFmpzPolyMat -> Ptr CFmpzPolyMat -> IO ()

-- | /fmpz_poly_mat_swap/ /mat1/ /mat2/ 
--
-- Swaps @mat1@ and @mat2@ efficiently.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_swap"
  fmpz_poly_mat_swap :: Ptr CFmpzPolyMat -> Ptr CFmpzPolyMat -> IO ()

-- | /fmpz_poly_mat_swap_entrywise/ /mat1/ /mat2/ 
--
-- Swaps two matrices by swapping the individual entries rather than
-- swapping the contents of the structs.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_swap_entrywise"
  fmpz_poly_mat_swap_entrywise :: Ptr CFmpzPolyMat -> Ptr CFmpzPolyMat -> IO ()

-- Input and output ------------------------------------------------------------

foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_fprint"
  fmpz_poly_mat_fprint :: Ptr CFile -> Ptr CFmpzPolyMat -> CString -> IO ()

foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_get_str"
  fmpz_poly_mat_get_str :: Ptr CFmpzPolyMat -> CString -> IO CString
  
-- | /fmpz_poly_mat_print/ /mat/ /x/ 
--
-- Prints the matrix @mat@ to standard output, using the variable @x@.
fmpz_poly_mat_print :: Ptr CFmpzPolyMat -> CString -> IO ()
fmpz_poly_mat_print mat x = do
  printCStr (\mat -> fmpz_poly_mat_get_str mat x) mat
  return ()

-- Random matrix generation ----------------------------------------------------

-- | /fmpz_poly_mat_randtest/ /mat/ /state/ /len/ /bits/ 
--
-- This is equivalent to applying @fmpz_poly_randtest@ to all entries in
-- the matrix.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_randtest"
  fmpz_poly_mat_randtest :: Ptr CFmpzPolyMat -> Ptr CFRandState -> CLong -> CFBitCnt -> IO ()

-- | /fmpz_poly_mat_randtest_unsigned/ /mat/ /state/ /len/ /bits/ 
--
-- This is equivalent to applying @fmpz_poly_randtest_unsigned@ to all
-- entries in the matrix.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_randtest_unsigned"
  fmpz_poly_mat_randtest_unsigned :: Ptr CFmpzPolyMat -> Ptr CFRandState -> CLong -> CFBitCnt -> IO ()

-- | /fmpz_poly_mat_randtest_sparse/ /A/ /state/ /len/ /bits/ /density/ 
--
-- Creates a random matrix with the amount of nonzero entries given
-- approximately by the @density@ variable, which should be a fraction
-- between 0 (most sparse) and 1 (most dense).
-- 
-- The nonzero entries will have random lengths between 1 and @len@.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_randtest_sparse"
  fmpz_poly_mat_randtest_sparse :: Ptr CFmpzPolyMat -> Ptr CFRandState -> CLong -> CFBitCnt -> CFloat -> IO ()

-- Special matrices ------------------------------------------------------------

-- | /fmpz_poly_mat_zero/ /mat/ 
--
-- Sets @mat@ to the zero matrix.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_zero"
  fmpz_poly_mat_zero :: Ptr CFmpzPolyMat -> IO ()

-- | /fmpz_poly_mat_one/ /mat/ 
--
-- Sets @mat@ to the unit or identity matrix of given shape, having the
-- element 1 on the main diagonal and zeros elsewhere. If @mat@ is
-- nonsquare, it is set to the truncation of a unit matrix.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_one"
  fmpz_poly_mat_one :: Ptr CFmpzPolyMat -> IO ()

-- Basic comparison and properties ---------------------------------------------

-- | /fmpz_poly_mat_equal/ /mat1/ /mat2/ 
--
-- Returns nonzero if @mat1@ and @mat2@ have the same shape and all their
-- entries agree, and returns zero otherwise.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_equal"
  fmpz_poly_mat_equal :: Ptr CFmpzPolyMat -> Ptr CFmpzPolyMat -> IO CInt

-- | /fmpz_poly_mat_is_zero/ /mat/ 
--
-- Returns nonzero if all entries in @mat@ are zero, and returns zero
-- otherwise.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_is_zero"
  fmpz_poly_mat_is_zero :: Ptr CFmpzPolyMat -> IO CInt

-- | /fmpz_poly_mat_is_one/ /mat/ 
--
-- Returns nonzero if all entries of @mat@ on the main diagonal are the
-- constant polynomial 1 and all remaining entries are zero, and returns
-- zero otherwise. The matrix need not be square.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_is_one"
  fmpz_poly_mat_is_one :: Ptr CFmpzPolyMat -> IO CInt

-- | /fmpz_poly_mat_is_empty/ /mat/ 
--
-- Returns a non-zero value if the number of rows or the number of columns
-- in @mat@ is zero, and otherwise returns zero.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_is_empty"
  fmpz_poly_mat_is_empty :: Ptr CFmpzPolyMat -> IO CInt

-- | /fmpz_poly_mat_is_square/ /mat/ 
--
-- Returns a non-zero value if the number of rows is equal to the number of
-- columns in @mat@, and otherwise returns zero.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_is_square"
  fmpz_poly_mat_is_square :: Ptr CFmpzPolyMat -> IO CInt

-- Norms -----------------------------------------------------------------------

-- | /fmpz_poly_mat_max_bits/ /A/ 
--
-- Returns the maximum number of bits among the coefficients of the entries
-- in @A@, or the negative of that value if any coefficient is negative.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_max_bits"
  fmpz_poly_mat_max_bits :: Ptr CFmpzPolyMat -> IO CLong

-- | /fmpz_poly_mat_max_length/ /A/ 
--
-- Returns the maximum polynomial length among all the entries in @A@.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_max_length"
  fmpz_poly_mat_max_length :: Ptr CFmpzPolyMat -> IO CLong

-- Transpose -------------------------------------------------------------------

-- | /fmpz_poly_mat_transpose/ /B/ /A/ 
--
-- Sets \(B\) to \(A^t\).
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_transpose"
  fmpz_poly_mat_transpose :: Ptr CFmpzPolyMat -> Ptr CFmpzPolyMat -> IO ()

-- Evaluation ------------------------------------------------------------------

-- | /fmpz_poly_mat_evaluate_fmpz/ /B/ /A/ /x/ 
--
-- Sets the @fmpz_mat_t@ @B@ to @A@ evaluated entrywise at the point @x@.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_evaluate_fmpz"
  fmpz_poly_mat_evaluate_fmpz :: Ptr CFmpzMat -> Ptr CFmpzPolyMat -> Ptr CFmpz -> IO ()

-- Arithmetic ------------------------------------------------------------------

-- | /fmpz_poly_mat_scalar_mul_fmpz_poly/ /B/ /A/ /c/ 
--
-- Sets @B@ to @A@ multiplied entrywise by the polynomial @c@.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_scalar_mul_fmpz_poly"
  fmpz_poly_mat_scalar_mul_fmpz_poly :: Ptr CFmpzPolyMat -> Ptr CFmpzPolyMat -> Ptr CFmpzPoly -> IO ()

-- | /fmpz_poly_mat_scalar_mul_fmpz/ /B/ /A/ /c/ 
--
-- Sets @B@ to @A@ multiplied entrywise by the integer @c@.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_scalar_mul_fmpz"
  fmpz_poly_mat_scalar_mul_fmpz :: Ptr CFmpzPolyMat -> Ptr CFmpzPolyMat -> Ptr CFmpz -> IO ()

-- | /fmpz_poly_mat_add/ /C/ /A/ /B/ 
--
-- Sets @C@ to the sum of @A@ and @B@. All matrices must have the same
-- shape. Aliasing is allowed.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_add"
  fmpz_poly_mat_add :: Ptr CFmpzPolyMat -> Ptr CFmpzPolyMat -> Ptr CFmpzPolyMat -> IO ()

-- | /fmpz_poly_mat_sub/ /C/ /A/ /B/ 
--
-- Sets @C@ to the sum of @A@ and @B@. All matrices must have the same
-- shape. Aliasing is allowed.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_sub"
  fmpz_poly_mat_sub :: Ptr CFmpzPolyMat -> Ptr CFmpzPolyMat -> Ptr CFmpzPolyMat -> IO ()

-- | /fmpz_poly_mat_neg/ /B/ /A/ 
--
-- Sets @B@ to the negation of @A@. The matrices must have the same shape.
-- Aliasing is allowed.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_neg"
  fmpz_poly_mat_neg :: Ptr CFmpzPolyMat -> Ptr CFmpzPolyMat -> IO ()

-- | /fmpz_poly_mat_mul/ /C/ /A/ /B/ 
--
-- Sets @C@ to the matrix product of @A@ and @B@. The matrices must have
-- compatible dimensions for matrix multiplication. Aliasing is allowed.
-- This function automatically chooses between classical and KS
-- multiplication.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_mul"
  fmpz_poly_mat_mul :: Ptr CFmpzPolyMat -> Ptr CFmpzPolyMat -> Ptr CFmpzPolyMat -> IO ()

-- | /fmpz_poly_mat_mul_classical/ /C/ /A/ /B/ 
--
-- Sets @C@ to the matrix product of @A@ and @B@, computed using the
-- classical algorithm. The matrices must have compatible dimensions for
-- matrix multiplication. Aliasing is allowed.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_mul_classical"
  fmpz_poly_mat_mul_classical :: Ptr CFmpzPolyMat -> Ptr CFmpzPolyMat -> Ptr CFmpzPolyMat -> IO ()

-- | /fmpz_poly_mat_mul_KS/ /C/ /A/ /B/ 
--
-- Sets @C@ to the matrix product of @A@ and @B@, computed using Kronecker
-- segmentation. The matrices must have compatible dimensions for matrix
-- multiplication. Aliasing is allowed.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_mul_KS"
  fmpz_poly_mat_mul_KS :: Ptr CFmpzPolyMat -> Ptr CFmpzPolyMat -> Ptr CFmpzPolyMat -> IO ()

-- | /fmpz_poly_mat_mullow/ /C/ /A/ /B/ /len/ 
--
-- Sets @C@ to the matrix product of @A@ and @B@, truncating each entry in
-- the result to length @len@. Uses classical matrix multiplication. The
-- matrices must have compatible dimensions for matrix multiplication.
-- Aliasing is allowed.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_mullow"
  fmpz_poly_mat_mullow :: Ptr CFmpzPolyMat -> Ptr CFmpzPolyMat -> Ptr CFmpzPolyMat -> CLong -> IO ()

-- | /fmpz_poly_mat_sqr/ /B/ /A/ 
--
-- Sets @B@ to the square of @A@, which must be a square matrix. Aliasing
-- is allowed. This function automatically chooses between classical and KS
-- squaring.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_sqr"
  fmpz_poly_mat_sqr :: Ptr CFmpzPolyMat -> Ptr CFmpzPolyMat -> IO ()

-- | /fmpz_poly_mat_sqr_classical/ /B/ /A/ 
--
-- Sets @B@ to the square of @A@, which must be a square matrix. Aliasing
-- is allowed. This function uses direct formulas for very small matrices,
-- and otherwise classical matrix multiplication.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_sqr_classical"
  fmpz_poly_mat_sqr_classical :: Ptr CFmpzPolyMat -> Ptr CFmpzPolyMat -> IO ()

-- | /fmpz_poly_mat_sqr_KS/ /B/ /A/ 
--
-- Sets @B@ to the square of @A@, which must be a square matrix. Aliasing
-- is allowed. This function uses Kronecker segmentation.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_sqr_KS"
  fmpz_poly_mat_sqr_KS :: Ptr CFmpzPolyMat -> Ptr CFmpzPolyMat -> IO ()

-- | /fmpz_poly_mat_sqrlow/ /B/ /A/ /len/ 
--
-- Sets @B@ to the square of @A@, which must be a square matrix, truncating
-- all entries to length @len@. Aliasing is allowed. This function uses
-- direct formulas for very small matrices, and otherwise classical matrix
-- multiplication.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_sqrlow"
  fmpz_poly_mat_sqrlow :: Ptr CFmpzPolyMat -> Ptr CFmpzPolyMat -> CLong -> IO ()

-- | /fmpz_poly_mat_pow/ /B/ /A/ /exp/ 
--
-- Sets @B@ to @A@ raised to the power @exp@, where @A@ is a square matrix.
-- Uses exponentiation by squaring. Aliasing is allowed.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_pow"
  fmpz_poly_mat_pow :: Ptr CFmpzPolyMat -> Ptr CFmpzPolyMat -> CULong -> IO ()

-- | /fmpz_poly_mat_pow_trunc/ /B/ /A/ /exp/ /len/ 
--
-- Sets @B@ to @A@ raised to the power @exp@, truncating all entries to
-- length @len@, where @A@ is a square matrix. Uses exponentiation by
-- squaring. Aliasing is allowed.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_pow_trunc"
  fmpz_poly_mat_pow_trunc :: Ptr CFmpzPolyMat -> Ptr CFmpzPolyMat -> CULong -> CLong -> IO ()

-- | /fmpz_poly_mat_prod/ /res/ /factors/ /n/ 
--
-- Sets @res@ to the product of the @n@ matrices given in the vector
-- @factors@, all of which must be square and of the same size. Uses binary
-- splitting.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_prod"
  fmpz_poly_mat_prod :: Ptr CFmpzPolyMat -> Ptr (Ptr CFmpzPolyMat) -> CLong -> IO ()

-- Row reduction ---------------------------------------------------------------

-- | /fmpz_poly_mat_find_pivot_any/ /mat/ /start_row/ /end_row/ /c/ 
--
-- Attempts to find a pivot entry for row reduction. Returns a row index
-- \(r\) between @start_row@ (inclusive) and @stop_row@ (exclusive) such
-- that column \(c\) in @mat@ has a nonzero entry on row \(r\), or returns
-- -1 if no such entry exists.
-- 
-- This implementation simply chooses the first nonzero entry it
-- encounters. This is likely to be a nearly optimal choice if all entries
-- in the matrix have roughly the same size, but can lead to unnecessary
-- coefficient growth if the entries vary in size.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_find_pivot_any"
  fmpz_poly_mat_find_pivot_any :: Ptr CFmpzPolyMat -> CLong -> CLong -> CLong -> IO CLong

-- | /fmpz_poly_mat_find_pivot_partial/ /mat/ /start_row/ /end_row/ /c/ 
--
-- Attempts to find a pivot entry for row reduction. Returns a row index
-- \(r\) between @start_row@ (inclusive) and @stop_row@ (exclusive) such
-- that column \(c\) in @mat@ has a nonzero entry on row \(r\), or returns
-- -1 if no such entry exists.
-- 
-- This implementation searches all the rows in the column and chooses the
-- nonzero entry of smallest degree. If there are several entries with the
-- same minimal degree, it chooses the entry with the smallest coefficient
-- bit bound. This heuristic typically reduces coefficient growth when the
-- matrix entries vary in size.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_find_pivot_partial"
  fmpz_poly_mat_find_pivot_partial :: Ptr CFmpzPolyMat -> CLong -> CLong -> CLong -> IO CLong

-- | /fmpz_poly_mat_fflu/ /B/ /den/ /perm/ /A/ /rank_check/ 
--
-- Uses fraction-free Gaussian elimination to set (@B@, @den@) to a
-- fraction-free LU decomposition of @A@ and returns the rank of @A@.
-- Aliasing of @A@ and @B@ is allowed.
-- 
-- Pivot elements are chosen with @fmpz_poly_mat_find_pivot_partial@. If
-- @perm@ is non-@NULL@, the permutation of rows in the matrix will also be
-- applied to @perm@.
-- 
-- If @rank_check@ is set, the function aborts and returns 0 if the matrix
-- is detected not to have full rank without completing the elimination.
-- 
-- The denominator @den@ is set to \(\pm \operatorname{det}(A)\), where the
-- sign is decided by the parity of the permutation. Note that the
-- determinant is not generally the minimal denominator.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_fflu"
  fmpz_poly_mat_fflu :: Ptr CFmpzPolyMat -> Ptr CFmpzPoly -> Ptr CLong -> Ptr CFmpzPolyMat -> CInt -> IO CLong

-- | /fmpz_poly_mat_rref/ /B/ /den/ /A/ 
--
-- Sets (@B@, @den@) to the reduced row echelon form of @A@ and returns the
-- rank of @A@. Aliasing of @A@ and @B@ is allowed.
-- 
-- The denominator @den@ is set to \(\pm \operatorname{det}(A)\). Note that
-- the determinant is not generally the minimal denominator.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_rref"
  fmpz_poly_mat_rref :: Ptr CFmpzPolyMat -> Ptr CFmpzPoly -> Ptr CFmpzPolyMat -> IO CLong

-- Trace -----------------------------------------------------------------------

-- | /fmpz_poly_mat_trace/ /trace/ /mat/ 
--
-- Computes the trace of the matrix, i.e. the sum of the entries on the
-- main diagonal. The matrix is required to be square.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_trace"
  fmpz_poly_mat_trace :: Ptr CFmpzPoly -> Ptr CFmpzPolyMat -> IO ()

-- Determinant and rank --------------------------------------------------------

-- | /fmpz_poly_mat_det/ /det/ /A/ 
--
-- Sets @det@ to the determinant of the square matrix @A@. Uses a direct
-- formula, fraction-free LU decomposition, or interpolation, depending on
-- the size of the matrix.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_det"
  fmpz_poly_mat_det :: Ptr CFmpzPoly -> Ptr CFmpzPolyMat -> IO ()

-- | /fmpz_poly_mat_det_fflu/ /det/ /A/ 
--
-- Sets @det@ to the determinant of the square matrix @A@. The determinant
-- is computed by performing a fraction-free LU decomposition on a copy of
-- @A@.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_det_fflu"
  fmpz_poly_mat_det_fflu :: Ptr CFmpzPoly -> Ptr CFmpzPolyMat -> IO ()

-- | /fmpz_poly_mat_det_interpolate/ /det/ /A/ 
--
-- Sets @det@ to the determinant of the square matrix @A@. The determinant
-- is computed by determining a bound \(n\) for its length, evaluating the
-- matrix at \(n\) distinct points, computing the determinant of each
-- integer matrix, and forming the interpolating polynomial.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_det_interpolate"
  fmpz_poly_mat_det_interpolate :: Ptr CFmpzPoly -> Ptr CFmpzPolyMat -> IO ()

-- | /fmpz_poly_mat_rank/ /A/ 
--
-- Returns the rank of @A@. Performs fraction-free LU decomposition on a
-- copy of @A@.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_rank"
  fmpz_poly_mat_rank :: Ptr CFmpzPolyMat -> IO CLong

-- Inverse ---------------------------------------------------------------------

-- | /fmpz_poly_mat_inv/ /Ainv/ /den/ /A/ 
--
-- Sets (@Ainv@, @den@) to the inverse matrix of @A@. Returns 1 if @A@ is
-- nonsingular and 0 if @A@ is singular. Aliasing of @Ainv@ and @A@ is
-- allowed.
-- 
-- More precisely, @det@ will be set to the determinant of @A@ and @Ainv@
-- will be set to the adjugate matrix of @A@. Note that the determinant is
-- not necessarily the minimal denominator.
-- 
-- Uses fraction-free LU decomposition, followed by solving for the
-- identity matrix.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_inv"
  fmpz_poly_mat_inv :: Ptr CFmpzPolyMat -> Ptr CFmpzPoly -> Ptr CFmpzPolyMat -> IO CInt

-- Nullspace -------------------------------------------------------------------

-- | /fmpz_poly_mat_nullspace/ /res/ /mat/ 
--
-- Computes the right rational nullspace of the matrix @mat@ and returns
-- the nullity.
-- 
-- More precisely, assume that @mat@ has rank \(r\) and nullity \(n\). Then
-- this function sets the first \(n\) columns of @res@ to linearly
-- independent vectors spanning the nullspace of @mat@. As a result, we
-- always have rank(@res@) \(= n\), and @mat@ \(\times\) @res@ is the zero
-- matrix.
-- 
-- The computed basis vectors will not generally be in a reduced form. In
-- general, the polynomials in each column vector in the result will have a
-- nontrivial common GCD.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_nullspace"
  fmpz_poly_mat_nullspace :: Ptr CFmpzPolyMat -> Ptr CFmpzPolyMat -> IO CLong

-- Solving ---------------------------------------------------------------------

-- | /fmpz_poly_mat_solve/ /X/ /den/ /A/ /B/ 
--
-- Solves the equation \(AX = B\) for nonsingular \(A\). More precisely,
-- computes (@X@, @den@) such that \(AX = B \times \operatorname{den}\).
-- Returns 1 if \(A\) is nonsingular and 0 if \(A\) is singular. The
-- computed denominator will not generally be minimal.
-- 
-- Uses fraction-free LU decomposition followed by fraction-free forward
-- and back substitution.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_solve"
  fmpz_poly_mat_solve :: Ptr CFmpzPolyMat -> Ptr CFmpzPoly -> Ptr CFmpzPolyMat -> Ptr CFmpzPolyMat -> IO CInt

-- | /fmpz_poly_mat_solve_fflu/ /X/ /den/ /A/ /B/ 
--
-- Solves the equation \(AX = B\) for nonsingular \(A\). More precisely,
-- computes (@X@, @den@) such that \(AX = B \times \operatorname{den}\).
-- Returns 1 if \(A\) is nonsingular and 0 if \(A\) is singular. The
-- computed denominator will not generally be minimal.
-- 
-- Uses fraction-free LU decomposition followed by fraction-free forward
-- and back substitution.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_solve_fflu"
  fmpz_poly_mat_solve_fflu :: Ptr CFmpzPolyMat -> Ptr CFmpzPoly -> Ptr CFmpzPolyMat -> Ptr CFmpzPolyMat -> IO CInt

-- | /fmpz_poly_mat_solve_fflu_precomp/ /X/ /perm/ /FFLU/ /B/ 
--
-- Performs fraction-free forward and back substitution given a precomputed
-- fraction-free LU decomposition and corresponding permutation.
foreign import ccall "fmpz_poly_mat.h fmpz_poly_mat_solve_fflu_precomp"
  fmpz_poly_mat_solve_fflu_precomp :: Ptr CFmpzPolyMat -> Ptr CLong -> Ptr CFmpzPolyMat -> Ptr CFmpzPolyMat -> IO ()

