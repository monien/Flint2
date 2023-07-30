{-|
module      :  Data.Number.Flint.NMod.Poly.Mat.FFI
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de
-}
module Data.Number.Flint.NMod.Poly.Mat.FFI (
  -- * Matrices of univariate polynomials over integers mod n (word-size n)
    NModPolyMat (..)
  , CNModPolyMat (..)
  , newNModPolyMat
  , withNModPolyMat
  -- * Memory management
  , nmod_poly_mat_init
  , nmod_poly_mat_init_set
  , nmod_poly_mat_clear
  -- * Basic properties
  , nmod_poly_mat_nrows
  , nmod_poly_mat_ncols
  , nmod_poly_mat_modulus
  -- * Basic assignment and manipulation
  , nmod_poly_mat_entry
  , nmod_poly_mat_set
  , nmod_poly_mat_swap
  , nmod_poly_mat_swap_entrywise
  -- * Input and output
  , nmod_poly_mat_print
  -- * Random matrix generation
  , nmod_poly_mat_randtest
  , nmod_poly_mat_randtest_sparse
  -- * Special matrices
  , nmod_poly_mat_zero
  , nmod_poly_mat_one
  -- * Basic comparison and properties
  , nmod_poly_mat_equal
  , nmod_poly_mat_is_zero
  , nmod_poly_mat_is_one
  , nmod_poly_mat_is_empty
  , nmod_poly_mat_is_square
  -- * Norms
  , nmod_poly_mat_max_length
  -- * Evaluation
  , nmod_poly_mat_evaluate_nmod
  -- * Arithmetic
  , nmod_poly_mat_scalar_mul_nmod_poly
  , nmod_poly_mat_scalar_mul_nmod
  , nmod_poly_mat_add
  , nmod_poly_mat_sub
  , nmod_poly_mat_neg
  , nmod_poly_mat_mul
  , nmod_poly_mat_mul_classical
  , nmod_poly_mat_mul_KS
  , nmod_poly_mat_mul_interpolate
  , nmod_poly_mat_sqr
  , nmod_poly_mat_sqr_classical
  , nmod_poly_mat_sqr_KS
  , nmod_poly_mat_sqr_interpolate
  , nmod_poly_mat_pow
  -- * Row reduction
  , nmod_poly_mat_find_pivot_any
  , nmod_poly_mat_find_pivot_partial
  , nmod_poly_mat_fflu
  , nmod_poly_mat_rref
  -- * Trace
  , nmod_poly_mat_trace
  -- * Determinant and rank
  , nmod_poly_mat_det
  , nmod_poly_mat_det_fflu
  , nmod_poly_mat_det_interpolate
  , nmod_poly_mat_rank
  -- * Inverse
  , nmod_poly_mat_inv
  -- * Nullspace
  , nmod_poly_mat_nullspace
  -- * Solving
  , nmod_poly_mat_solve
  , nmod_poly_mat_solve_fflu
  , nmod_poly_mat_solve_fflu_precomp
) where 

-- Matrices of univariate polynomials over integers mod n (word-size n) --------

import Control.Monad

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr, castPtr )
import Foreign.Storable
import Foreign.Marshal ( free )
import Foreign.Marshal.Array ( advancePtr)

import Data.Number.Flint.Flint
import Data.Number.Flint.ThreadPool

import Data.Number.Flint.Fmpz
import Data.Number.Flint.NMod
import Data.Number.Flint.NMod.Vec
import Data.Number.Flint.NMod.Types

#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/nmod_vec.h>
#include <flint/nmod_mat.h>
#include <flint/nmod_poly.h>
#include <flint/nmod_poly_mat.h>

-- nmod_mat_t -----------------------------------------------------------------

newNModPolyMat rows cols n = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> nmod_poly_mat_init x rows cols n
  addForeignPtrFinalizer p_nmod_poly_mat_clear x
  return $ NModPolyMat x

{-# INLINE withNModPolyMat #-}
withNModPolyMat (NModPolyMat x) f = do
  withForeignPtr x $ \px -> f px >>= return . (NModPolyMat x,)

-- Memory management -----------------------------------------------------------

-- | /nmod_poly_mat_init/ /mat/ /rows/ /cols/ /n/ 
--
-- Initialises a matrix with the given number of rows and columns for use.
-- The modulus is set to \(n\).
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_init"
  nmod_poly_mat_init :: Ptr CNModPolyMat -> CLong -> CLong -> CMpLimb -> IO ()

-- | /nmod_poly_mat_init_set/ /mat/ /src/ 
--
-- Initialises a matrix @mat@ of the same dimensions and modulus as @src@,
-- and sets it to a copy of @src@.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_init_set"
  nmod_poly_mat_init_set :: Ptr CNModPolyMat -> Ptr CNModPolyMat -> IO ()

-- | /nmod_poly_mat_clear/ /mat/ 
--
-- Frees all memory associated with the matrix. The matrix must be
-- reinitialised if it is to be used again.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_clear"
  nmod_poly_mat_clear :: Ptr CNModPolyMat -> IO ()

foreign import ccall "nmod_poly_mat.h &nmod_poly_mat_clear"
  p_nmod_poly_mat_clear :: FunPtr (Ptr CNModPolyMat -> IO ())

-- Basic properties ------------------------------------------------------------

-- | /nmod_poly_mat_nrows/ /mat/ 
--
-- Returns the number of rows in @mat@.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_nrows"
  nmod_poly_mat_nrows :: Ptr CNModPolyMat -> IO CLong

-- | /nmod_poly_mat_ncols/ /mat/ 
--
-- Returns the number of columns in @mat@.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_ncols"
  nmod_poly_mat_ncols :: Ptr CNModPolyMat -> IO CLong

-- | /nmod_poly_mat_modulus/ /mat/ 
--
-- Returns the modulus of @mat@.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_modulus"
  nmod_poly_mat_modulus :: Ptr CNModPolyMat -> IO CMpLimb

-- Basic assignment and manipulation -------------------------------------------

-- | /nmod_poly_mat_entry/ /mat/ /i/ /j/ 
--
-- Gives a reference to the entry at row @i@ and column @j@. The reference
-- can be passed as an input or output variable to any @nmod_poly@ function
-- for direct manipulation of the matrix element. No bounds checking is
-- performed.
nmod_poly_mat_entry :: Ptr CNModPolyMat -> CLong -> CLong -> IO (Ptr CNModPoly)
nmod_poly_mat_entry mat i j = do
  CNModPolyMat entries r c rows mod <- peek mat
  return $ entries `advancePtr` (fromIntegral (i*c + j))


-- | /nmod_poly_mat_set/ /mat1/ /mat2/ 
--
-- Sets @mat1@ to a copy of @mat2@.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_set"
  nmod_poly_mat_set :: Ptr CNModPolyMat -> Ptr CNModPolyMat -> IO ()

-- | /nmod_poly_mat_swap/ /mat1/ /mat2/ 
--
-- Swaps @mat1@ and @mat2@ efficiently.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_swap"
  nmod_poly_mat_swap :: Ptr CNModPolyMat -> Ptr CNModPolyMat -> IO ()

-- | /nmod_poly_mat_swap_entrywise/ /mat1/ /mat2/ 
--
-- Swaps two matrices by swapping the individual entries rather than
-- swapping the contents of the structs.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_swap_entrywise"
  nmod_poly_mat_swap_entrywise :: Ptr CNModPolyMat -> Ptr CNModPolyMat -> IO ()

-- Input and output ------------------------------------------------------------

foreign import ccall "nmod_poly_mat.h nmod_poly_mat_get_str"
  nmod_poly_mat_get_str :: Ptr CNModPolyMat -> CString -> IO CString

foreign import ccall "nmod_poly_mat.h nmod_poly_mat_fprint"
  nmod_poly_mat_fprint :: Ptr CFile -> Ptr CNModPolyMat -> CString -> IO ()

-- | /nmod_poly_mat_print/ /mat/ /x/ 
--
-- Prints the matrix @mat@ to standard output, using the variable @x@.
nmod_poly_mat_print :: Ptr CNModPolyMat -> CString -> IO ()
nmod_poly_mat_print mat x = do
  printCStr (\mat -> nmod_poly_mat_get_str mat x) mat
  return ()

-- Random matrix generation ----------------------------------------------------

-- | /nmod_poly_mat_randtest/ /mat/ /state/ /len/ 
--
-- This is equivalent to applying @nmod_poly_randtest@ to all entries in
-- the matrix.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_randtest"
  nmod_poly_mat_randtest :: Ptr CNModPolyMat -> Ptr CFRandState -> CLong -> IO ()

-- | /nmod_poly_mat_randtest_sparse/ /A/ /state/ /len/ /density/ 
--
-- Creates a random matrix with the amount of nonzero entries given
-- approximately by the @density@ variable, which should be a fraction
-- between 0 (most sparse) and 1 (most dense).
-- 
-- The nonzero entries will have random lengths between 1 and @len@.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_randtest_sparse"
  nmod_poly_mat_randtest_sparse :: Ptr CNModPolyMat -> Ptr CFRandState -> CLong -> CFloat -> IO ()

-- Special matrices ------------------------------------------------------------

-- | /nmod_poly_mat_zero/ /mat/ 
--
-- Sets @mat@ to the zero matrix.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_zero"
  nmod_poly_mat_zero :: Ptr CNModPolyMat -> IO ()

-- | /nmod_poly_mat_one/ /mat/ 
--
-- Sets @mat@ to the unit or identity matrix of given shape, having the
-- element 1 on the main diagonal and zeros elsewhere. If @mat@ is
-- nonsquare, it is set to the truncation of a unit matrix.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_one"
  nmod_poly_mat_one :: Ptr CNModPolyMat -> IO ()

-- Basic comparison and properties ---------------------------------------------

-- | /nmod_poly_mat_equal/ /mat1/ /mat2/ 
--
-- Returns nonzero if @mat1@ and @mat2@ have the same shape and all their
-- entries agree, and returns zero otherwise.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_equal"
  nmod_poly_mat_equal :: Ptr CNModPolyMat -> Ptr CNModPolyMat -> IO CInt

-- | /nmod_poly_mat_is_zero/ /mat/ 
--
-- Returns nonzero if all entries in @mat@ are zero, and returns zero
-- otherwise.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_is_zero"
  nmod_poly_mat_is_zero :: Ptr CNModPolyMat -> IO CInt

-- | /nmod_poly_mat_is_one/ /mat/ 
--
-- Returns nonzero if all entry of @mat@ on the main diagonal are the
-- constant polynomial 1 and all remaining entries are zero, and returns
-- zero otherwise. The matrix need not be square.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_is_one"
  nmod_poly_mat_is_one :: Ptr CNModPolyMat -> IO CInt

-- | /nmod_poly_mat_is_empty/ /mat/ 
--
-- Returns a non-zero value if the number of rows or the number of columns
-- in @mat@ is zero, and otherwise returns zero.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_is_empty"
  nmod_poly_mat_is_empty :: Ptr CNModPolyMat -> IO CInt

-- | /nmod_poly_mat_is_square/ /mat/ 
--
-- Returns a non-zero value if the number of rows is equal to the number of
-- columns in @mat@, and otherwise returns zero.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_is_square"
  nmod_poly_mat_is_square :: Ptr CNModPolyMat -> IO CInt

-- Norms -----------------------------------------------------------------------

-- | /nmod_poly_mat_max_length/ /A/ 
--
-- Returns the maximum polynomial length among all the entries in @A@.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_max_length"
  nmod_poly_mat_max_length :: Ptr CNModPolyMat -> IO CLong

-- Evaluation ------------------------------------------------------------------

-- | /nmod_poly_mat_evaluate_nmod/ /B/ /A/ /x/ 
--
-- Sets the @nmod_mat_t@ @B@ to @A@ evaluated entrywise at the point @x@.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_evaluate_nmod"
  nmod_poly_mat_evaluate_nmod :: Ptr CNModMat -> Ptr CNModPolyMat -> CMpLimb -> IO ()

-- Arithmetic ------------------------------------------------------------------

-- | /nmod_poly_mat_scalar_mul_nmod_poly/ /B/ /A/ /c/ 
--
-- Sets @B@ to @A@ multiplied entrywise by the polynomial @c@.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_scalar_mul_nmod_poly"
  nmod_poly_mat_scalar_mul_nmod_poly :: Ptr CNModPolyMat -> Ptr CNModPolyMat -> Ptr CNModPoly -> IO ()

-- | /nmod_poly_mat_scalar_mul_nmod/ /B/ /A/ /c/ 
--
-- Sets @B@ to @A@ multiplied entrywise by the coefficient @c@, which is
-- assumed to be reduced modulo the modulus.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_scalar_mul_nmod"
  nmod_poly_mat_scalar_mul_nmod :: Ptr CNModPolyMat -> Ptr CNModPolyMat -> CMpLimb -> IO ()

-- | /nmod_poly_mat_add/ /C/ /A/ /B/ 
--
-- Sets @C@ to the sum of @A@ and @B@. All matrices must have the same
-- shape. Aliasing is allowed.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_add"
  nmod_poly_mat_add :: Ptr CNModPolyMat -> Ptr CNModPolyMat -> Ptr CNModPolyMat -> IO ()

-- | /nmod_poly_mat_sub/ /C/ /A/ /B/ 
--
-- Sets @C@ to the sum of @A@ and @B@. All matrices must have the same
-- shape. Aliasing is allowed.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_sub"
  nmod_poly_mat_sub :: Ptr CNModPolyMat -> Ptr CNModPolyMat -> Ptr CNModPolyMat -> IO ()

-- | /nmod_poly_mat_neg/ /B/ /A/ 
--
-- Sets @B@ to the negation of @A@. The matrices must have the same shape.
-- Aliasing is allowed.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_neg"
  nmod_poly_mat_neg :: Ptr CNModPolyMat -> Ptr CNModPolyMat -> IO ()

-- | /nmod_poly_mat_mul/ /C/ /A/ /B/ 
--
-- Sets @C@ to the matrix product of @A@ and @B@. The matrices must have
-- compatible dimensions for matrix multiplication. Aliasing is allowed.
-- This function automatically chooses between classical, KS and
-- evaluation-interpolation multiplication.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_mul"
  nmod_poly_mat_mul :: Ptr CNModPolyMat -> Ptr CNModPolyMat -> Ptr CNModPolyMat -> IO ()

-- | /nmod_poly_mat_mul_classical/ /C/ /A/ /B/ 
--
-- Sets @C@ to the matrix product of @A@ and @B@, computed using the
-- classical algorithm. The matrices must have compatible dimensions for
-- matrix multiplication. Aliasing is allowed.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_mul_classical"
  nmod_poly_mat_mul_classical :: Ptr CNModPolyMat -> Ptr CNModPolyMat -> Ptr CNModPolyMat -> IO ()

-- | /nmod_poly_mat_mul_KS/ /C/ /A/ /B/ 
--
-- Sets @C@ to the matrix product of @A@ and @B@, computed using Kronecker
-- segmentation. The matrices must have compatible dimensions for matrix
-- multiplication. Aliasing is allowed.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_mul_KS"
  nmod_poly_mat_mul_KS :: Ptr CNModPolyMat -> Ptr CNModPolyMat -> Ptr CNModPolyMat -> IO ()

-- | /nmod_poly_mat_mul_interpolate/ /C/ /A/ /B/ 
--
-- Sets @C@ to the matrix product of @A@ and @B@, computed through
-- evaluation and interpolation. The matrices must have compatible
-- dimensions for matrix multiplication. For interpolation to be
-- well-defined, we require that the modulus is a prime at least as large
-- as \(m + n - 1\) where \(m\) and \(n\) are the maximum lengths of
-- polynomials in the input matrices. Aliasing is allowed.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_mul_interpolate"
  nmod_poly_mat_mul_interpolate :: Ptr CNModPolyMat -> Ptr CNModPolyMat -> Ptr CNModPolyMat -> IO ()

-- | /nmod_poly_mat_sqr/ /B/ /A/ 
--
-- Sets @B@ to the square of @A@, which must be a square matrix. Aliasing
-- is allowed. This function automatically chooses between classical and KS
-- squaring.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_sqr"
  nmod_poly_mat_sqr :: Ptr CNModPolyMat -> Ptr CNModPolyMat -> IO ()

-- | /nmod_poly_mat_sqr_classical/ /B/ /A/ 
--
-- Sets @B@ to the square of @A@, which must be a square matrix. Aliasing
-- is allowed. This function uses direct formulas for very small matrices,
-- and otherwise classical matrix multiplication.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_sqr_classical"
  nmod_poly_mat_sqr_classical :: Ptr CNModPolyMat -> Ptr CNModPolyMat -> IO ()

-- | /nmod_poly_mat_sqr_KS/ /B/ /A/ 
--
-- Sets @B@ to the square of @A@, which must be a square matrix. Aliasing
-- is allowed. This function uses Kronecker segmentation.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_sqr_KS"
  nmod_poly_mat_sqr_KS :: Ptr CNModPolyMat -> Ptr CNModPolyMat -> IO ()

-- | /nmod_poly_mat_sqr_interpolate/ /B/ /A/ 
--
-- Sets @B@ to the square of @A@, which must be a square matrix, computed
-- through evaluation and interpolation. For interpolation to be
-- well-defined, we require that the modulus is a prime at least as large
-- as \(2n - 1\) where \(n\) is the maximum length of polynomials in the
-- input matrix. Aliasing is allowed.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_sqr_interpolate"
  nmod_poly_mat_sqr_interpolate :: Ptr CNModPolyMat -> Ptr CNModPolyMat -> IO ()

-- | /nmod_poly_mat_pow/ /B/ /A/ /exp/ 
--
-- Sets @B@ to @A@ raised to the power @exp@, where @A@ is a square matrix.
-- Uses exponentiation by squaring. Aliasing is allowed.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_pow"
  nmod_poly_mat_pow :: Ptr CNModPolyMat -> Ptr CNModPolyMat -> CULong -> IO ()

-- Row reduction ---------------------------------------------------------------

-- | /nmod_poly_mat_find_pivot_any/ /mat/ /start_row/ /end_row/ /c/ 
--
-- Attempts to find a pivot entry for row reduction. Returns a row index
-- \(r\) between @start_row@ (inclusive) and @stop_row@ (exclusive) such
-- that column \(c\) in @mat@ has a nonzero entry on row \(r\), or returns
-- -1 if no such entry exists.
-- 
-- This implementation simply chooses the first nonzero entry from it
-- encounters. This is likely to be a nearly optimal choice if all entries
-- in the matrix have roughly the same size, but can lead to unnecessary
-- coefficient growth if the entries vary in size.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_find_pivot_any"
  nmod_poly_mat_find_pivot_any :: Ptr CNModPolyMat -> CLong -> CLong -> CLong -> IO CLong

-- | /nmod_poly_mat_find_pivot_partial/ /mat/ /start_row/ /end_row/ /c/ 
--
-- Attempts to find a pivot entry for row reduction. Returns a row index
-- \(r\) between @start_row@ (inclusive) and @stop_row@ (exclusive) such
-- that column \(c\) in @mat@ has a nonzero entry on row \(r\), or returns
-- -1 if no such entry exists.
-- 
-- This implementation searches all the rows in the column and chooses the
-- nonzero entry of smallest degree. This heuristic typically reduces
-- coefficient growth when the matrix entries vary in size.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_find_pivot_partial"
  nmod_poly_mat_find_pivot_partial :: Ptr CNModPolyMat -> CLong -> CLong -> CLong -> IO CLong

-- | /nmod_poly_mat_fflu/ /B/ /den/ /perm/ /A/ /rank_check/ 
--
-- Uses fraction-free Gaussian elimination to set (@B@, @den@) to a
-- fraction-free LU decomposition of @A@ and returns the rank of @A@.
-- Aliasing of @A@ and @B@ is allowed.
-- 
-- Pivot elements are chosen with @nmod_poly_mat_find_pivot_partial@. If
-- @perm@ is non-@NULL@, the permutation of rows in the matrix will also be
-- applied to @perm@.
-- 
-- If @rank_check@ is set, the function aborts and returns 0 if the matrix
-- is detected not to have full rank without completing the elimination.
-- 
-- The denominator @den@ is set to \(\pm \operatorname{det}(A)\), where the
-- sign is decided by the parity of the permutation. Note that the
-- determinant is not generally the minimal denominator.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_fflu"
  nmod_poly_mat_fflu :: Ptr CNModPolyMat -> Ptr CNModPoly -> Ptr CLong -> Ptr CNModPolyMat -> CInt -> IO CLong

-- | /nmod_poly_mat_rref/ /B/ /den/ /A/ 
--
-- Sets (@B@, @den@) to the reduced row echelon form of @A@ and returns the
-- rank of @A@. Aliasing of @A@ and @B@ is allowed.
-- 
-- The denominator @den@ is set to \(\pm \operatorname{det}(A)\). Note that
-- the determinant is not generally the minimal denominator.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_rref"
  nmod_poly_mat_rref :: Ptr CNModPolyMat -> Ptr CNModPoly -> Ptr CNModPolyMat -> IO CLong

-- Trace -----------------------------------------------------------------------

-- | /nmod_poly_mat_trace/ /trace/ /mat/ 
--
-- Computes the trace of the matrix, i.e. the sum of the entries on the
-- main diagonal. The matrix is required to be square.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_trace"
  nmod_poly_mat_trace :: Ptr CNModPoly -> Ptr CNModPolyMat -> IO ()

-- Determinant and rank --------------------------------------------------------

-- | /nmod_poly_mat_det/ /det/ /A/ 
--
-- Sets @det@ to the determinant of the square matrix @A@. Uses a direct
-- formula, fraction-free LU decomposition, or interpolation, depending on
-- the size of the matrix.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_det"
  nmod_poly_mat_det :: Ptr CNModPoly -> Ptr CNModPolyMat -> IO ()

-- | /nmod_poly_mat_det_fflu/ /det/ /A/ 
--
-- Sets @det@ to the determinant of the square matrix @A@. The determinant
-- is computed by performing a fraction-free LU decomposition on a copy of
-- @A@.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_det_fflu"
  nmod_poly_mat_det_fflu :: Ptr CNModPoly -> Ptr CNModPolyMat -> IO ()

-- | /nmod_poly_mat_det_interpolate/ /det/ /A/ 
--
-- Sets @det@ to the determinant of the square matrix @A@. The determinant
-- is computed by determining a bound \(n\) for its length, evaluating the
-- matrix at \(n\) distinct points, computing the determinant of each
-- coefficient matrix, and forming the interpolating polynomial.
-- 
-- If the coefficient ring does not contain \(n\) distinct points (that is,
-- if working over \(\mathbf{Z}/p\mathbf{Z}\) where \(p < n\)), this
-- function automatically falls back to @nmod_poly_mat_det_fflu@.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_det_interpolate"
  nmod_poly_mat_det_interpolate :: Ptr CNModPoly -> Ptr CNModPolyMat -> IO ()

-- | /nmod_poly_mat_rank/ /A/ 
--
-- Returns the rank of @A@. Performs fraction-free LU decomposition on a
-- copy of @A@.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_rank"
  nmod_poly_mat_rank :: Ptr CNModPolyMat -> IO CLong

-- Inverse ---------------------------------------------------------------------

-- | /nmod_poly_mat_inv/ /Ainv/ /den/ /A/ 
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
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_inv"
  nmod_poly_mat_inv :: Ptr CNModPolyMat -> Ptr CNModPoly -> Ptr CNModPolyMat -> IO CInt

-- Nullspace -------------------------------------------------------------------

-- | /nmod_poly_mat_nullspace/ /res/ /mat/ 
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
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_nullspace"
  nmod_poly_mat_nullspace :: Ptr CNModPolyMat -> Ptr CNModPolyMat -> IO CLong

-- Solving ---------------------------------------------------------------------

-- | /nmod_poly_mat_solve/ /X/ /den/ /A/ /B/ 
--
-- Solves the equation \(AX = B\) for nonsingular \(A\). More precisely,
-- computes (@X@, @den@) such that \(AX = B \times \operatorname{den}\).
-- Returns 1 if \(A\) is nonsingular and 0 if \(A\) is singular. The
-- computed denominator will not generally be minimal.
-- 
-- Uses fraction-free LU decomposition followed by fraction-free forward
-- and back substitution.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_solve"
  nmod_poly_mat_solve :: Ptr CNModPolyMat -> Ptr CNModPoly -> Ptr CNModPolyMat -> Ptr CNModPolyMat -> IO CInt

-- | /nmod_poly_mat_solve_fflu/ /X/ /den/ /A/ /B/ 
--
-- Solves the equation \(AX = B\) for nonsingular \(A\). More precisely,
-- computes (@X@, @den@) such that \(AX = B \times \operatorname{den}\).
-- Returns 1 if \(A\) is nonsingular and 0 if \(A\) is singular. The
-- computed denominator will not generally be minimal.
-- 
-- Uses fraction-free LU decomposition followed by fraction-free forward
-- and back substitution.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_solve_fflu"
  nmod_poly_mat_solve_fflu :: Ptr CNModPolyMat -> Ptr CNModPoly -> Ptr CNModPolyMat -> Ptr CNModPolyMat -> IO CInt

-- | /nmod_poly_mat_solve_fflu_precomp/ /X/ /perm/ /FFLU/ /B/ 
--
-- Performs fraction-free forward and back substitution given a precomputed
-- fraction-free LU decomposition and corresponding permutation.
foreign import ccall "nmod_poly_mat.h nmod_poly_mat_solve_fflu_precomp"
  nmod_poly_mat_solve_fflu_precomp :: Ptr CNModPolyMat -> Ptr CLong -> Ptr CNModPolyMat -> Ptr CNModPolyMat -> IO ()

