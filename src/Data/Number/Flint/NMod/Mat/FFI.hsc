{-|
module      :  Data.Number.Flint.NMod.Mat.FFI
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de
-}
module Data.Number.Flint.NMod.Mat.FFI (
  -- * Matrices over integers mod n (word-size n)
    NModMat (..)
  , CNModMat (..)
  , newNModMat
  , withNModMat
  -- * Memory management
  , nmod_mat_init
  , nmod_mat_init_set
  , nmod_mat_clear
  , nmod_mat_set
  , nmod_mat_swap
  , nmod_mat_swap_entrywise
  -- * Basic properties and manipulation
  -- , nmod_mat_entry
  , nmod_mat_get_entry
  , nmod_mat_entry_ptr
  , nmod_mat_set_entry
  , nmod_mat_nrows
  , nmod_mat_ncols
  , nmod_mat_zero
  , nmod_mat_is_zero
  -- * Window
  , nmod_mat_window_init
  , nmod_mat_window_clear
  -- * Concatenate
  , nmod_mat_concat_vertical
  , nmod_mat_concat_horizontal
  -- * Printing
  , nmod_mat_print_pretty
  -- * Random matrix generation
  , nmod_mat_randtest
  , nmod_mat_randfull
  , nmod_mat_randpermdiag
  , nmod_mat_randrank
  , nmod_mat_randops
  , nmod_mat_randtril
  , nmod_mat_randtriu
  -- * Comparison
  , nmod_mat_equal
  , nmod_mat_is_zero_row
  -- * Transposition and permutations
  , nmod_mat_transpose
  , nmod_mat_swap_rows
  , nmod_mat_swap_cols
  , nmod_mat_invert_rows
  , nmod_mat_invert_cols
  , nmod_mat_permute_rows
  -- * Addition and subtraction
  , nmod_mat_add
  , nmod_mat_sub
  , nmod_mat_neg
  -- * Matrix-scalar arithmetic
  , nmod_mat_scalar_mul
  , nmod_mat_scalar_addmul_ui
  , nmod_mat_scalar_mul_fmpz
  -- * Matrix multiplication
  , nmod_mat_mul
  , _nmod_mat_mul_classical_op
  , nmod_mat_mul_classical
  , _nmod_mat_mul_classical_threaded_pool_op
  , _nmod_mat_mul_classical_threaded_op
  , nmod_mat_mul_classical_threaded
  , nmod_mat_mul_strassen
  , nmod_mat_mul_blas
  , nmod_mat_addmul
  , nmod_mat_submul
  , nmod_mat_mul_nmod_vec
  , nmod_mat_nmod_vec_mul
  -- * Matrix Exponentiation
  , _nmod_mat_pow
  , nmod_mat_pow
  -- * Trace
  , nmod_mat_trace
  -- * Determinant and rank
  , nmod_mat_det_howell
  , nmod_mat_det
  , nmod_mat_rank
  -- * Inverse
  , nmod_mat_inv
  -- * Triangular solving
  , nmod_mat_solve_tril
  , nmod_mat_solve_tril_classical
  , nmod_mat_solve_tril_recursive
  , nmod_mat_solve_triu
  , nmod_mat_solve_triu_classical
  , nmod_mat_solve_triu_recursive
  -- * Nonsingular square solving
  , nmod_mat_solve
  , nmod_mat_can_solve_inner
  , nmod_mat_can_solve
  , nmod_mat_solve_vec
  -- * LU decomposition
  , nmod_mat_lu
  -- * Reduced row echelon form
  , nmod_mat_rref
  , nmod_mat_reduce_row
  -- * Nullspace
  , nmod_mat_nullspace
  -- * Transforms
  , nmod_mat_similarity
  -- * Characteristic polynomial
  , nmod_mat_charpoly_berkowitz
  -- * Minimal polynomial
  , nmod_mat_minpoly
  -- * Strong echelon form and Howell form
  , nmod_mat_strong_echelon_form
  , nmod_mat_howell_form
) where

-- Matrices over integers mod n (word-size n) ----------------------------------

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

-- nmod_mat_t -----------------------------------------------------------------

newNModMat rows cols n = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> nmod_mat_init x rows cols n
  addForeignPtrFinalizer p_nmod_mat_clear x
  return $ NModMat x

{-# INLINE withNModMat #-}
withNModMat (NModMat x) f = do
  withForeignPtr x $ \px -> f px >>= return . (NModMat x,)

-- Memory management -----------------------------------------------------------

-- | /nmod_mat_init/ /mat/ /rows/ /cols/ /n/ 
-- 
-- Initialises @mat@ to a @rows@-by-@cols@ matrix with coefficients modulo
-- \(n\), where \(n\) can be any nonzero integer that fits in a limb. All
-- elements are set to zero.
foreign import ccall "nmod_mat.h nmod_mat_init"
  nmod_mat_init :: Ptr CNModMat -> CLong -> CLong -> CMpLimb -> IO ()

-- | /nmod_mat_init_set/ /mat/ /src/ 
-- 
-- Initialises @mat@ and sets its dimensions, modulus and elements to those
-- of @src@.
foreign import ccall "nmod_mat.h nmod_mat_init_set"
  nmod_mat_init_set :: Ptr CNModMat -> Ptr CNModMat -> IO ()

-- | /nmod_mat_clear/ /mat/ 
-- 
-- Clears the matrix and releases any memory it used. The matrix cannot be
-- used again until it is initialised. This function must be called exactly
-- once when finished using an @nmod_mat_t@ object.
foreign import ccall "nmod_mat.h nmod_mat_clear"
  nmod_mat_clear :: Ptr CNModMat -> IO ()

foreign import ccall "nmod_mat.h &nmod_mat_clear"
  p_nmod_mat_clear :: FunPtr (Ptr CNModMat -> IO ())

-- | /nmod_mat_set/ /mat/ /src/ 
-- 
-- Sets @mat@ to a copy of @src@. It is assumed that @mat@ and @src@ have
-- identical dimensions.
foreign import ccall "nmod_mat.h nmod_mat_set"
  nmod_mat_set :: Ptr CNModMat -> Ptr CNModMat -> IO ()

-- | /nmod_mat_swap/ /mat1/ /mat2/ 
-- 
-- Exchanges @mat1@ and @mat2@.
foreign import ccall "nmod_mat.h nmod_mat_swap"
  nmod_mat_swap :: Ptr CNModMat -> Ptr CNModMat -> IO ()

-- | /nmod_mat_swap_entrywise/ /mat1/ /mat2/ 
-- 
-- Swaps two matrices by swapping the individual entries rather than
-- swapping the contents of the structs.
foreign import ccall "nmod_mat.h nmod_mat_swap_entrywise"
  nmod_mat_swap_entrywise :: Ptr CNModMat -> Ptr CNModMat -> IO ()

-- Basic properties and manipulation -------------------------------------------

-- -- | /nmod_mat_entry/ /mat/ /i/ /j/ 
-- -- 
-- -- Directly accesses the entry in @mat@ in row \(i\) and column \(j\),
-- -- indexed from zero. No bounds checking is performed. This macro can be
-- -- used both for reading and writing coefficients.
-- foreign import ccall "nmod_mat.h nmod_mat_entry"
--   nmod_mat_entry :: Ptr CNModMat -> CLong -> CLong -> IO (Ptr CNMod)
  
-- nmod_mat_entry mat i j = do
--   ncols <- nmod_mat_nrows mat
--   return $ (castPtr mat) `advancePtr` (fromIntegral (ncols * i + ))

-- | /nmod_mat_get_entry/ /mat/ /i/ /j/ 
-- 
-- Get the entry at row \(i\) and column \(j\) of the matrix @mat@.
foreign import ccall "nmod_mat.h nmod_mat_get_entry"
  nmod_mat_get_entry :: Ptr CNModMat -> CLong -> CLong -> IO CMpLimb

-- | /nmod_mat_entry_ptr/ /mat/ /i/ /j/ 
-- 
-- Return a pointer to the entry at row \(i\) and column \(j\) of the
-- matrix @mat@.
foreign import ccall "nmod_mat.h nmod_mat_entry_ptr"
  nmod_mat_entry_ptr :: Ptr CNModMat -> CLong -> CLong -> IO (Ptr CMpLimb)

-- | /nmod_mat_set_entry/ /mat/ /i/ /j/ /x/ 
-- 
-- Set the entry at row \(i\) and column \(j\) of the matrix @mat@ to @x@.
foreign import ccall "nmod_mat.h nmod_mat_set_entry"
  nmod_mat_set_entry :: Ptr CNModMat -> CLong -> CLong -> CMpLimb -> IO ()

-- | /nmod_mat_nrows/ /mat/ 
-- 
-- Returns the number of rows in @mat@.
foreign import ccall "nmod_mat.h nmod_mat_nrows"
  nmod_mat_nrows :: Ptr CNModMat -> IO CLong

-- | /nmod_mat_ncols/ /mat/ 
-- 
-- Returns the number of columns in @mat@.
foreign import ccall "nmod_mat.h nmod_mat_ncols"
  nmod_mat_ncols :: Ptr CNModMat -> IO CLong

-- | /nmod_mat_zero/ /mat/ 
-- 
-- Sets all entries of the matrix @mat@ to zero.
foreign import ccall "nmod_mat.h nmod_mat_zero"
  nmod_mat_zero :: Ptr CNModMat -> IO ()

-- | /nmod_mat_is_zero/ /mat/ 
-- 
-- Returns \(1\) if all entries of the matrix @mat@ are zero.
foreign import ccall "nmod_mat.h nmod_mat_is_zero"
  nmod_mat_is_zero :: Ptr CNModMat -> IO CInt

-- Window ----------------------------------------------------------------------

-- | /nmod_mat_window_init/ /window/ /mat/ /r1/ /c1/ /r2/ /c2/ 
-- 
-- Initializes the matrix @window@ to be an @r2 - r1@ by @c2 - c1@
-- submatrix of @mat@ whose @(0,0)@ entry is the @(r1, c1)@ entry of @mat@.
-- The memory for the elements of @window@ is shared with @mat@.
foreign import ccall "nmod_mat.h nmod_mat_window_init"
  nmod_mat_window_init :: Ptr CNModMat -> Ptr CNModMat -> CLong -> CLong -> CLong -> CLong -> IO ()

-- | /nmod_mat_window_clear/ /window/ 
-- 
-- Clears the matrix @window@ and releases any memory that it uses. Note
-- that the memory to the underlying matrix that @window@ points to is not
-- freed.
foreign import ccall "nmod_mat.h nmod_mat_window_clear"
  nmod_mat_window_clear :: Ptr CNModMat -> IO ()

-- Concatenate -----------------------------------------------------------------

-- | /nmod_mat_concat_vertical/ /res/ /mat1/ /mat2/ 
-- 
-- Sets @res@ to vertical concatenation of (mat1, @mat2@) in that order.
-- Matrix dimensions : @mat1@ : \(m \times n\), @mat2@ : \(k \times n\),
-- @res@ : \((m + k) \times n\).
foreign import ccall "nmod_mat.h nmod_mat_concat_vertical"
  nmod_mat_concat_vertical :: Ptr CNModMat -> Ptr CNModMat -> Ptr CNModMat -> IO ()

-- | /nmod_mat_concat_horizontal/ /res/ /mat1/ /mat2/ 
-- 
-- Sets @res@ to horizontal concatenation of (@mat1@, @mat2@) in that
-- order. Matrix dimensions : @mat1@ : \(m \times n\), @mat2@ :
-- \(m \times k\), @res@ : \(m \times (n + k)\).
foreign import ccall "nmod_mat.h nmod_mat_concat_horizontal"
  nmod_mat_concat_horizontal :: Ptr CNModMat -> Ptr CNModMat -> Ptr CNModMat -> IO ()

-- Printing --------------------------------------------------------------------

-- | /nmod_mat_print_pretty/ /mat/ 
-- 
-- Pretty-prints @mat@ to @stdout@. A header is printed followed by the
-- rows enclosed in brackets. Each column is right-aligned to the width of
-- the modulus written in decimal, and the columns are separated by spaces.
-- For example:
-- 
-- > <2 x 3 integer matrix mod 2903>
-- > [   0    0 2607]
-- > [ 622    0    0]
foreign import ccall "nmod_mat.h nmod_mat_print_pretty"
  nmod_mat_print_pretty :: Ptr CNModMat -> IO ()

-- Random matrix generation ----------------------------------------------------

-- | /nmod_mat_randtest/ /mat/ /state/ 
-- 
-- Sets the elements to a random matrix with entries between \(0\) and
-- \(m-1\) inclusive, where \(m\) is the modulus of @mat@. A sparse matrix
-- is generated with increased probability.
foreign import ccall "nmod_mat.h nmod_mat_randtest"
  nmod_mat_randtest :: Ptr CNModMat -> Ptr CFRandState -> IO ()

-- | /nmod_mat_randfull/ /mat/ /state/ 
-- 
-- Sets the element to random numbers likely to be close to the modulus of
-- the matrix. This is used to test potential overflow-related bugs.
foreign import ccall "nmod_mat.h nmod_mat_randfull"
  nmod_mat_randfull :: Ptr CNModMat -> Ptr CFRandState -> IO ()

-- | /nmod_mat_randpermdiag/ /mat/ /state/ /diag/ /n/ 
-- 
-- Sets @mat@ to a random permutation of the diagonal matrix with \(n\)
-- leading entries given by the vector @diag@. It is assumed that the main
-- diagonal of @mat@ has room for at least \(n\) entries.
-- 
-- Returns \(0\) or \(1\), depending on whether the permutation is even or
-- odd respectively.
foreign import ccall "nmod_mat.h nmod_mat_randpermdiag"
  nmod_mat_randpermdiag :: Ptr CNModMat -> Ptr CFRandState -> Ptr (Ptr CMp) -> CLong -> IO CInt

-- | /nmod_mat_randrank/ /mat/ /state/ /rank/ 
-- 
-- Sets @mat@ to a random sparse matrix with the given rank, having exactly
-- as many non-zero elements as the rank, with the non-zero elements being
-- uniformly random integers between \(0\) and \(m-1\) inclusive, where
-- \(m\) is the modulus of @mat@.
-- 
-- The matrix can be transformed into a dense matrix with unchanged rank by
-- subsequently calling @nmod_mat_randops@.
foreign import ccall "nmod_mat.h nmod_mat_randrank"
  nmod_mat_randrank :: Ptr CNModMat -> Ptr CFRandState -> CLong -> IO ()

-- | /nmod_mat_randops/ /mat/ /count/ /state/ 
-- 
-- Randomises @mat@ by performing elementary row or column operations. More
-- precisely, at most @count@ random additions or subtractions of distinct
-- rows and columns will be performed. This leaves the rank (and for square
-- matrices, determinant) unchanged.
foreign import ccall "nmod_mat.h nmod_mat_randops"
  nmod_mat_randops :: Ptr CNModMat -> CLong -> Ptr CFRandState -> IO ()

-- | /nmod_mat_randtril/ /mat/ /state/ /unit/ 
-- 
-- Sets @mat@ to a random lower triangular matrix. If @unit@ is 1, it will
-- have ones on the main diagonal, otherwise it will have random nonzero
-- entries on the main diagonal.
foreign import ccall "nmod_mat.h nmod_mat_randtril"
  nmod_mat_randtril :: Ptr CNModMat -> Ptr CFRandState -> CInt -> IO ()

-- | /nmod_mat_randtriu/ /mat/ /state/ /unit/ 
-- 
-- Sets @mat@ to a random upper triangular matrix. If @unit@ is 1, it will
-- have ones on the main diagonal, otherwise it will have random nonzero
-- entries on the main diagonal.
foreign import ccall "nmod_mat.h nmod_mat_randtriu"
  nmod_mat_randtriu :: Ptr CNModMat -> Ptr CFRandState -> CInt -> IO ()

-- Comparison ------------------------------------------------------------------

-- | /nmod_mat_equal/ /mat1/ /mat2/ 
-- 
-- Returns nonzero if @mat1@ and @mat2@ have the same dimensions and
-- elements, and zero otherwise. The moduli are ignored.
foreign import ccall "nmod_mat.h nmod_mat_equal"
  nmod_mat_equal :: Ptr CNModMat -> Ptr CNModMat -> IO CInt

-- | /nmod_mat_is_zero_row/ /mat/ /i/ 
-- 
-- Returns a non-zero value if row \(i\) of @mat@ is zero.
foreign import ccall "nmod_mat.h nmod_mat_is_zero_row"
  nmod_mat_is_zero_row :: Ptr CNModMat -> CLong -> IO CInt

-- Transposition and permutations ----------------------------------------------

-- | /nmod_mat_transpose/ /B/ /A/ 
-- 
-- Sets \(B\) to the transpose of \(A\). Dimensions must be compatible.
-- \(B\) and \(A\) may be the same object if and only if the matrix is
-- square.
foreign import ccall "nmod_mat.h nmod_mat_transpose"
  nmod_mat_transpose :: Ptr CNModMat -> Ptr CNModMat -> IO ()

-- | /nmod_mat_swap_rows/ /mat/ /perm/ /r/ /s/ 
-- 
-- Swaps rows @r@ and @s@ of @mat@. If @perm@ is non-@NULL@, the
-- permutation of the rows will also be applied to @perm@.
foreign import ccall "nmod_mat.h nmod_mat_swap_rows"
  nmod_mat_swap_rows :: Ptr CNModMat -> Ptr CLong -> CLong -> CLong -> IO ()

-- | /nmod_mat_swap_cols/ /mat/ /perm/ /r/ /s/ 
-- 
-- Swaps columns @r@ and @s@ of @mat@. If @perm@ is non-@NULL@, the
-- permutation of the columns will also be applied to @perm@.
foreign import ccall "nmod_mat.h nmod_mat_swap_cols"
  nmod_mat_swap_cols :: Ptr CNModMat -> Ptr CLong -> CLong -> CLong -> IO ()

-- | /nmod_mat_invert_rows/ /mat/ /perm/ 
-- 
-- Swaps rows @i@ and @r - i@ of @mat@ for @0 \<= i \< r\/2@, where @r@ is
-- the number of rows of @mat@. If @perm@ is non-@NULL@, the permutation of
-- the rows will also be applied to @perm@.
foreign import ccall "nmod_mat.h nmod_mat_invert_rows"
  nmod_mat_invert_rows :: Ptr CNModMat -> Ptr CLong -> IO ()

-- | /nmod_mat_invert_cols/ /mat/ /perm/ 
-- 
-- Swaps columns @i@ and @c - i@ of @mat@ for @0 \<= i \< c\/2@, where @c@
-- is the number of columns of @mat@. If @perm@ is non-@NULL@, the
-- permutation of the columns will also be applied to @perm@.
foreign import ccall "nmod_mat.h nmod_mat_invert_cols"
  nmod_mat_invert_cols :: Ptr CNModMat -> Ptr CLong -> IO ()

-- | /nmod_mat_permute_rows/ /mat/ /perm_act/ /perm_store/ 
-- 
-- Permutes rows of the matrix @mat@ according to permutation @perm_act@
-- and, if @perm_store@ is not @NULL@, apply the same permutation to it.
foreign import ccall "nmod_mat.h nmod_mat_permute_rows"
  nmod_mat_permute_rows :: Ptr CNModMat -> Ptr CLong -> Ptr CLong -> IO ()

-- Addition and subtraction ----------------------------------------------------

-- | /nmod_mat_add/ /C/ /A/ /B/ 
-- 
-- Computes \(C = A + B\). Dimensions must be identical.
foreign import ccall "nmod_mat.h nmod_mat_add"
  nmod_mat_add :: Ptr CNModMat -> Ptr CNModMat -> Ptr CNModMat -> IO ()

-- | /nmod_mat_sub/ /C/ /A/ /B/ 
-- 
-- Computes \(C = A - B\). Dimensions must be identical.
foreign import ccall "nmod_mat.h nmod_mat_sub"
  nmod_mat_sub :: Ptr CNModMat -> Ptr CNModMat -> Ptr CNModMat -> IO ()

-- | /nmod_mat_neg/ /A/ /B/ 
-- 
-- Sets \(B = -A\). Dimensions must be identical.
foreign import ccall "nmod_mat.h nmod_mat_neg"
  nmod_mat_neg :: Ptr CNModMat -> Ptr CNModMat -> IO ()

-- Matrix-scalar arithmetic ----------------------------------------------------

-- | /nmod_mat_scalar_mul/ /B/ /A/ /c/ 
-- 
-- Sets \(B = cA\), where the scalar \(c\) is assumed to be reduced modulo
-- the modulus. Dimensions of \(A\) and \(B\) must be identical.
foreign import ccall "nmod_mat.h nmod_mat_scalar_mul"
  nmod_mat_scalar_mul :: Ptr CNModMat -> Ptr CNModMat -> CMpLimb -> IO ()

-- | /nmod_mat_scalar_addmul_ui/ /dest/ /X/ /Y/ /b/ 
-- 
-- Sets \(dest = X + bY\), where the scalar \(b\) is assumed to be reduced
-- modulo the modulus. Dimensions of dest, X and Y must be identical. dest
-- can be aliased with X or Y.
foreign import ccall "nmod_mat.h nmod_mat_scalar_addmul_ui"
  nmod_mat_scalar_addmul_ui :: Ptr CNModMat -> Ptr CNModMat -> Ptr CNModMat -> CMpLimb -> IO ()

-- | /nmod_mat_scalar_mul_fmpz/ /res/ /M/ /c/ 
-- 
-- Sets \(B = cA\), where the scalar \(c\) is of type @fmpz_t@. Dimensions
-- of \(A\) and \(B\) must be identical.
foreign import ccall "nmod_mat.h nmod_mat_scalar_mul_fmpz"
  nmod_mat_scalar_mul_fmpz :: Ptr CNModMat -> Ptr CNModMat -> Ptr CFmpz -> IO ()

-- Matrix multiplication -------------------------------------------------------

-- | /nmod_mat_mul/ /C/ /A/ /B/ 
-- 
-- Sets \(C = AB\). Dimensions must be compatible for matrix
-- multiplication. Aliasing is allowed. This function automatically chooses
-- between classical and Strassen multiplication.
foreign import ccall "nmod_mat.h nmod_mat_mul"
  nmod_mat_mul :: Ptr CNModMat -> Ptr CNModMat -> Ptr CNModMat -> IO ()

-- | /_nmod_mat_mul_classical_op/ /D/ /C/ /A/ /B/ /op/ 
-- 
-- Sets @D = A*B op C@ where @op@ is @+1@ for addition, @-1@ for
-- subtraction and @0@ to ignore @C@.
foreign import ccall "nmod_mat.h _nmod_mat_mul_classical_op"
  _nmod_mat_mul_classical_op :: Ptr CNModMat -> Ptr CNModMat -> Ptr CNModMat -> Ptr CNModMat -> CInt -> IO ()

-- | /nmod_mat_mul_classical/ /C/ /A/ /B/ 
-- 
-- Sets \(C = AB\). Dimensions must be compatible for matrix
-- multiplication. \(C\) is not allowed to be aliased with \(A\) or \(B\).
-- Uses classical matrix multiplication, creating a temporary transposed
-- copy of \(B\) to improve memory locality if the matrices are large
-- enough, and packing several entries of \(B\) into each word if the
-- modulus is very small.
foreign import ccall "nmod_mat.h nmod_mat_mul_classical"
  nmod_mat_mul_classical :: Ptr CNModMat -> Ptr CNModMat -> Ptr CNModMat -> IO ()

-- | /_nmod_mat_mul_classical_threaded_pool_op/ /D/ /C/ /A/ /B/ /op/ /threads/ /num_threads/ 
-- 
-- Multithreaded version of @_nmod_mat_mul_classical@.
foreign import ccall "nmod_mat.h _nmod_mat_mul_classical_threaded_pool_op"
  _nmod_mat_mul_classical_threaded_pool_op :: Ptr CNModMat -> Ptr CNModMat -> Ptr CNModMat -> Ptr CNModMat -> CInt -> Ptr CThreadPoolHandle -> CLong -> IO ()

-- | /_nmod_mat_mul_classical_threaded_op/ /D/ /C/ /A/ /B/ /op/ 
-- 
-- Multithreaded version of @_nmod_mat_mul_classical@.
foreign import ccall "nmod_mat.h _nmod_mat_mul_classical_threaded_op"
  _nmod_mat_mul_classical_threaded_op :: Ptr CNModMat -> Ptr CNModMat -> Ptr CNModMat -> Ptr CNModMat -> CInt -> IO ()

-- | /nmod_mat_mul_classical_threaded/ /C/ /A/ /B/ 
-- 
-- Multithreaded version of @nmod_mat_mul_classical@.
foreign import ccall "nmod_mat.h nmod_mat_mul_classical_threaded"
  nmod_mat_mul_classical_threaded :: Ptr CNModMat -> Ptr CNModMat -> Ptr CNModMat -> IO ()

-- | /nmod_mat_mul_strassen/ /C/ /A/ /B/ 
-- 
-- Sets \(C = AB\). Dimensions must be compatible for matrix
-- multiplication. \(C\) is not allowed to be aliased with \(A\) or \(B\).
-- Uses Strassen multiplication (the Strassen-Winograd variant).
foreign import ccall "nmod_mat.h nmod_mat_mul_strassen"
  nmod_mat_mul_strassen :: Ptr CNModMat -> Ptr CNModMat -> Ptr CNModMat -> IO ()

-- | /nmod_mat_mul_blas/ /C/ /A/ /B/ 
-- 
-- Tries to set \(C = AB\) using BLAS and returns \(1\) for success and
-- \(0\) for failure. Dimensions must be compatible for matrix
-- multiplication.
foreign import ccall "nmod_mat.h nmod_mat_mul_blas"
  nmod_mat_mul_blas :: Ptr CNModMat -> Ptr CNModMat -> Ptr CNModMat -> IO CInt

-- | /nmod_mat_addmul/ /D/ /C/ /A/ /B/ 
-- 
-- Sets \(D = C + AB\). \(C\) and \(D\) may be aliased with each other but
-- not with \(A\) or \(B\). Automatically selects between classical and
-- Strassen multiplication.
foreign import ccall "nmod_mat.h nmod_mat_addmul"
  nmod_mat_addmul :: Ptr CNModMat -> Ptr CNModMat -> Ptr CNModMat -> Ptr CNModMat -> IO ()

-- | /nmod_mat_submul/ /D/ /C/ /A/ /B/ 
-- 
-- Sets \(D = C + AB\). \(C\) and \(D\) may be aliased with each other but
-- not with \(A\) or \(B\).
foreign import ccall "nmod_mat.h nmod_mat_submul"
  nmod_mat_submul :: Ptr CNModMat -> Ptr CNModMat -> Ptr CNModMat -> Ptr CNModMat -> IO ()

-- | /nmod_mat_mul_nmod_vec/ /c/ /A/ /b/ /blen/ 
-- 
-- Compute a matrix-vector product of @A@ and @(b, blen)@ and store the
-- result in @c@. The vector @(b, blen)@ is either truncated or
-- zero-extended to the number of columns of @A@. The number entries
-- written to @c@ is always equal to the number of rows of @A@.
foreign import ccall "nmod_mat.h nmod_mat_mul_nmod_vec"
  nmod_mat_mul_nmod_vec :: Ptr CMpLimb -> Ptr CNModMat -> Ptr CMpLimb -> CLong -> IO ()

-- | /nmod_mat_nmod_vec_mul/ /c/ /a/ /alen/ /B/ 
-- 
-- Compute a vector-matrix product of @(a, alen)@ and @B@ and and store the
-- result in @c@. The vector @(a, alen)@ is either truncated or
-- zero-extended to the number of rows of @B@. The number entries written
-- to @c@ is always equal to the number of columns of @B@.
foreign import ccall "nmod_mat.h nmod_mat_nmod_vec_mul"
  nmod_mat_nmod_vec_mul :: Ptr CMpLimb -> Ptr CMpLimb -> CLong -> Ptr CNModMat -> IO ()

-- Matrix Exponentiation -------------------------------------------------------

-- | /_nmod_mat_pow/ /dest/ /mat/ /pow/ 
-- 
-- Sets \(dest = mat^{pow}\). @dest@ and @mat@ cannot be aliased.
-- Implements exponentiation by squaring.
foreign import ccall "nmod_mat.h _nmod_mat_pow"
  _nmod_mat_pow :: Ptr CNModMat -> Ptr CNModMat -> CULong -> IO ()

-- | /nmod_mat_pow/ /dest/ /mat/ /pow/ 
-- 
-- Sets \(dest = mat^{pow}\). @dest@ and @mat@ may be aliased. Implements
-- exponentiation by squaring.
foreign import ccall "nmod_mat.h nmod_mat_pow"
  nmod_mat_pow :: Ptr CNModMat -> Ptr CNModMat -> CULong -> IO ()

-- Trace -----------------------------------------------------------------------

-- | /nmod_mat_trace/ /mat/ 
-- 
-- Computes the trace of the matrix, i.e. the sum of the entries on the
-- main diagonal. The matrix is required to be square.
foreign import ccall "nmod_mat.h nmod_mat_trace"
  nmod_mat_trace :: Ptr CNModMat -> IO CMpLimb

-- Determinant and rank --------------------------------------------------------

-- | /nmod_mat_det_howell/ /A/ 
-- 
-- Returns the determinant of \(A\).
foreign import ccall "nmod_mat.h nmod_mat_det_howell"
  nmod_mat_det_howell :: Ptr CNModMat -> IO CMpLimb

-- | /nmod_mat_det/ /A/ 
-- 
-- Returns the determinant of \(A\).
foreign import ccall "nmod_mat.h nmod_mat_det"
  nmod_mat_det :: Ptr CNModMat -> IO CMpLimb

-- | /nmod_mat_rank/ /A/ 
-- 
-- Returns the rank of \(A\). The modulus of \(A\) must be a prime number.
foreign import ccall "nmod_mat.h nmod_mat_rank"
  nmod_mat_rank :: Ptr CNModMat -> IO CLong

-- Inverse ---------------------------------------------------------------------

-- | /nmod_mat_inv/ /B/ /A/ 
-- 
-- Sets \(B = A^{-1}\) and returns \(1\) if \(A\) is invertible. If \(A\)
-- is singular, returns \(0\) and sets the elements of \(B\) to undefined
-- values.
-- 
-- \(A\) and \(B\) must be square matrices with the same dimensions and
-- modulus. The modulus must be prime.
foreign import ccall "nmod_mat.h nmod_mat_inv"
  nmod_mat_inv :: Ptr CNModMat -> Ptr CNModMat -> IO CInt

-- Triangular solving ----------------------------------------------------------

-- | /nmod_mat_solve_tril/ /X/ /L/ /B/ /unit/ 
-- 
-- Sets \(X = L^{-1} B\) where \(L\) is a full rank lower triangular square
-- matrix. If @unit@ = 1, \(L\) is assumed to have ones on its main
-- diagonal, and the main diagonal will not be read. \(X\) and \(B\) are
-- allowed to be the same matrix, but no other aliasing is allowed.
-- Automatically chooses between the classical and recursive algorithms.
foreign import ccall "nmod_mat.h nmod_mat_solve_tril"
  nmod_mat_solve_tril :: Ptr CNModMat -> Ptr CNModMat -> Ptr CNModMat -> CInt -> IO ()

-- | /nmod_mat_solve_tril_classical/ /X/ /L/ /B/ /unit/ 
-- 
-- Sets \(X = L^{-1} B\) where \(L\) is a full rank lower triangular square
-- matrix. If @unit@ = 1, \(L\) is assumed to have ones on its main
-- diagonal, and the main diagonal will not be read. \(X\) and \(B\) are
-- allowed to be the same matrix, but no other aliasing is allowed. Uses
-- forward substitution.
foreign import ccall "nmod_mat.h nmod_mat_solve_tril_classical"
  nmod_mat_solve_tril_classical :: Ptr CNModMat -> Ptr CNModMat -> Ptr CNModMat -> CInt -> IO ()

-- | /nmod_mat_solve_tril_recursive/ /X/ /L/ /B/ /unit/ 
-- 
-- Sets \(X = L^{-1} B\) where \(L\) is a full rank lower triangular square
-- matrix. If @unit@ = 1, \(L\) is assumed to have ones on its main
-- diagonal, and the main diagonal will not be read. \(X\) and \(B\) are
-- allowed to be the same matrix, but no other aliasing is allowed.
-- 
-- Uses the block inversion formula
-- 
-- \[\begin{aligned}
-- `
-- \begin{pmatrix} A & 0 \\ C & D \end{pmatrix}^{-1}
-- \begin{pmatrix} X \\ Y \end{pmatrix} =
-- \begin{pmatrix} A^{-1} X \\ D^{-1} ( Y - C A^{-1} X ) \end{pmatrix}
-- \end{aligned}\]
-- 
-- to reduce the problem to matrix multiplication and triangular solving of
-- smaller systems.
foreign import ccall "nmod_mat.h nmod_mat_solve_tril_recursive"
  nmod_mat_solve_tril_recursive :: Ptr CNModMat -> Ptr CNModMat -> Ptr CNModMat -> CInt -> IO ()

-- | /nmod_mat_solve_triu/ /X/ /U/ /B/ /unit/ 
-- 
-- Sets \(X = U^{-1} B\) where \(U\) is a full rank upper triangular square
-- matrix. If @unit@ = 1, \(U\) is assumed to have ones on its main
-- diagonal, and the main diagonal will not be read. \(X\) and \(B\) are
-- allowed to be the same matrix, but no other aliasing is allowed.
-- Automatically chooses between the classical and recursive algorithms.
foreign import ccall "nmod_mat.h nmod_mat_solve_triu"
  nmod_mat_solve_triu :: Ptr CNModMat -> Ptr CNModMat -> Ptr CNModMat -> CInt -> IO ()

-- | /nmod_mat_solve_triu_classical/ /X/ /U/ /B/ /unit/ 
-- 
-- Sets \(X = U^{-1} B\) where \(U\) is a full rank upper triangular square
-- matrix. If @unit@ = 1, \(U\) is assumed to have ones on its main
-- diagonal, and the main diagonal will not be read. \(X\) and \(B\) are
-- allowed to be the same matrix, but no other aliasing is allowed. Uses
-- forward substitution.
foreign import ccall "nmod_mat.h nmod_mat_solve_triu_classical"
  nmod_mat_solve_triu_classical :: Ptr CNModMat -> Ptr CNModMat -> Ptr CNModMat -> CInt -> IO ()

-- | /nmod_mat_solve_triu_recursive/ /X/ /U/ /B/ /unit/ 
-- 
-- Sets \(X = U^{-1} B\) where \(U\) is a full rank upper triangular square
-- matrix. If @unit@ = 1, \(U\) is assumed to have ones on its main
-- diagonal, and the main diagonal will not be read. \(X\) and \(B\) are
-- allowed to be the same matrix, but no other aliasing is allowed.
-- 
-- Uses the block inversion formula
-- 
-- \[\begin{aligned}
-- `
-- \begin{pmatrix} A & B \\ 0 & D \end{pmatrix}^{-1}
-- \begin{pmatrix} X \\ Y \end{pmatrix} =
-- \begin{pmatrix} A^{-1} (X - B D^{-1} Y) \\ D^{-1} Y \end{pmatrix}
-- \end{aligned}\]
-- 
-- to reduce the problem to matrix multiplication and triangular solving of
-- smaller systems.
foreign import ccall "nmod_mat.h nmod_mat_solve_triu_recursive"
  nmod_mat_solve_triu_recursive :: Ptr CNModMat -> Ptr CNModMat -> Ptr CNModMat -> CInt -> IO ()

-- Nonsingular square solving --------------------------------------------------

-- | /nmod_mat_solve/ /X/ /A/ /B/ 
-- 
-- Solves the matrix-matrix equation \(AX = B\) over
-- \(\mathbb{Z} / p \mathbb{Z}\) where \(p\) is the modulus of \(X\) which
-- must be a prime number. \(X\), \(A\), and \(B\) should have the same
-- moduli.
-- 
-- Returns \(1\) if \(A\) has full rank; otherwise returns \(0\) and sets
-- the elements of \(X\) to undefined values.
-- 
-- The matrix \(A\) must be square.
foreign import ccall "nmod_mat.h nmod_mat_solve"
  nmod_mat_solve :: Ptr CNModMat -> Ptr CNModMat -> Ptr CNModMat -> IO CInt

-- | /nmod_mat_can_solve_inner/ /rank/ /perm/ /pivots/ /X/ /A/ /B/ 
-- 
-- As for @nmod_mat_can_solve@ except that if \(rank\) is not \(NULL\) the
-- value it points to will be set to the rank of \(A\). If \(perm\) is not
-- \(NULL\) then it must be a valid initialised permutation whose length is
-- the number of rows of \(A\). After the function call it will be set to
-- the row permutation given by LU decomposition of \(A\). If \(pivots\) is
-- not \(NULL\) then it must an initialised vector. Only the first
-- \(*rank\) of these will be set by the function call. They are set to the
-- columns of the pivots chosen by the LU decomposition of \(A\).
foreign import ccall "nmod_mat.h nmod_mat_can_solve_inner"
  nmod_mat_can_solve_inner :: Ptr CLong -> Ptr CLong -> Ptr CLong -> Ptr CNModMat -> Ptr CNModMat -> Ptr CNModMat -> IO CInt

-- | /nmod_mat_can_solve/ /X/ /A/ /B/ 
-- 
-- Solves the matrix-matrix equation \(AX = B\) over
-- \(\mathbb{Z} / p \mathbb{Z}\) where \(p\) is the modulus of \(X\) which
-- must be a prime number. \(X\), \(A\), and \(B\) should have the same
-- moduli.
-- 
-- Returns \(1\) if a solution exists; otherwise returns \(0\) and sets the
-- elements of \(X\) to zero. If more than one solution exists, one of the
-- valid solutions is given.
-- 
-- There are no restrictions on the shape of \(A\) and it may be singular.
foreign import ccall "nmod_mat.h nmod_mat_can_solve"
  nmod_mat_can_solve :: Ptr CNModMat -> Ptr CNModMat -> Ptr CNModMat -> IO CInt

-- | /nmod_mat_solve_vec/ /x/ /A/ /b/ 
-- 
-- Solves the matrix-vector equation \(Ax = b\) over
-- \(\mathbb{Z} / p \mathbb{Z}\) where \(p\) is the modulus of \(A\) which
-- must be a prime number.
-- 
-- Returns \(1\) if \(A\) has full rank; otherwise returns \(0\) and sets
-- the elements of \(x\) to undefined values.
foreign import ccall "nmod_mat.h nmod_mat_solve_vec"
  nmod_mat_solve_vec :: Ptr CMpLimb -> Ptr CNModMat -> Ptr CMpLimb -> IO CInt

-- LU decomposition ------------------------------------------------------------

-- | /nmod_mat_lu/ /P/ /A/ /rank_check/ 
-- 
-- Computes a generalised LU decomposition \(LU = PA\) of a given matrix
-- \(A\), returning the rank of \(A\).
-- 
-- If \(A\) is a nonsingular square matrix, it will be overwritten with a
-- unit diagonal lower triangular matrix \(L\) and an upper triangular
-- matrix \(U\) (the diagonal of \(L\) will not be stored explicitly).
-- 
-- If \(A\) is an arbitrary matrix of rank \(r\), \(U\) will be in row
-- echelon form having \(r\) nonzero rows, and \(L\) will be lower
-- triangular but truncated to \(r\) columns, having implicit ones on the
-- \(r\) first entries of the main diagonal. All other entries will be
-- zero.
-- 
-- If a nonzero value for @rank_check@ is passed, the function will abandon
-- the output matrix in an undefined state and return 0 if \(A\) is
-- detected to be rank-deficient.
-- 
-- The /classical/ version uses direct Gaussian elimination. The
-- /classical_delayed/ version also uses Gaussian elimination, but performs
-- delayed modular reductions. The /recursive/ version uses block recursive
-- decomposition. The default function chooses an algorithm automatically.
foreign import ccall "nmod_mat.h nmod_mat_lu"
  nmod_mat_lu :: Ptr CLong -> Ptr CNModMat -> CInt -> IO CLong

-- Reduced row echelon form ----------------------------------------------------

-- | /nmod_mat_rref/ /A/ 
-- 
-- Puts \(A\) in reduced row echelon form and returns the rank of \(A\).
-- 
-- The rref is computed by first obtaining an unreduced row echelon form
-- via LU decomposition and then solving an additional triangular system.
foreign import ccall "nmod_mat.h nmod_mat_rref"
  nmod_mat_rref :: Ptr CNModMat -> IO CLong

-- | /nmod_mat_reduce_row/ /A/ /P/ /L/ /n/ 
-- 
-- Reduce row n of the matrix \(A\), assuming the prior rows are in Gauss
-- form. However those rows may not be in order. The entry \(i\) of the
-- array \(P\) is the row of \(A\) which has a pivot in the \(i\)-th
-- column. If no such row exists, the entry of \(P\) will be \(-1\). The
-- function returns the column in which the \(n\)-th row has a pivot after
-- reduction. This will always be chosen to be the first available column
-- for a pivot from the left. This information is also updated in \(P\).
-- Entry \(i\) of the array \(L\) contains the number of possibly nonzero
-- columns of \(A\) row \(i\). This speeds up reduction in the case that
-- \(A\) is chambered on the right. Otherwise the entries of \(L\) can all
-- be set to the number of columns of \(A\). We require the entries of
-- \(L\) to be monotonic increasing.
foreign import ccall "nmod_mat.h nmod_mat_reduce_row"
  nmod_mat_reduce_row :: Ptr CNModMat -> Ptr CLong -> Ptr CLong -> CLong -> IO CLong

-- Nullspace -------------------------------------------------------------------

-- | /nmod_mat_nullspace/ /X/ /A/ 
-- 
-- Computes the nullspace of \(A\) and returns the nullity.
-- 
-- More precisely, this function sets \(X\) to a maximum rank matrix such
-- that \(AX = 0\) and returns the rank of \(X\). The columns of \(X\) will
-- form a basis for the nullspace of \(A\).
-- 
-- \(X\) must have sufficient space to store all basis vectors in the
-- nullspace.
-- 
-- This function computes the reduced row echelon form and then reads off
-- the basis vectors.
foreign import ccall "nmod_mat.h nmod_mat_nullspace"
  nmod_mat_nullspace :: Ptr CNModMat -> Ptr CNModMat -> IO CLong

-- Transforms ------------------------------------------------------------------

-- | /nmod_mat_similarity/ /M/ /r/ /d/ 
-- 
-- Applies a similarity transform to the \(n\times n\) matrix \(M\)
-- in-place.
-- 
-- If \(P\) is the \(n\times n\) identity matrix the zero entries of whose
-- row \(r\) (0-indexed) have been replaced by \(d\), this transform is
-- equivalent to \(M = P^{-1}MP\).
-- 
-- Similarity transforms preserve the determinant, characteristic
-- polynomial and minimal polynomial.
-- 
-- The value \(d\) is required to be reduced modulo the modulus of the
-- entries in the matrix.
foreign import ccall "nmod_mat.h nmod_mat_similarity"
  nmod_mat_similarity :: Ptr CNModMat -> CLong -> CULong -> IO ()

-- Characteristic polynomial ---------------------------------------------------

-- | /nmod_mat_charpoly_berkowitz/ /p/ /M/ 
-- 
-- Compute the characteristic polynomial \(p\) of the matrix \(M\). The
-- matrix is required to be square, otherwise an exception is raised. The
-- /danilevsky/ algorithm assumes that the modulus is prime.
foreign import ccall "nmod_mat.h nmod_mat_charpoly_berkowitz"
  nmod_mat_charpoly_berkowitz :: Ptr CNModPoly -> Ptr CNModMat -> IO ()

-- Minimal polynomial ----------------------------------------------------------

-- | /nmod_mat_minpoly/ /p/ /M/ 
-- 
-- Compute the minimal polynomial \(p\) of the matrix \(M\). The matrix is
-- required to be square, otherwise an exception is raised.
foreign import ccall "nmod_mat.h nmod_mat_minpoly"
  nmod_mat_minpoly :: Ptr CNModPoly -> Ptr CNModMat -> IO ()

-- Strong echelon form and Howell form -----------------------------------------

-- | /nmod_mat_strong_echelon_form/ /A/ 
-- 
-- Puts \(A\) into strong echelon form. The Howell form and the strong
-- echelon form are equal up to permutation of the rows, see
-- < [FieHof2014]> for a definition of the strong echelon form and the
-- algorithm used here. Note that < [FieHof2014]> defines strong echelon
-- form as a lower left normal form, while the implemented version returns
-- an upper right normal form, agreeing with the definition of Howell form
-- in < [StoMul1998]>.
-- 
-- \(A\) must have at least as many rows as columns.
foreign import ccall "nmod_mat.h nmod_mat_strong_echelon_form"
  nmod_mat_strong_echelon_form :: Ptr CNModMat -> IO ()

-- | /nmod_mat_howell_form/ /A/ 
-- 
-- Puts \(A\) into Howell form and returns the number of non-zero rows. For
-- a definition of the Howell form see < [StoMul1998]>. The Howell form is
-- computed by first putting \(A\) into strong echelon form and then
-- ordering the rows.
-- 
-- \(A\) must have at least as many rows as columns.
foreign import ccall "nmod_mat.h nmod_mat_howell_form"
  nmod_mat_howell_form :: Ptr CNModMat -> IO CLong

