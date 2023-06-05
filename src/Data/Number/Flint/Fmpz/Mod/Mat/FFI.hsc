{-# language
    CApiFFI
  , FlexibleInstances
  , ForeignFunctionInterface
  , MultiParamTypeClasses
  , TupleSections
  , TypeFamilies
  #-}

module Data.Number.Flint.Fmpz.Mod.Mat.FFI (
  -- * Matrices over integers mod n
    FmpzModMat (..)
  , CFmpzModMat (..)
  , newFmpzModMat
  , withFmpzModMat
  , withNewFmpzModMat
  -- * Types, macros and constants
  -- * Element access
  , fmpz_mod_mat_entry
  , fmpz_mod_mat_set_entry
  -- * Memory management
  , fmpz_mod_mat_init
  , fmpz_mod_mat_init_set
  , fmpz_mod_mat_clear
  , fmpz_mod_mat_nrows
  , fmpz_mod_mat_ncols
  , _fmpz_mod_mat_set_mod
  , fmpz_mod_mat_one
  , fmpz_mod_mat_zero
  , fmpz_mod_mat_swap
  , fmpz_mod_mat_swap_entrywise
  , fmpz_mod_mat_is_empty
  , fmpz_mod_mat_is_square
  , _fmpz_mod_mat_reduce
  -- * Random generation
  , fmpz_mod_mat_randtest
  -- * Windows and concatenation
  , fmpz_mod_mat_window_init
  , fmpz_mod_mat_window_clear
  , fmpz_mod_mat_concat_horizontal
  , fmpz_mod_mat_concat_vertical
  -- * Input and output
  , fmpz_mod_mat_print_pretty
  -- * Comparison
  , fmpz_mod_mat_is_zero
  -- * Set and transpose
  , fmpz_mod_mat_set
  , fmpz_mod_mat_transpose
  -- * Conversions
  , fmpz_mod_mat_set_fmpz_mat
  , fmpz_mod_mat_get_fmpz_mat
  -- * Addition and subtraction
  , fmpz_mod_mat_add
  , fmpz_mod_mat_sub
  , fmpz_mod_mat_neg
  -- * Scalar arithmetic
  , fmpz_mod_mat_scalar_mul_si
  , fmpz_mod_mat_scalar_mul_ui
  , fmpz_mod_mat_scalar_mul_fmpz
  -- * Matrix multiplication
  , fmpz_mod_mat_mul
  , _fmpz_mod_mat_mul_classical_threaded_pool_op
  -- , _fmpz_mod_mat_mul_classical_threaded_op
  , fmpz_mod_mat_mul_classical_threaded
  , fmpz_mod_mat_sqr
  , fmpz_mod_mat_mul_fmpz_vec
  , fmpz_mod_mat_fmpz_vec_mul
  -- * Trace
  , fmpz_mod_mat_trace
  -- * Gaussian elimination
  , fmpz_mod_mat_rref
  -- * Strong echelon form and Howell form
  , fmpz_mod_mat_strong_echelon_form
  , fmpz_mod_mat_howell_form
  -- * Inverse
  , fmpz_mod_mat_inv
  -- * LU decomposition
  , fmpz_mod_mat_lu
  -- * Triangular solving
  , fmpz_mod_mat_solve_tril
  , fmpz_mod_mat_solve_triu
  -- * Solving
  , fmpz_mod_mat_solve
  , fmpz_mod_mat_can_solve
  -- * Transforms
  , fmpz_mod_mat_similarity
) where

-- matrices over integers mod n ------------------------------------------------

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr )
import Foreign.Storable
import Foreign.Marshal ( free )

import Data.Number.Flint.Flint
import Data.Number.Flint.ThreadPool

import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Mat
import Data.Number.Flint.Fmpz.Poly
import Data.Number.Flint.Fmpz.Mod
import Data.Number.Flint.Fmpq

#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpq.h>
#include <flint/fmpz_mod_mat.h>

-- fmpz_mod_mat_t --------------------------------------------------------------

data FmpzModMat = FmpzModMat {-# UNPACK #-} !(ForeignPtr CFmpzModMat)
type CFmpzModMat = CFlint FmpzModMat

instance Storable CFmpzModMat where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fmpz_mod_mat_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fmpz_mod_mat_t}
  peek = undefined
  poke = undefined

newFmpzModMat nrows ncols n = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x ->
    withFmpz n $ \n -> 
      fmpz_mod_mat_init x nrows ncols n
  addForeignPtrFinalizer p_fmpz_mod_mat_clear x
  return $ FmpzModMat x

{-# INLINE withFmpzModMat #-}
withFmpzModMat (FmpzModMat x) f = do
  withForeignPtr x $ \px -> f px >>= return . (FmpzModMat x,)

{-# INLINE withNewFmpzModMat #-}
withNewFmpzModMat nrows ncols n f =
  newFmpzModMat nrows ncols n >>= flip withFmpzModMat f
  
-- Element access --------------------------------------------------------------

-- | /fmpz_mod_mat_entry/ /mat/ /i/ /j/ 
-- 
-- Return a reference to the element at row @i@ and column @j@ of @mat@.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_entry"
  fmpz_mod_mat_entry :: Ptr CFmpzModMat -> CLong -> CLong -> IO (Ptr CFmpz)

-- | /fmpz_mod_mat_set_entry/ /mat/ /i/ /j/ /val/ 
-- 
-- Set the entry at row @i@ and column @j@ of @mat@ to @val@.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_set_entry"
  fmpz_mod_mat_set_entry :: Ptr CFmpzModMat -> CLong -> CLong -> Ptr CFmpz -> IO ()

-- Memory management -----------------------------------------------------------

-- | /fmpz_mod_mat_init/ /mat/ /rows/ /cols/ /n/ 
-- 
-- Initialise @mat@ as a matrix with the given number of @rows@ and @cols@
-- and modulus @n@.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_init"
  fmpz_mod_mat_init :: Ptr CFmpzModMat -> CLong -> CLong -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_mat_init_set/ /mat/ /src/ 
-- 
-- Initialise @mat@ and set it equal to the matrix @src@, including the
-- number of rows and columns and the modulus.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_init_set"
  fmpz_mod_mat_init_set :: Ptr CFmpzModMat -> Ptr CFmpzModMat -> IO ()

-- | /fmpz_mod_mat_clear/ /mat/ 
-- 
-- Clear @mat@ and release any memory it used.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_clear"
  fmpz_mod_mat_clear :: Ptr CFmpzModMat -> IO ()

foreign import ccall "fmpz_mod_mat.h &fmpz_mod_mat_clear"
  p_fmpz_mod_mat_clear :: FunPtr (Ptr CFmpzModMat -> IO ())

-- Basic manipulation ----------------------------------------------------------

-- | /fmpz_mod_mat_nrows/ /mat/ 
-- 
-- Return the number of rows of @mat@.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_nrows"
  fmpz_mod_mat_nrows :: Ptr CFmpzModMat -> IO CLong

-- | /fmpz_mod_mat_ncols/ /mat/ 
-- 
-- Return the number of columns of @mat@.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_ncols"
  fmpz_mod_mat_ncols :: Ptr CFmpzModMat -> IO CLong

-- | /_fmpz_mod_mat_set_mod/ /mat/ /n/ 
-- 
-- Set the modulus of the matrix @mat@ to @n@.
foreign import ccall "fmpz_mod_mat.h _fmpz_mod_mat_set_mod"
  _fmpz_mod_mat_set_mod :: Ptr CFmpzModMat -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_mat_one/ /mat/ 
-- 
-- Set @mat@ to the identity matrix (ones down the diagonal).
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_one"
  fmpz_mod_mat_one :: Ptr CFmpzModMat -> IO ()

-- | /fmpz_mod_mat_zero/ /mat/ 
-- 
-- Set @mat@ to the zero matrix.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_zero"
  fmpz_mod_mat_zero :: Ptr CFmpzModMat -> IO ()

-- | /fmpz_mod_mat_swap/ /mat1/ /mat2/ 
-- 
-- Efficiently swap the matrices @mat1@ and @mat2@.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_swap"
  fmpz_mod_mat_swap :: Ptr CFmpzModMat -> Ptr CFmpzModMat -> IO ()

-- | /fmpz_mod_mat_swap_entrywise/ /mat1/ /mat2/ 
-- 
-- Swaps two matrices by swapping the individual entries rather than
-- swapping the contents of the structs.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_swap_entrywise"
  fmpz_mod_mat_swap_entrywise :: Ptr CFmpzModMat -> Ptr CFmpzModMat -> IO ()

-- | /fmpz_mod_mat_is_empty/ /mat/ 
-- 
-- Return \(1\) if @mat@ has either zero rows or columns.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_is_empty"
  fmpz_mod_mat_is_empty :: Ptr CFmpzModMat -> IO CInt

-- | /fmpz_mod_mat_is_square/ /mat/ 
-- 
-- Return \(1\) if @mat@ has the same number of rows and columns.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_is_square"
  fmpz_mod_mat_is_square :: Ptr CFmpzModMat -> IO CInt

-- | /_fmpz_mod_mat_reduce/ /mat/ 
-- 
-- Reduce all the entries of @mat@ by the modulus @n@. This function is
-- only needed internally.
foreign import ccall "fmpz_mod_mat.h _fmpz_mod_mat_reduce"
  _fmpz_mod_mat_reduce :: Ptr CFmpzModMat -> IO ()

-- Random generation -----------------------------------------------------------

-- | /fmpz_mod_mat_randtest/ /mat/ /state/ 
-- 
-- Generate a random matrix with the existing dimensions and entries in
-- \([0, n)\) where @n@ is the modulus.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_randtest"
  fmpz_mod_mat_randtest :: Ptr CFmpzModMat -> Ptr CFRandState -> IO ()

-- Windows and concatenation ---------------------------------------------------

-- | /fmpz_mod_mat_window_init/ /window/ /mat/ /r1/ /c1/ /r2/ /c2/ 
-- 
-- Initializes the matrix @window@ to be an @r2 - r1@ by @c2 - c1@
-- submatrix of @mat@ whose @(0, 0)@ entry is the @(r1, c1)@ entry of
-- @mat@. The memory for the elements of @window@ is shared with @mat@.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_window_init"
  fmpz_mod_mat_window_init :: Ptr CFmpzModMat -> Ptr CFmpzModMat -> CLong -> CLong -> CLong -> CLong -> IO ()

-- | /fmpz_mod_mat_window_clear/ /window/ 
-- 
-- Clears the matrix @window@ and releases any memory that it uses. Note
-- that the memory to the underlying matrix that @window@ points to is not
-- freed.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_window_clear"
  fmpz_mod_mat_window_clear :: Ptr CFmpzModMat -> IO ()

-- | /fmpz_mod_mat_concat_horizontal/ /res/ /mat1/ /mat2/ 
-- 
-- Sets @res@ to vertical concatenation of (@mat1@, @mat2@) in that order.
-- Matrix dimensions : @mat1@ : \(m \times n\), @mat2@ : \(k \times n\),
-- @res@ : \((m + k) \times n\).
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_concat_horizontal"
  fmpz_mod_mat_concat_horizontal :: Ptr CFmpzModMat -> Ptr CFmpzModMat -> Ptr CFmpzModMat -> IO ()

-- | /fmpz_mod_mat_concat_vertical/ /res/ /mat1/ /mat2/ 
-- 
-- Sets @res@ to horizontal concatenation of (@mat1@, @mat2@) in that
-- order. Matrix dimensions : @mat1@ : \(m \times n\), @mat2@ :
-- \(m \times k\), @res@ : \(m \times (n + k)\).
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_concat_vertical"
  fmpz_mod_mat_concat_vertical :: Ptr CFmpzModMat -> Ptr CFmpzModMat -> Ptr CFmpzModMat -> IO ()

-- Input and output ------------------------------------------------------------

-- | /fmpz_mod_mat_print_pretty/ /mat/ 
-- 
-- Prints the given matrix to @stdout@. The format is an opening square
-- bracket then on each line a row of the matrix, followed by a closing
-- square bracket. Each row is written as an opening square bracket
-- followed by a space separated list of coefficients followed by a closing
-- square bracket.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_print_pretty"
  fmpz_mod_mat_print_pretty :: Ptr CFmpzModMat -> IO ()

-- Comparison ------------------------------------------------------------------

-- | /fmpz_mod_mat_is_zero/ /mat/ 
-- 
-- Return \(1\) if @mat@ is the zero matrix.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_is_zero"
  fmpz_mod_mat_is_zero :: Ptr CFmpzModMat -> IO CInt

-- Set and transpose -----------------------------------------------------------

-- | /fmpz_mod_mat_set/ /B/ /A/ 
-- 
-- Set @B@ to equal @A@.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_set"
  fmpz_mod_mat_set :: Ptr CFmpzModMat -> Ptr CFmpzModMat -> IO ()

-- | /fmpz_mod_mat_transpose/ /B/ /A/ 
-- 
-- Set @B@ to the transpose of @A@.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_transpose"
  fmpz_mod_mat_transpose :: Ptr CFmpzModMat -> Ptr CFmpzModMat -> IO ()

-- Conversions -----------------------------------------------------------------

-- | /fmpz_mod_mat_set_fmpz_mat/ /A/ /B/ 
-- 
-- Set @A@ to the matrix @B@ reducing modulo the modulus of @A@.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_set_fmpz_mat"
  fmpz_mod_mat_set_fmpz_mat :: Ptr CFmpzModMat -> Ptr CFmpzMat -> IO ()

-- | /fmpz_mod_mat_get_fmpz_mat/ /A/ /B/ 
-- 
-- Set @A@ to a lift of @B@.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_get_fmpz_mat"
  fmpz_mod_mat_get_fmpz_mat :: Ptr CFmpzMat -> Ptr CFmpzModMat -> IO ()

-- Addition and subtraction ----------------------------------------------------

-- | /fmpz_mod_mat_add/ /C/ /A/ /B/ 
-- 
-- Set @C@ to \(A + B\).
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_add"
  fmpz_mod_mat_add :: Ptr CFmpzModMat -> Ptr CFmpzModMat -> Ptr CFmpzModMat -> IO ()

-- | /fmpz_mod_mat_sub/ /C/ /A/ /B/ 
-- 
-- Set @C@ to \(A - B\).
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_sub"
  fmpz_mod_mat_sub :: Ptr CFmpzModMat -> Ptr CFmpzModMat -> Ptr CFmpzModMat -> IO ()

-- | /fmpz_mod_mat_neg/ /B/ /A/ 
-- 
-- Set @B@ to \(-A\).
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_neg"
  fmpz_mod_mat_neg :: Ptr CFmpzModMat -> Ptr CFmpzModMat -> IO ()

-- Scalar arithmetic -----------------------------------------------------------

-- | /fmpz_mod_mat_scalar_mul_si/ /B/ /A/ /c/ 
-- 
-- Set @B@ to \(cA\) where @c@ is a constant.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_scalar_mul_si"
  fmpz_mod_mat_scalar_mul_si :: Ptr CFmpzModMat -> Ptr CFmpzModMat -> CLong -> IO ()

-- | /fmpz_mod_mat_scalar_mul_ui/ /B/ /A/ /c/ 
-- 
-- Set @B@ to \(cA\) where @c@ is a constant.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_scalar_mul_ui"
  fmpz_mod_mat_scalar_mul_ui :: Ptr CFmpzModMat -> Ptr CFmpzModMat -> CLong -> IO ()

-- | /fmpz_mod_mat_scalar_mul_fmpz/ /B/ /A/ /c/ 
-- 
-- Set @B@ to \(cA\) where @c@ is a constant.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_scalar_mul_fmpz"
  fmpz_mod_mat_scalar_mul_fmpz :: Ptr CFmpzModMat -> Ptr CFmpzModMat -> Ptr CFmpz -> IO ()

-- Matrix multiplication -------------------------------------------------------

-- | /fmpz_mod_mat_mul/ /C/ /A/ /B/ 
-- 
-- Set @C@ to @A\\times B@. The number of rows of @B@ must match the number
-- of columns of @A@.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_mul"
  fmpz_mod_mat_mul :: Ptr CFmpzModMat -> Ptr CFmpzModMat -> Ptr CFmpzModMat -> IO ()

-- | /_fmpz_mod_mat_mul_classical_threaded_pool_op/ /D/ /C/ /A/ /B/ /op/ /threads/ /num_threads/ 
-- 
-- Set @D@ to @A\\times B + op*C@ where @op@ is @+1@, @-1@ or @0@.
foreign import ccall "fmpz_mod_mat.h _fmpz_mod_mat_mul_classical_threaded_pool_op"
  _fmpz_mod_mat_mul_classical_threaded_pool_op :: Ptr CFmpzModMat -> Ptr CFmpzModMat -> Ptr CFmpzModMat -> Ptr CFmpzModMat -> CInt -> Ptr CThreadPoolHandle -> CLong -> IO ()

-- -- | /_fmpz_mod_mat_mul_classical_threaded_op/ /D/ /C/ /A/ /B/ /op/ 
-- -- 
-- -- Set @D@ to @A\\times B + op*C@ where @op@ is @+1@, @-1@ or @0@.
-- foreign import ccall "fmpz_mod_mat.h _fmpz_mod_mat_mul_classical_threaded_op"
--   _fmpz_mod_mat_mul_classical_threaded_op :: Ptr CFmpzModMat -> Ptr CFmpzModMat -> Ptr CFmpzModMat -> Ptr CFmpzModMat -> CInt -> IO ()

-- | /fmpz_mod_mat_mul_classical_threaded/ /C/ /A/ /B/ 
-- 
-- Set @C@ to @A\\times B@. The number of rows of @B@ must match the number
-- of columns of @A@.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_mul_classical_threaded"
  fmpz_mod_mat_mul_classical_threaded :: Ptr CFmpzModMat -> Ptr CFmpzModMat -> Ptr CFmpzModMat -> IO ()

-- | /fmpz_mod_mat_sqr/ /B/ /A/ 
-- 
-- Set @B@ to @A^2@. The matrix @A@ must be square.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_sqr"
  fmpz_mod_mat_sqr :: Ptr CFmpzModMat -> Ptr CFmpzModMat -> IO ()

-- | /fmpz_mod_mat_mul_fmpz_vec/ /c/ /A/ /b/ /blen/ 
-- 
-- Compute a matrix-vector product of @A@ and @(b, blen)@ and store the
-- result in @c@. The vector @(b, blen)@ is either truncated or
-- zero-extended to the number of columns of @A@. The number entries
-- written to @c@ is always equal to the number of rows of @A@.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_mul_fmpz_vec"
  fmpz_mod_mat_mul_fmpz_vec :: Ptr CFmpz -> Ptr CFmpzModMat -> Ptr CFmpz -> CLong -> IO ()

-- | /fmpz_mod_mat_fmpz_vec_mul/ /c/ /a/ /alen/ /B/ 
-- 
-- Compute a vector-matrix product of @(a, alen)@ and @B@ and and store the
-- result in @c@. The vector @(a, alen)@ is either truncated or
-- zero-extended to the number of rows of @B@. The number entries written
-- to @c@ is always equal to the number of columns of @B@.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_fmpz_vec_mul"
  fmpz_mod_mat_fmpz_vec_mul :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpzModMat -> IO ()

-- Trace -----------------------------------------------------------------------

-- | /fmpz_mod_mat_trace/ /trace/ /mat/ 
-- 
-- Set @trace@ to the trace of the matrix @mat@.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_trace"
  fmpz_mod_mat_trace :: Ptr CFmpz -> Ptr CFmpzModMat -> IO ()

-- Gaussian elimination --------------------------------------------------------

-- | /fmpz_mod_mat_rref/ /perm/ /mat/ 
-- 
-- Uses Gauss-Jordan elimination to set @mat@ to its reduced row echelon
-- form and returns the rank of @mat@.
-- 
-- If @perm@ is non-@NULL@, the permutation of rows in the matrix will also
-- be applied to @perm@.
-- 
-- The modulus is assumed to be prime.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_rref"
  fmpz_mod_mat_rref :: Ptr CLong -> Ptr CFmpzModMat -> IO CLong

-- Strong echelon form and Howell form -----------------------------------------

-- | /fmpz_mod_mat_strong_echelon_form/ /mat/ 
-- 
-- Transforms \(mat\) into the strong echelon form of \(mat\). The Howell
-- form and the strong echelon form are equal up to permutation of the
-- rows, see < [FieHof2014]> for a definition of the strong echelon form
-- and the algorithm used here.
-- 
-- \(mat\) must have at least as many rows as columns.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_strong_echelon_form"
  fmpz_mod_mat_strong_echelon_form :: Ptr CFmpzModMat -> IO ()

-- | /fmpz_mod_mat_howell_form/ /mat/ 
-- 
-- Transforms \(mat\) into the Howell form of \(mat\). For a definition of
-- the Howell form see < [StoMul1998]>. The Howell form is computed by
-- first putting \(mat\) into strong echelon form and then ordering the
-- rows.
-- 
-- \(mat\) must have at least as many rows as columns.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_howell_form"
  fmpz_mod_mat_howell_form :: Ptr CFmpzModMat -> IO CLong

-- Inverse ---------------------------------------------------------------------

-- | /fmpz_mod_mat_inv/ /B/ /A/ /ctx/ 
-- 
-- Sets \(B = A^{-1}\) and returns \(1\) if \(A\) is invertible. If \(A\)
-- is singular, returns \(0\) and sets the elements of \(B\) to undefined
-- values.
-- 
-- \(A\) and \(B\) must be square matrices with the same dimensions.
-- 
-- The modulus is assumed to be prime.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_inv"
  fmpz_mod_mat_inv :: Ptr CFmpzModMat -> Ptr CFmpzModMat -> Ptr CFmpzModCtx -> IO CInt

-- LU decomposition ------------------------------------------------------------

-- | /fmpz_mod_mat_lu/ /P/ /A/ /rank_check/ /ctx/ 
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
-- The modulus is assumed to be prime.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_lu"
  fmpz_mod_mat_lu :: Ptr CLong -> Ptr CFmpzModMat -> CInt -> Ptr CFmpzModCtx -> IO CLong

-- Triangular solving ----------------------------------------------------------

-- | /fmpz_mod_mat_solve_tril/ /X/ /L/ /B/ /unit/ /ctx/ 
-- 
-- Sets \(X = L^{-1} B\) where \(L\) is a full rank lower triangular square
-- matrix. If @unit@ = 1, \(L\) is assumed to have ones on its main
-- diagonal, and the main diagonal will not be read. \(X\) and \(B\) are
-- allowed to be the same matrix, but no other aliasing is allowed.
-- Automatically chooses between the classical and recursive algorithms.
-- 
-- The modulus is assumed to be prime.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_solve_tril"
  fmpz_mod_mat_solve_tril :: Ptr CFmpzModMat -> Ptr CFmpzModMat -> Ptr CFmpzModMat -> CInt -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_mat_solve_triu/ /X/ /U/ /B/ /unit/ /ctx/ 
-- 
-- Sets \(X = U^{-1} B\) where \(U\) is a full rank upper triangular square
-- matrix. If @unit@ = 1, \(U\) is assumed to have ones on its main
-- diagonal, and the main diagonal will not be read. \(X\) and \(B\) are
-- allowed to be the same matrix, but no other aliasing is allowed.
-- Automatically chooses between the classical and recursive algorithms.
-- 
-- The modulus is assumed to be prime.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_solve_triu"
  fmpz_mod_mat_solve_triu :: Ptr CFmpzModMat -> Ptr CFmpzModMat -> Ptr CFmpzModMat -> CInt -> Ptr CFmpzModCtx -> IO ()

-- Solving ---------------------------------------------------------------------

-- | /fmpz_mod_mat_solve/ /X/ /A/ /B/ /ctx/ 
-- 
-- Solves the matrix-matrix equation \(AX = B\).
-- 
-- Returns \(1\) if \(A\) has full rank; otherwise returns \(0\) and sets
-- the elements of \(X\) to undefined values.
-- 
-- The matrix \(A\) must be square.
-- 
-- The modulus is assumed to be prime.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_solve"
  fmpz_mod_mat_solve :: Ptr CFmpzModMat -> Ptr CFmpzModMat -> Ptr CFmpzModMat -> Ptr CFmpzModCtx -> IO CInt

-- | /fmpz_mod_mat_can_solve/ /X/ /A/ /B/ /ctx/ 
-- 
-- Solves the matrix-matrix equation \(AX = B\) over \(Fp\).
-- 
-- Returns \(1\) if a solution exists; otherwise returns \(0\) and sets the
-- elements of \(X\) to zero. If more than one solution exists, one of the
-- valid solutions is given.
-- 
-- There are no restrictions on the shape of \(A\) and it may be singular.
-- 
-- The modulus is assumed to be prime.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_can_solve"
  fmpz_mod_mat_can_solve :: Ptr CFmpzModMat -> Ptr CFmpzModMat -> Ptr CFmpzModMat -> Ptr CFmpzModCtx -> IO CInt

-- Transforms ------------------------------------------------------------------

-- | /fmpz_mod_mat_similarity/ /M/ /r/ /d/ /ctx/ 
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
-- 
-- The modulus is assumed to be prime.
foreign import ccall "fmpz_mod_mat.h fmpz_mod_mat_similarity"
  fmpz_mod_mat_similarity :: Ptr CFmpzModMat -> CLong -> Ptr CFmpz -> Ptr CFmpzModCtx -> IO ()

