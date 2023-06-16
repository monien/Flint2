{-# language
    CApiFFI
  , FlexibleInstances
  , ForeignFunctionInterface
  , TupleSections
  #-}

module Data.Number.Flint.Arb.Mat.FFI (
  -- * Matrices over the real numbers
  -- * Types
    ArbMat (..)
  , CArbMat (..)
  , newArbMat
  , withArbMat
  , withNewArbMat
  -- * Memory management
  , arb_mat_init
  , arb_mat_clear
  , arb_mat_allocated_bytes
  , arb_mat_window_init
  , arb_mat_window_clear
  -- * Conversions
  , arb_mat_set
  , arb_mat_set_fmpz_mat
  , arb_mat_set_round_fmpz_mat
  , arb_mat_set_fmpq_mat
  -- * Random generation
  , arb_mat_randtest
  -- * Input and output
  , arb_mat_printd
  , arb_mat_fprintd
  -- * Comparisons
  , arb_mat_equal
  , arb_mat_overlaps
  , arb_mat_contains
  , arb_mat_contains_fmpz_mat
  , arb_mat_contains_fmpq_mat
  , arb_mat_eq
  , arb_mat_ne
  , arb_mat_is_empty
  , arb_mat_is_square
  , arb_mat_is_exact
  , arb_mat_is_zero
  , arb_mat_is_finite
  , arb_mat_is_triu
  , arb_mat_is_tril
  , arb_mat_is_diag
  -- * Special matrices
  , arb_mat_zero
  , arb_mat_one
  , arb_mat_ones
  , arb_mat_indeterminate
  , arb_mat_hilbert
  , arb_mat_pascal
  , arb_mat_stirling
  , arb_mat_dct
  -- * Transpose
  , arb_mat_transpose
  -- * Norms
  , arb_mat_bound_inf_norm
  , arb_mat_frobenius_norm
  , arb_mat_bound_frobenius_norm
  -- * Arithmetic
  , arb_mat_neg
  , arb_mat_add
  , arb_mat_sub
  , arb_mat_mul_classical
  , arb_mat_mul_threaded
  , arb_mat_mul_block
  , arb_mat_mul
  , arb_mat_mul_entrywise
  , arb_mat_sqr_classical
  , arb_mat_sqr
  , arb_mat_pow_ui
  , _arb_mat_addmul_rad_mag_fast
  , arb_mat_approx_mul
  -- * Scalar arithmetic
  , arb_mat_scalar_mul_2exp_si
  , arb_mat_scalar_addmul_si
  , arb_mat_scalar_addmul_fmpz
  , arb_mat_scalar_addmul_arb
  , arb_mat_scalar_mul_si
  , arb_mat_scalar_mul_fmpz
  , arb_mat_scalar_mul_arb
  , arb_mat_scalar_div_si
  , arb_mat_scalar_div_fmpz
  , arb_mat_scalar_div_arb
  -- * Gaussian elimination and solving
  , arb_mat_lu_classical
  , arb_mat_lu_recursive
  , arb_mat_lu
  , arb_mat_solve_tril_classical
  , arb_mat_solve_tril_recursive
  , arb_mat_solve_tril
  , arb_mat_solve_triu_classical
  , arb_mat_solve_triu_recursive
  , arb_mat_solve_triu
  , arb_mat_solve_lu_precomp
  , arb_mat_solve
  , arb_mat_solve_lu
  , arb_mat_solve_precond
  , arb_mat_solve_preapprox
  , arb_mat_inv
  , arb_mat_det_lu
  , arb_mat_det_precond
  , arb_mat_det
  , arb_mat_approx_solve_triu
  , arb_mat_approx_solve_tril
  , arb_mat_approx_lu
  , arb_mat_approx_solve_lu_precomp
  , arb_mat_approx_solve
  , arb_mat_approx_inv
  -- * Cholesky decomposition and solving
  , _arb_mat_cholesky_banachiewicz
  , arb_mat_cho
  , arb_mat_solve_cho_precomp
  , arb_mat_spd_solve
  , arb_mat_inv_cho_precomp
  , arb_mat_spd_inv
  , _arb_mat_ldl_inplace
  , _arb_mat_ldl_golub_and_van_loan
  , arb_mat_ldl
  , arb_mat_solve_ldl_precomp
  , arb_mat_inv_ldl_precomp
  -- * Characteristic polynomial and companion matrix
  , _arb_mat_charpoly
  , arb_mat_charpoly
  , _arb_mat_companion
  , arb_mat_companion
  -- * Special functions
  , arb_mat_exp_taylor_sum
  , arb_mat_exp
  , arb_mat_trace
  , _arb_mat_diag_prod
  , arb_mat_diag_prod
  -- * Sparsity structure
  --, arb_mat_entrywise_is_zero
  , arb_mat_entrywise_not_is_zero
  , arb_mat_count_is_zero
  , arb_mat_count_not_is_zero
  -- * Component and error operations
  , arb_mat_get_mid
  , arb_mat_add_error_mag
) where 

-- __arb_mat.h__ -- matrices over the real numbers -----------------------------

import System.IO.Unsafe

import Control.Monad

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, nullPtr, plusPtr )
import Foreign.Storable
import Foreign.Marshal ( free )

import Data.Number.Flint.Flint

import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Mat

import Data.Number.Flint.Fmpq.Mat

import Data.Number.Flint.Arb.Types

#include <flint/arb_mat.h>

-- Types -----------------------------------------------------------------------

data ArbMat = ArbMat {-# UNPACK #-} !(ForeignPtr CArbMat) 
data CArbMat = CArbMat (Ptr CArb) CLong CLong (Ptr (Ptr CArb)) 

instance Storable CArbMat where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size arb_mat_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment arb_mat_t}
  peek = error "CArbMat.peek: Not defined."
  poke = error "CArbMat.poke: Not defined."
 
newArbMat rows cols = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> arb_mat_init x rows cols
  addForeignPtrFinalizer p_arb_mat_clear x
  return $ ArbMat x

{-# INLINE withArbMat #-}
withArbMat (ArbMat x) f = do
  withForeignPtr x $ \px -> f px >>= return . (ArbMat x,)

{-# INLINE withNewArbMat #-}
withNewArbMat rows cols f = do
  x <- newArbMat rows cols
  withArbMat x f

-- Memory management -----------------------------------------------------------

-- | /arb_mat_init/ /mat/ /r/ /c/ 
-- 
-- Initializes the matrix, setting it to the zero matrix with /r/ rows and
-- /c/ columns.
foreign import ccall "arb_mat.h arb_mat_init"
  arb_mat_init :: Ptr CArbMat -> CLong -> CLong -> IO ()

-- | /arb_mat_clear/ /mat/ 
-- 
-- Clears the matrix, deallocating all entries.
foreign import ccall "arb_mat.h arb_mat_clear"
  arb_mat_clear :: Ptr CArbMat -> IO ()

foreign import ccall "arb_mat.h &arb_mat_clear"
  p_arb_mat_clear :: FunPtr (Ptr CArbMat -> IO ())

-- | /arb_mat_allocated_bytes/ /x/ 
-- 
-- Returns the total number of bytes heap-allocated internally by this
-- object. The count excludes the size of the structure itself. Add
-- @sizeof(arb_mat_struct)@ to get the size of the object as a whole.
foreign import ccall "arb_mat.h arb_mat_allocated_bytes"
  arb_mat_allocated_bytes :: Ptr CArbMat -> IO CLong

-- | /arb_mat_window_init/ /window/ /mat/ /r1/ /c1/ /r2/ /c2/ 
-- 
-- Initializes /window/ to a window matrix into the submatrix of /mat/
-- starting at the corner at row /r1/ and column /c1/ (inclusive) and
-- ending at row /r2/ and column /c2/ (exclusive).
foreign import ccall "arb_mat.h arb_mat_window_init"
  arb_mat_window_init :: Ptr CArbMat -> Ptr CArbMat -> CLong -> CLong -> CLong -> CLong -> IO ()

-- | /arb_mat_window_clear/ /window/ 
-- 
-- Frees the window matrix.
foreign import ccall "arb_mat.h arb_mat_window_clear"
  arb_mat_window_clear :: Ptr CArbMat -> IO ()

-- Conversions -----------------------------------------------------------------

foreign import ccall "arb_mat.h arb_mat_set"
  arb_mat_set :: Ptr CArbMat -> Ptr CArbMat -> IO ()

foreign import ccall "arb_mat.h arb_mat_set_fmpz_mat"
  arb_mat_set_fmpz_mat :: Ptr CArbMat -> Ptr CFmpzMat -> IO ()

foreign import ccall "arb_mat.h arb_mat_set_round_fmpz_mat"
  arb_mat_set_round_fmpz_mat :: Ptr CArbMat -> Ptr CFmpzMat -> CLong -> IO ()

-- | /arb_mat_set_fmpq_mat/ /dest/ /src/ /prec/ 
-- 
-- Sets /dest/ to /src/. The operands must have identical dimensions.
foreign import ccall "arb_mat.h arb_mat_set_fmpq_mat"
  arb_mat_set_fmpq_mat :: Ptr CArbMat -> Ptr CFmpqMat -> CLong -> IO ()

-- Random generation -----------------------------------------------------------

-- | /arb_mat_randtest/ /mat/ /state/ /prec/ /mag_bits/ 
-- 
-- Sets /mat/ to a random matrix with up to /prec/ bits of precision and
-- with exponents of width up to /mag_bits/.
foreign import ccall "arb_mat.h arb_mat_randtest"
  arb_mat_randtest :: Ptr CArbMat -> Ptr CFRandState -> CLong -> CLong -> IO ()

-- Input and output ------------------------------------------------------------

-- | /arb_mat_printd/ /mat/ /digits/ 
-- 
-- Prints each entry in the matrix with the specified number of decimal
-- digits.
foreign import ccall "arb_mat.h arb_mat_printd"
  arb_mat_printd :: Ptr CArbMat -> CLong -> IO ()

-- | /arb_mat_fprintd/ /file/ /mat/ /digits/ 
-- 
-- Prints each entry in the matrix with the specified number of decimal
-- digits to the stream /file/.
foreign import ccall "arb_mat.h arb_mat_fprintd"
  arb_mat_fprintd :: Ptr CFile -> Ptr CArbMat -> CLong -> IO ()

-- Comparisons -----------------------------------------------------------------

-- Predicate methods return 1 if the property certainly holds and 0
-- otherwise.
--
-- | /arb_mat_equal/ /mat1/ /mat2/ 
-- 
-- Returns whether the matrices have the same dimensions and identical
-- intervals as entries.
foreign import ccall "arb_mat.h arb_mat_equal"
  arb_mat_equal :: Ptr CArbMat -> Ptr CArbMat -> IO CInt

-- | /arb_mat_overlaps/ /mat1/ /mat2/ 
-- 
-- Returns whether the matrices have the same dimensions and each entry in
-- /mat1/ overlaps with the corresponding entry in /mat2/.
foreign import ccall "arb_mat.h arb_mat_overlaps"
  arb_mat_overlaps :: Ptr CArbMat -> Ptr CArbMat -> IO CInt

foreign import ccall "arb_mat.h arb_mat_contains"
  arb_mat_contains :: Ptr CArbMat -> Ptr CArbMat -> IO CInt

foreign import ccall "arb_mat.h arb_mat_contains_fmpz_mat"
  arb_mat_contains_fmpz_mat :: Ptr CArbMat -> Ptr CFmpzMat -> IO CInt

-- | /arb_mat_contains_fmpq_mat/ /mat1/ /mat2/ 
-- 
-- Returns whether the matrices have the same dimensions and each entry in
-- /mat2/ is contained in the corresponding entry in /mat1/.
foreign import ccall "arb_mat.h arb_mat_contains_fmpq_mat"
  arb_mat_contains_fmpq_mat :: Ptr CArbMat -> Ptr CFmpqMat -> IO CInt

-- | /arb_mat_eq/ /mat1/ /mat2/ 
-- 
-- Returns whether /mat1/ and /mat2/ certainly represent the same matrix.
foreign import ccall "arb_mat.h arb_mat_eq"
  arb_mat_eq :: Ptr CArbMat -> Ptr CArbMat -> IO CInt

-- | /arb_mat_ne/ /mat1/ /mat2/ 
-- 
-- Returns whether /mat1/ and /mat2/ certainly do not represent the same
-- matrix.
foreign import ccall "arb_mat.h arb_mat_ne"
  arb_mat_ne :: Ptr CArbMat -> Ptr CArbMat -> IO CInt

-- | /arb_mat_is_empty/ /mat/ 
-- 
-- Returns whether the number of rows or the number of columns in /mat/ is
-- zero.
foreign import ccall "arb_mat.h arb_mat_is_empty"
  arb_mat_is_empty :: Ptr CArbMat -> IO CInt

-- | /arb_mat_is_square/ /mat/ 
-- 
-- Returns whether the number of rows is equal to the number of columns in
-- /mat/.
foreign import ccall "arb_mat.h arb_mat_is_square"
  arb_mat_is_square :: Ptr CArbMat -> IO CInt

-- | /arb_mat_is_exact/ /mat/ 
-- 
-- Returns whether all entries in /mat/ have zero radius.
foreign import ccall "arb_mat.h arb_mat_is_exact"
  arb_mat_is_exact :: Ptr CArbMat -> IO CInt

-- | /arb_mat_is_zero/ /mat/ 
-- 
-- Returns whether all entries in /mat/ are exactly zero.
foreign import ccall "arb_mat.h arb_mat_is_zero"
  arb_mat_is_zero :: Ptr CArbMat -> IO CInt

-- | /arb_mat_is_finite/ /mat/ 
-- 
-- Returns whether all entries in /mat/ are finite.
foreign import ccall "arb_mat.h arb_mat_is_finite"
  arb_mat_is_finite :: Ptr CArbMat -> IO CInt

-- | /arb_mat_is_triu/ /mat/ 
-- 
-- Returns whether /mat/ is upper triangular; that is, all entries below
-- the main diagonal are exactly zero.
foreign import ccall "arb_mat.h arb_mat_is_triu"
  arb_mat_is_triu :: Ptr CArbMat -> IO CInt

-- | /arb_mat_is_tril/ /mat/ 
-- 
-- Returns whether /mat/ is lower triangular; that is, all entries above
-- the main diagonal are exactly zero.
foreign import ccall "arb_mat.h arb_mat_is_tril"
  arb_mat_is_tril :: Ptr CArbMat -> IO CInt

-- | /arb_mat_is_diag/ /mat/ 
-- 
-- Returns whether /mat/ is a diagonal matrix; that is, all entries off the
-- main diagonal are exactly zero.
foreign import ccall "arb_mat.h arb_mat_is_diag"
  arb_mat_is_diag :: Ptr CArbMat -> IO CInt

-- Special matrices ------------------------------------------------------------

-- | /arb_mat_zero/ /mat/ 
-- 
-- Sets all entries in mat to zero.
foreign import ccall "arb_mat.h arb_mat_zero"
  arb_mat_zero :: Ptr CArbMat -> IO ()

-- | /arb_mat_one/ /mat/ 
-- 
-- Sets the entries on the main diagonal to ones, and all other entries to
-- zero.
foreign import ccall "arb_mat.h arb_mat_one"
  arb_mat_one :: Ptr CArbMat -> IO ()

-- | /arb_mat_ones/ /mat/ 
-- 
-- Sets all entries in the matrix to ones.
foreign import ccall "arb_mat.h arb_mat_ones"
  arb_mat_ones :: Ptr CArbMat -> IO ()

-- | /arb_mat_indeterminate/ /mat/ 
-- 
-- Sets all entries in the matrix to indeterminate (NaN).
foreign import ccall "arb_mat.h arb_mat_indeterminate"
  arb_mat_indeterminate :: Ptr CArbMat -> IO ()

-- | /arb_mat_hilbert/ /mat/ /prec/ 
-- 
-- Sets /mat/ to the Hilbert matrix, which has entries
-- \(A_{j,k} = 1/(j+k+1)\).
foreign import ccall "arb_mat.h arb_mat_hilbert"
  arb_mat_hilbert :: Ptr CArbMat -> CLong -> IO ()

-- | /arb_mat_pascal/ /mat/ /triangular/ /prec/ 
-- 
-- Sets /mat/ to a Pascal matrix, whose entries are binomial coefficients.
-- If /triangular/ is 0, constructs a full symmetric matrix with the rows
-- of Pascal\'s triangle as successive antidiagonals. If /triangular/ is 1,
-- constructs the upper triangular matrix with the rows of Pascal\'s
-- triangle as columns, and if /triangular/ is -1, constructs the lower
-- triangular matrix with the rows of Pascal\'s triangle as rows.
-- 
-- The entries are computed using recurrence relations. When the dimensions
-- get large, some precision loss is possible; in that case, the user may
-- wish to create the matrix at slightly higher precision and then round it
-- to the final precision.
foreign import ccall "arb_mat.h arb_mat_pascal"
  arb_mat_pascal :: Ptr CArbMat -> CInt -> CLong -> IO ()

-- | /arb_mat_stirling/ /mat/ /kind/ /prec/ 
-- 
-- Sets /mat/ to a Stirling matrix, whose entries are Stirling numbers. If
-- /kind/ is 0, the entries are set to the unsigned Stirling numbers of the
-- first kind. If /kind/ is 1, the entries are set to the signed Stirling
-- numbers of the first kind. If /kind/ is 2, the entries are set to the
-- Stirling numbers of the second kind.
-- 
-- The entries are computed using recurrence relations. When the dimensions
-- get large, some precision loss is possible; in that case, the user may
-- wish to create the matrix at slightly higher precision and then round it
-- to the final precision.
foreign import ccall "arb_mat.h arb_mat_stirling"
  arb_mat_stirling :: Ptr CArbMat -> CInt -> CLong -> IO ()

-- | /arb_mat_dct/ /mat/ /type/ /prec/ 
-- 
-- Sets /mat/ to the DCT (discrete cosine transform) matrix of order /n/
-- where /n/ is the smallest dimension of /mat/ (if /mat/ is not square,
-- the matrix is extended periodically along the larger dimension). There
-- are many different conventions for defining DCT matrices; here, we use
-- the normalized \"DCT-II\" transform matrix
-- 
-- \[`\]
-- \[A_{j,k} = \sqrt{\frac{2}{n}} \cos\left(\frac{\pi j}{n} \left(k+\frac{1}{2}\right)\right)\]
-- 
-- which satisfies \(A^{-1} = A^T\). The /type/ parameter is currently
-- ignored and should be set to 0. In the future, it might be used to
-- select a different convention.
foreign import ccall "arb_mat.h arb_mat_dct"
  arb_mat_dct :: Ptr CArbMat -> CInt -> CLong -> IO ()

-- Transpose -------------------------------------------------------------------

-- | /arb_mat_transpose/ /dest/ /src/ 
-- 
-- Sets /dest/ to the exact transpose /src/. The operands must have
-- compatible dimensions. Aliasing is allowed.
foreign import ccall "arb_mat.h arb_mat_transpose"
  arb_mat_transpose :: Ptr CArbMat -> Ptr CArbMat -> IO ()

-- Norms -----------------------------------------------------------------------

-- | /arb_mat_bound_inf_norm/ /b/ /A/ 
-- 
-- Sets /b/ to an upper bound for the infinity norm (i.e. the largest
-- absolute value row sum) of /A/.
foreign import ccall "arb_mat.h arb_mat_bound_inf_norm"
  arb_mat_bound_inf_norm :: Ptr CMag -> Ptr CArbMat -> IO ()

-- | /arb_mat_frobenius_norm/ /res/ /A/ /prec/ 
-- 
-- Sets /res/ to the Frobenius norm (i.e. the square root of the sum of
-- squares of entries) of /A/.
foreign import ccall "arb_mat.h arb_mat_frobenius_norm"
  arb_mat_frobenius_norm :: Ptr CArb -> Ptr CArbMat -> CLong -> IO ()

-- | /arb_mat_bound_frobenius_norm/ /res/ /A/ 
-- 
-- Sets /res/ to an upper bound for the Frobenius norm of /A/.
foreign import ccall "arb_mat.h arb_mat_bound_frobenius_norm"
  arb_mat_bound_frobenius_norm :: Ptr CMag -> Ptr CArbMat -> IO ()

-- Arithmetic ------------------------------------------------------------------

-- | /arb_mat_neg/ /dest/ /src/ 
-- 
-- Sets /dest/ to the exact negation of /src/. The operands must have the
-- same dimensions.
foreign import ccall "arb_mat.h arb_mat_neg"
  arb_mat_neg :: Ptr CArbMat -> Ptr CArbMat -> IO ()

-- | /arb_mat_add/ /res/ /mat1/ /mat2/ /prec/ 
-- 
-- Sets res to the sum of /mat1/ and /mat2/. The operands must have the
-- same dimensions.
foreign import ccall "arb_mat.h arb_mat_add"
  arb_mat_add :: Ptr CArbMat -> Ptr CArbMat -> Ptr CArbMat -> CLong -> IO ()

-- | /arb_mat_sub/ /res/ /mat1/ /mat2/ /prec/ 
-- 
-- Sets /res/ to the difference of /mat1/ and /mat2/. The operands must
-- have the same dimensions.
foreign import ccall "arb_mat.h arb_mat_sub"
  arb_mat_sub :: Ptr CArbMat -> Ptr CArbMat -> Ptr CArbMat -> CLong -> IO ()

foreign import ccall "arb_mat.h arb_mat_mul_classical"
  arb_mat_mul_classical :: Ptr CArbMat -> Ptr CArbMat -> Ptr CArbMat -> CLong -> IO ()

foreign import ccall "arb_mat.h arb_mat_mul_threaded"
  arb_mat_mul_threaded :: Ptr CArbMat -> Ptr CArbMat -> Ptr CArbMat -> CLong -> IO ()

foreign import ccall "arb_mat.h arb_mat_mul_block"
  arb_mat_mul_block :: Ptr CArbMat -> Ptr CArbMat -> Ptr CArbMat -> CLong -> IO ()

-- | /arb_mat_mul/ /res/ /mat1/ /mat2/ /prec/ 
-- 
-- Sets /res/ to the matrix product of /mat1/ and /mat2/. The operands must
-- have compatible dimensions for matrix multiplication.
-- 
-- The /classical/ version performs matrix multiplication in the trivial
-- way.
-- 
-- The /block/ version decomposes the input matrices into one or several
-- blocks of uniformly scaled matrices and multiplies large blocks via
-- /fmpz_mat_mul/. It also invokes @_arb_mat_addmul_rad_mag_fast@ for the
-- radius matrix multiplications.
-- 
-- The /threaded/ version performs classical multiplication but splits the
-- computation over the number of threads returned by
-- /flint_get_num_threads()/.
-- 
-- The default version chooses an algorithm automatically.
foreign import ccall "arb_mat.h arb_mat_mul"
  arb_mat_mul :: Ptr CArbMat -> Ptr CArbMat -> Ptr CArbMat -> CLong -> IO ()

-- | /arb_mat_mul_entrywise/ /C/ /A/ /B/ /prec/ 
-- 
-- Sets /C/ to the entrywise product of /A/ and /B/. The operands must have
-- the same dimensions.
foreign import ccall "arb_mat.h arb_mat_mul_entrywise"
  arb_mat_mul_entrywise :: Ptr CArbMat -> Ptr CArbMat -> Ptr CArbMat -> CLong -> IO ()

foreign import ccall "arb_mat.h arb_mat_sqr_classical"
  arb_mat_sqr_classical :: Ptr CArbMat -> Ptr CArbMat -> CLong -> IO ()

-- | /arb_mat_sqr/ /res/ /mat/ /prec/ 
-- 
-- Sets /res/ to the matrix square of /mat/. The operands must both be
-- square with the same dimensions.
foreign import ccall "arb_mat.h arb_mat_sqr"
  arb_mat_sqr :: Ptr CArbMat -> Ptr CArbMat -> CLong -> IO ()

-- | /arb_mat_pow_ui/ /res/ /mat/ /exp/ /prec/ 
-- 
-- Sets /res/ to /mat/ raised to the power /exp/. Requires that /mat/ is a
-- square matrix.
foreign import ccall "arb_mat.h arb_mat_pow_ui"
  arb_mat_pow_ui :: Ptr CArbMat -> Ptr CArbMat -> CULong -> CLong -> IO ()

-- | /_arb_mat_addmul_rad_mag_fast/ /C/ /A/ /B/ /ar/ /ac/ /bc/ 
-- 
-- Helper function for matrix multiplication. Adds to the radii of /C/ the
-- matrix product of the matrices represented by /A/ and /B/, where /A/ is
-- a linear array of coefficients in row-major order and /B/ is a linear
-- array of coefficients in column-major order. This function assumes that
-- all exponents are small and is unsafe for general use.
foreign import ccall "arb_mat.h _arb_mat_addmul_rad_mag_fast"
  _arb_mat_addmul_rad_mag_fast :: Ptr CArbMat -> Ptr CMag -> Ptr CMag -> CLong -> CLong -> CLong -> IO ()

-- | /arb_mat_approx_mul/ /res/ /mat1/ /mat2/ /prec/ 
-- 
-- Approximate matrix multiplication. The input radii are ignored and the
-- output matrix is set to an approximate floating-point result. The radii
-- in the output matrix will /not/ necessarily be zeroed.
foreign import ccall "arb_mat.h arb_mat_approx_mul"
  arb_mat_approx_mul :: Ptr CArbMat -> Ptr CArbMat -> Ptr CArbMat -> CLong -> IO ()

-- Scalar arithmetic -----------------------------------------------------------

-- | /arb_mat_scalar_mul_2exp_si/ /B/ /A/ /c/ 
-- 
-- Sets /B/ to /A/ multiplied by \(2^c\).
foreign import ccall "arb_mat.h arb_mat_scalar_mul_2exp_si"
  arb_mat_scalar_mul_2exp_si :: Ptr CArbMat -> Ptr CArbMat -> CLong -> IO ()

foreign import ccall "arb_mat.h arb_mat_scalar_addmul_si"
  arb_mat_scalar_addmul_si :: Ptr CArbMat -> Ptr CArbMat -> CLong -> CLong -> IO ()

foreign import ccall "arb_mat.h arb_mat_scalar_addmul_fmpz"
  arb_mat_scalar_addmul_fmpz :: Ptr CArbMat -> Ptr CArbMat -> Ptr CFmpz -> CLong -> IO ()

-- | /arb_mat_scalar_addmul_arb/ /B/ /A/ /c/ /prec/ 
-- 
-- Sets /B/ to \(B + A \times c\).
foreign import ccall "arb_mat.h arb_mat_scalar_addmul_arb"
  arb_mat_scalar_addmul_arb :: Ptr CArbMat -> Ptr CArbMat -> Ptr CArb -> CLong -> IO ()

foreign import ccall "arb_mat.h arb_mat_scalar_mul_si"
  arb_mat_scalar_mul_si :: Ptr CArbMat -> Ptr CArbMat -> CLong -> CLong -> IO ()

foreign import ccall "arb_mat.h arb_mat_scalar_mul_fmpz"
  arb_mat_scalar_mul_fmpz :: Ptr CArbMat -> Ptr CArbMat -> Ptr CFmpz -> CLong -> IO ()

-- | /arb_mat_scalar_mul_arb/ /B/ /A/ /c/ /prec/ 
-- 
-- Sets /B/ to \(A \times c\).
foreign import ccall "arb_mat.h arb_mat_scalar_mul_arb"
  arb_mat_scalar_mul_arb :: Ptr CArbMat -> Ptr CArbMat -> Ptr CArb -> CLong -> IO ()

foreign import ccall "arb_mat.h arb_mat_scalar_div_si"
  arb_mat_scalar_div_si :: Ptr CArbMat -> Ptr CArbMat -> CLong -> CLong -> IO ()

foreign import ccall "arb_mat.h arb_mat_scalar_div_fmpz"
  arb_mat_scalar_div_fmpz :: Ptr CArbMat -> Ptr CArbMat -> Ptr CFmpz -> CLong -> IO ()

-- | /arb_mat_scalar_div_arb/ /B/ /A/ /c/ /prec/ 
-- 
-- Sets /B/ to \(A / c\).
foreign import ccall "arb_mat.h arb_mat_scalar_div_arb"
  arb_mat_scalar_div_arb :: Ptr CArbMat -> Ptr CArbMat -> Ptr CArb -> CLong -> IO ()

-- Gaussian elimination and solving --------------------------------------------

foreign import ccall "arb_mat.h arb_mat_lu_classical"
  arb_mat_lu_classical :: Ptr CLong -> Ptr CArbMat -> Ptr CArbMat -> CLong -> IO CInt

foreign import ccall "arb_mat.h arb_mat_lu_recursive"
  arb_mat_lu_recursive :: Ptr CLong -> Ptr CArbMat -> Ptr CArbMat -> CLong -> IO CInt

-- | /arb_mat_lu/ /perm/ /LU/ /A/ /prec/ 
-- 
-- Given an \(n \times n\) matrix \(A\), computes an LU decomposition
-- \(PLU = A\) using Gaussian elimination with partial pivoting. The input
-- and output matrices can be the same, performing the decomposition
-- in-place.
-- 
-- Entry \(i\) in the permutation vector perm is set to the row index in
-- the input matrix corresponding to row \(i\) in the output matrix.
-- 
-- The algorithm succeeds and returns nonzero if it can find \(n\)
-- invertible (i.e. not containing zero) pivot entries. This guarantees
-- that the matrix is invertible.
-- 
-- The algorithm fails and returns zero, leaving the entries in \(P\) and
-- \(LU\) undefined, if it cannot find \(n\) invertible pivot elements. In
-- this case, either the matrix is singular, the input matrix was computed
-- to insufficient precision, or the LU decomposition was attempted at
-- insufficient precision.
-- 
-- The /classical/ version uses Gaussian elimination directly while the
-- /recursive/ version performs the computation in a block recursive way to
-- benefit from fast matrix multiplication. The default version chooses an
-- algorithm automatically.
foreign import ccall "arb_mat.h arb_mat_lu"
  arb_mat_lu :: Ptr CLong -> Ptr CArbMat -> Ptr CArbMat -> CLong -> IO CInt

foreign import ccall "arb_mat.h arb_mat_solve_tril_classical"
  arb_mat_solve_tril_classical :: Ptr CArbMat -> Ptr CArbMat -> Ptr CArbMat -> CInt -> CLong -> IO ()

foreign import ccall "arb_mat.h arb_mat_solve_tril_recursive"
  arb_mat_solve_tril_recursive :: Ptr CArbMat -> Ptr CArbMat -> Ptr CArbMat -> CInt -> CLong -> IO ()

foreign import ccall "arb_mat.h arb_mat_solve_tril"
  arb_mat_solve_tril :: Ptr CArbMat -> Ptr CArbMat -> Ptr CArbMat -> CInt -> CLong -> IO ()

foreign import ccall "arb_mat.h arb_mat_solve_triu_classical"
  arb_mat_solve_triu_classical :: Ptr CArbMat -> Ptr CArbMat -> Ptr CArbMat -> CInt -> CLong -> IO ()

foreign import ccall "arb_mat.h arb_mat_solve_triu_recursive"
  arb_mat_solve_triu_recursive :: Ptr CArbMat -> Ptr CArbMat -> Ptr CArbMat -> CInt -> CLong -> IO ()

-- | /arb_mat_solve_triu/ /X/ /U/ /B/ /unit/ /prec/ 
-- 
-- Solves the lower triangular system \(LX = B\) or the upper triangular
-- system \(UX = B\), respectively. If /unit/ is set, the main diagonal of
-- /L/ or /U/ is taken to consist of all ones, and in that case the actual
-- entries on the diagonal are not read at all and can contain other data.
-- 
-- The /classical/ versions perform the computations iteratively while the
-- /recursive/ versions perform the computations in a block recursive way
-- to benefit from fast matrix multiplication. The default versions choose
-- an algorithm automatically.
foreign import ccall "arb_mat.h arb_mat_solve_triu"
  arb_mat_solve_triu :: Ptr CArbMat -> Ptr CArbMat -> Ptr CArbMat -> CInt -> CLong -> IO ()

-- | /arb_mat_solve_lu_precomp/ /X/ /perm/ /LU/ /B/ /prec/ 
-- 
-- Solves \(AX = B\) given the precomputed nonsingular LU decomposition
-- \(A = PLU\). The matrices \(X\) and \(B\) are allowed to be aliased with
-- each other, but \(X\) is not allowed to be aliased with \(LU\).
foreign import ccall "arb_mat.h arb_mat_solve_lu_precomp"
  arb_mat_solve_lu_precomp :: Ptr CArbMat -> Ptr CLong -> Ptr CArbMat -> Ptr CArbMat -> CLong -> IO ()

foreign import ccall "arb_mat.h arb_mat_solve"
  arb_mat_solve :: Ptr CArbMat -> Ptr CArbMat -> Ptr CArbMat -> CLong -> IO CInt

foreign import ccall "arb_mat.h arb_mat_solve_lu"
  arb_mat_solve_lu :: Ptr CArbMat -> Ptr CArbMat -> Ptr CArbMat -> CLong -> IO CInt

-- | /arb_mat_solve_precond/ /X/ /A/ /B/ /prec/ 
-- 
-- Solves \(AX = B\) where \(A\) is a nonsingular \(n \times n\) matrix and
-- \(X\) and \(B\) are \(n \times m\) matrices.
-- 
-- If \(m > 0\) and \(A\) cannot be inverted numerically (indicating either
-- that \(A\) is singular or that the precision is insufficient), the
-- values in the output matrix are left undefined and zero is returned. A
-- nonzero return value guarantees that \(A\) is invertible and that the
-- exact solution matrix is contained in the output.
-- 
-- Three algorithms are provided:
-- 
-- -   The /lu/ version performs LU decomposition directly in ball
--     arithmetic. This is fast, but the bounds typically blow up
--     exponentially with /n/, even if the system is well-conditioned. This
--     algorithm is usually the best choice at very high precision.
-- -   The /precond/ version computes an approximate inverse to
--     precondition the system < [HS1967]>. This is usually several times
--     slower than direct LU decomposition, but the bounds do not blow up
--     with /n/ if the system is well-conditioned. This algorithm is
--     usually the best choice for large systems at low to moderate
--     precision.
-- -   The default version selects between /lu/ and /precomp/
--     automatically.
-- 
-- The automatic choice should be reasonable most of the time, but users
-- may benefit from trying either /lu/ or /precond/ in specific
-- applications. For example, the /lu/ solver often performs better for
-- ill-conditioned systems where use of very high precision is unavoidable.
foreign import ccall "arb_mat.h arb_mat_solve_precond"
  arb_mat_solve_precond :: Ptr CArbMat -> Ptr CArbMat -> Ptr CArbMat -> CLong -> IO CInt

-- | /arb_mat_solve_preapprox/ /X/ /A/ /B/ /R/ /T/ /prec/ 
-- 
-- Solves \(AX = B\) where \(A\) is a nonsingular \(n \times n\) matrix and
-- \(X\) and \(B\) are \(n \times m\) matrices, given an approximation
-- \(R\) of the matrix inverse of \(A\), and given the approximation \(T\)
-- of the solution \(X\).
-- 
-- If \(m > 0\) and \(A\) cannot be inverted numerically (indicating either
-- that \(A\) is singular or that the precision is insufficient, or that
-- \(R\) is not a close enough approximation of the inverse of \(A\)), the
-- values in the output matrix are left undefined and zero is returned. A
-- nonzero return value guarantees that \(A\) is invertible and that the
-- exact solution matrix is contained in the output.
foreign import ccall "arb_mat.h arb_mat_solve_preapprox"
  arb_mat_solve_preapprox :: Ptr CArbMat -> Ptr CArbMat -> Ptr CArbMat -> Ptr CArbMat -> Ptr CArbMat -> CLong -> IO CInt

-- | /arb_mat_inv/ /X/ /A/ /prec/ 
-- 
-- Sets \(X = A^{-1}\) where \(A\) is a square matrix, computed by solving
-- the system \(AX = I\).
-- 
-- If \(A\) cannot be inverted numerically (indicating either that \(A\) is
-- singular or that the precision is insufficient), the values in the
-- output matrix are left undefined and zero is returned. A nonzero return
-- value guarantees that the matrix is invertible and that the exact
-- inverse is contained in the output.
foreign import ccall "arb_mat.h arb_mat_inv"
  arb_mat_inv :: Ptr CArbMat -> Ptr CArbMat -> CLong -> IO CInt

foreign import ccall "arb_mat.h arb_mat_det_lu"
  arb_mat_det_lu :: Ptr CArb -> Ptr CArbMat -> CLong -> IO ()

foreign import ccall "arb_mat.h arb_mat_det_precond"
  arb_mat_det_precond :: Ptr CArb -> Ptr CArbMat -> CLong -> IO ()

-- | /arb_mat_det/ /det/ /A/ /prec/ 
-- 
-- Sets /det/ to the determinant of the matrix /A/.
-- 
-- The /lu/ version uses Gaussian elimination with partial pivoting. If at
-- some point an invertible pivot element cannot be found, the elimination
-- is stopped and the magnitude of the determinant of the remaining
-- submatrix is bounded using Hadamard\'s inequality.
-- 
-- The /precond/ version computes an approximate LU factorization of /A/
-- and multiplies by the inverse /L/ and /U/ martices as preconditioners to
-- obtain a matrix close to the identity matrix < [Rum2010]>. An enclosure
-- for this determinant is computed using Gershgorin circles. This is about
-- four times slower than direct Gaussian elimination, but much more
-- numerically stable.
-- 
-- The default version automatically selects between the /lu/ and /precond/
-- versions and additionally handles small or triangular matrices by direct
-- formulas.
foreign import ccall "arb_mat.h arb_mat_det"
  arb_mat_det :: Ptr CArb -> Ptr CArbMat -> CLong -> IO ()

foreign import ccall "arb_mat.h arb_mat_approx_solve_triu"
  arb_mat_approx_solve_triu :: Ptr CArbMat -> Ptr CArbMat -> Ptr CArbMat -> CInt -> CLong -> IO ()

foreign import ccall "arb_mat.h arb_mat_approx_solve_tril"
  arb_mat_approx_solve_tril :: Ptr CArbMat -> Ptr CArbMat -> Ptr CArbMat -> CInt -> CLong -> IO ()

foreign import ccall "arb_mat.h arb_mat_approx_lu"
  arb_mat_approx_lu :: Ptr CLong -> Ptr CArbMat -> Ptr CArbMat -> CLong -> IO CInt

foreign import ccall "arb_mat.h arb_mat_approx_solve_lu_precomp"
  arb_mat_approx_solve_lu_precomp :: Ptr CArbMat -> Ptr CLong -> Ptr CArbMat -> Ptr CArbMat -> CLong -> IO ()

foreign import ccall "arb_mat.h arb_mat_approx_solve"
  arb_mat_approx_solve :: Ptr CArbMat -> Ptr CArbMat -> Ptr CArbMat -> CLong -> IO CInt

-- | /arb_mat_approx_inv/ /X/ /A/ /prec/ 
-- 
-- These methods perform approximate solving /without any error control/.
-- The radii in the input matrices are ignored, the computations are done
-- numerically with floating-point arithmetic (using ordinary Gaussian
-- elimination and triangular solving, accelerated through the use of block
-- recursive strategies for large matrices), and the output matrices are
-- set to the approximate floating-point results with zeroed error bounds.
-- 
-- Approximate solutions are useful for computing preconditioning matrices
-- for certified solutions. Some users may also find these methods useful
-- for doing ordinary numerical linear algebra in applications where error
-- bounds are not needed.
foreign import ccall "arb_mat.h arb_mat_approx_inv"
  arb_mat_approx_inv :: Ptr CArbMat -> Ptr CArbMat -> CLong -> IO CInt

-- Cholesky decomposition and solving ------------------------------------------

foreign import ccall "arb_mat.h _arb_mat_cholesky_banachiewicz"
  _arb_mat_cholesky_banachiewicz :: Ptr CArbMat -> CLong -> IO CInt

-- | /arb_mat_cho/ /L/ /A/ /prec/ 
-- 
-- Computes the Cholesky decomposition of /A/, returning nonzero iff the
-- symmetric matrix defined by the lower triangular part of /A/ is
-- certainly positive definite.
-- 
-- If a nonzero value is returned, then /L/ is set to the lower triangular
-- matrix such that \(A = L * L^T\).
-- 
-- If zero is returned, then either the matrix is not symmetric positive
-- definite, the input matrix was computed to insufficient precision, or
-- the decomposition was attempted at insufficient precision.
-- 
-- The underscore method computes /L/ from /A/ in-place, leaving the strict
-- upper triangular region undefined.
foreign import ccall "arb_mat.h arb_mat_cho"
  arb_mat_cho :: Ptr CArbMat -> Ptr CArbMat -> CLong -> IO CInt

-- | /arb_mat_solve_cho_precomp/ /X/ /L/ /B/ /prec/ 
-- 
-- Solves \(AX = B\) given the precomputed Cholesky decomposition
-- \(A = L L^T\). The matrices /X/ and /B/ are allowed to be aliased with
-- each other, but /X/ is not allowed to be aliased with /L/.
foreign import ccall "arb_mat.h arb_mat_solve_cho_precomp"
  arb_mat_solve_cho_precomp :: Ptr CArbMat -> Ptr CArbMat -> Ptr CArbMat -> CLong -> IO ()

-- | /arb_mat_spd_solve/ /X/ /A/ /B/ /prec/ 
-- 
-- Solves \(AX = B\) where /A/ is a symmetric positive definite matrix and
-- /X/ and /B/ are \(n \times m\) matrices, using Cholesky decomposition.
-- 
-- If \(m > 0\) and /A/ cannot be factored using Cholesky decomposition
-- (indicating either that /A/ is not symmetric positive definite or that
-- the precision is insufficient), the values in the output matrix are left
-- undefined and zero is returned. A nonzero return value guarantees that
-- the symmetric matrix defined through the lower triangular part of /A/ is
-- invertible and that the exact solution matrix is contained in the
-- output.
foreign import ccall "arb_mat.h arb_mat_spd_solve"
  arb_mat_spd_solve :: Ptr CArbMat -> Ptr CArbMat -> Ptr CArbMat -> CLong -> IO CInt

-- | /arb_mat_inv_cho_precomp/ /X/ /L/ /prec/ 
-- 
-- Sets \(X = A^{-1}\) where \(A\) is a symmetric positive definite matrix
-- whose Cholesky decomposition /L/ has been computed with @arb_mat_cho@.
-- The inverse is calculated using the method of < [Kri2013]> which is more
-- efficient than solving \(AX = I\) with @arb_mat_solve_cho_precomp@.
foreign import ccall "arb_mat.h arb_mat_inv_cho_precomp"
  arb_mat_inv_cho_precomp :: Ptr CArbMat -> Ptr CArbMat -> CLong -> IO ()

-- | /arb_mat_spd_inv/ /X/ /A/ /prec/ 
-- 
-- Sets \(X = A^{-1}\) where /A/ is a symmetric positive definite matrix.
-- It is calculated using the method of < [Kri2013]> which computes fewer
-- intermediate results than solving \(AX = I\) with @arb_mat_spd_solve@.
-- 
-- If /A/ cannot be factored using Cholesky decomposition (indicating
-- either that /A/ is not symmetric positive definite or that the precision
-- is insufficient), the values in the output matrix are left undefined and
-- zero is returned. A nonzero return value guarantees that the symmetric
-- matrix defined through the lower triangular part of /A/ is invertible
-- and that the exact inverse is contained in the output.
foreign import ccall "arb_mat.h arb_mat_spd_inv"
  arb_mat_spd_inv :: Ptr CArbMat -> Ptr CArbMat -> CLong -> IO CInt

foreign import ccall "arb_mat.h _arb_mat_ldl_inplace"
  _arb_mat_ldl_inplace :: Ptr CArbMat -> CLong -> IO CInt

foreign import ccall "arb_mat.h _arb_mat_ldl_golub_and_van_loan"
  _arb_mat_ldl_golub_and_van_loan :: Ptr CArbMat -> CLong -> IO CInt

-- | /arb_mat_ldl/ /res/ /A/ /prec/ 
-- 
-- Computes the \(LDL^T\) decomposition of /A/, returning nonzero iff the
-- symmetric matrix defined by the lower triangular part of /A/ is
-- certainly positive definite.
-- 
-- If a nonzero value is returned, then /res/ is set to a lower triangular
-- matrix that encodes the \(L * D * L^T\) decomposition of /A/. In
-- particular, \(L\) is a lower triangular matrix with ones on its diagonal
-- and whose strictly lower triangular region is the same as that of /res/.
-- \(D\) is a diagonal matrix with the same diagonal as that of /res/.
-- 
-- If zero is returned, then either the matrix is not symmetric positive
-- definite, the input matrix was computed to insufficient precision, or
-- the decomposition was attempted at insufficient precision.
-- 
-- The underscore methods compute /res/ from /A/ in-place, leaving the
-- strict upper triangular region undefined. The default method uses
-- algorithm 4.1.2 from < [GVL1996]>.
foreign import ccall "arb_mat.h arb_mat_ldl"
  arb_mat_ldl :: Ptr CArbMat -> Ptr CArbMat -> CLong -> IO CInt

-- | /arb_mat_solve_ldl_precomp/ /X/ /L/ /B/ /prec/ 
-- 
-- Solves \(AX = B\) given the precomputed \(A = LDL^T\) decomposition
-- encoded by /L/. The matrices /X/ and /B/ are allowed to be aliased with
-- each other, but /X/ is not allowed to be aliased with /L/.
foreign import ccall "arb_mat.h arb_mat_solve_ldl_precomp"
  arb_mat_solve_ldl_precomp :: Ptr CArbMat -> Ptr CArbMat -> Ptr CArbMat -> CLong -> IO ()

-- | /arb_mat_inv_ldl_precomp/ /X/ /L/ /prec/ 
-- 
-- Sets \(X = A^{-1}\) where \(A\) is a symmetric positive definite matrix
-- whose \(LDL^T\) decomposition encoded by /L/ has been computed with
-- @arb_mat_ldl@. The inverse is calculated using the method of
-- < [Kri2013]> which is more efficient than solving \(AX = I\) with
-- @arb_mat_solve_ldl_precomp@.
foreign import ccall "arb_mat.h arb_mat_inv_ldl_precomp"
  arb_mat_inv_ldl_precomp :: Ptr CArbMat -> Ptr CArbMat -> CLong -> IO ()

-- Characteristic polynomial and companion matrix ------------------------------

foreign import ccall "arb_mat.h _arb_mat_charpoly"
  _arb_mat_charpoly :: Ptr CArb -> Ptr CArbMat -> CLong -> IO ()

-- | /arb_mat_charpoly/ /poly/ /mat/ /prec/ 
-- 
-- Sets /poly/ to the characteristic polynomial of /mat/ which must be a
-- square matrix. If the matrix has /n/ rows, the underscore method
-- requires space for \(n + 1\) output coefficients. Employs a
-- division-free algorithm using \(O(n^4)\) operations.
foreign import ccall "arb_mat.h arb_mat_charpoly"
  arb_mat_charpoly :: Ptr CArbPoly -> Ptr CArbMat -> CLong -> IO ()

foreign import ccall "arb_mat.h _arb_mat_companion"
  _arb_mat_companion :: Ptr CArbMat -> Ptr CArb -> CLong -> IO ()

-- | /arb_mat_companion/ /mat/ /poly/ /prec/ 
-- 
-- Sets the /n/ by /n/ matrix /mat/ to the companion matrix of the
-- polynomial /poly/ which must have degree /n/. The underscore method
-- reads \(n + 1\) input coefficients.
foreign import ccall "arb_mat.h arb_mat_companion"
  arb_mat_companion :: Ptr CArbMat -> Ptr CArbPoly -> CLong -> IO ()

-- Special functions -----------------------------------------------------------

-- | /arb_mat_exp_taylor_sum/ /S/ /A/ /N/ /prec/ 
-- 
-- Sets /S/ to the truncated exponential Taylor series
-- \(S = \sum_{k=0}^{N-1} A^k / k!\). Uses rectangular splitting to compute
-- the sum using \(O(\sqrt{N})\) matrix multiplications. The recurrence
-- relation for factorials is used to get scalars that are small integers
-- instead of full factorials. As in < [Joh2014b]>, all divisions are
-- postponed to the end by computing partial factorials of length
-- \(O(\sqrt{N})\). The scalars could be reduced by doing more divisions,
-- but this appears to be slower in most cases.
foreign import ccall "arb_mat.h arb_mat_exp_taylor_sum"
  arb_mat_exp_taylor_sum :: Ptr CArbMat -> Ptr CArbMat -> CLong -> CLong -> IO ()

-- | /arb_mat_exp/ /B/ /A/ /prec/ 
-- 
-- Sets /B/ to the exponential of the matrix /A/, defined by the Taylor
-- series
-- 
-- \[`\]
-- \[\exp(A) = \sum_{k=0}^{\infty} \frac{A^k}{k!}.\]
-- 
-- The function is evaluated as \(\exp(A/2^r)^{2^r}\), where \(r\) is
-- chosen to give rapid convergence.
-- 
-- The elementwise error when truncating the Taylor series after /N/ terms
-- is bounded by the error in the infinity norm, for which we have
-- 
-- \[`
-- \left\|\exp(2^{-r}A) - \sum_{k=0}^{N-1}
-- \frac{\left(2^{-r} A\right)^k}{k!} \right\|_{\infty} =
-- \left\|\sum_{k=N}^{\infty} \frac{\left(2^{-r} A\right)^k}{k!}\right\|_{\infty} \le
-- \sum_{k=N}^{\infty} \frac{(2^{-r} \|A\|_{\infty})^k}{k!}.\]
-- 
-- We bound the sum on the right using @mag_exp_tail@. Truncation error is
-- not added to entries whose values are determined by the sparsity
-- structure of \(A\).
foreign import ccall "arb_mat.h arb_mat_exp"
  arb_mat_exp :: Ptr CArbMat -> Ptr CArbMat -> CLong -> IO ()

-- | /arb_mat_trace/ /trace/ /mat/ /prec/ 
-- 
-- Sets /trace/ to the trace of the matrix, i.e. the sum of entries on the
-- main diagonal of /mat/. The matrix is required to be square.
foreign import ccall "arb_mat.h arb_mat_trace"
  arb_mat_trace :: Ptr CArb -> Ptr CArbMat -> CLong -> IO ()

foreign import ccall "arb_mat.h _arb_mat_diag_prod"
  _arb_mat_diag_prod :: Ptr CArb -> Ptr CArbMat -> CLong -> CLong -> CLong -> IO ()

-- | /arb_mat_diag_prod/ /res/ /mat/ /prec/ 
-- 
-- Sets /res/ to the product of the entries on the main diagonal of /mat/.
-- The underscore method computes the product of the entries between index
-- /a/ inclusive and /b/ exclusive (the indices must be in range).
foreign import ccall "arb_mat.h arb_mat_diag_prod"
  arb_mat_diag_prod :: Ptr CArb -> Ptr CArbMat -> CLong -> IO ()

-- Sparsity structure ----------------------------------------------------------

-- -- | /arb_mat_entrywise_is_zero/ /dest/ /src/ 
-- -- 
-- -- Sets each entry of /dest/ to indicate whether the corresponding entry of
-- -- /src/ is certainly zero. If the entry of /src/ at row \(i\) and column
-- -- \(j\) is zero according to @arb_is_zero@ then the entry of /dest/ at
-- -- that row and column is set to one, otherwise that entry of /dest/ is set
-- -- to zero.
-- foreign import ccall "arb_mat.h arb_mat_entrywise_is_zero"
--   arb_mat_entrywise_is_zero :: Ptr CFmpzMat -> Ptr CArbMat -> IO ()

-- | /arb_mat_entrywise_not_is_zero/ /dest/ /src/ 
-- 
-- Sets each entry of /dest/ to indicate whether the corresponding entry of
-- /src/ is not certainly zero. This the complement of
-- @arb_mat_entrywise_is_zero@.
foreign import ccall "arb_mat.h arb_mat_entrywise_not_is_zero"
  arb_mat_entrywise_not_is_zero :: Ptr CFmpzMat -> Ptr CArbMat -> IO ()

-- | /arb_mat_count_is_zero/ /mat/ 
-- 
-- Returns the number of entries of /mat/ that are certainly zero according
-- to @arb_is_zero@.
foreign import ccall "arb_mat.h arb_mat_count_is_zero"
  arb_mat_count_is_zero :: Ptr CArbMat -> IO CLong

-- | /arb_mat_count_not_is_zero/ /mat/ 
-- 
-- Returns the number of entries of /mat/ that are not certainly zero.
foreign import ccall "arb_mat.h arb_mat_count_not_is_zero"
  arb_mat_count_not_is_zero :: Ptr CArbMat -> IO CLong

-- Component and error operations ----------------------------------------------

-- | /arb_mat_get_mid/ /B/ /A/ 
-- 
-- Sets the entries of /B/ to the exact midpoints of the entries of /A/.
foreign import ccall "arb_mat.h arb_mat_get_mid"
  arb_mat_get_mid :: Ptr CArbMat -> Ptr CArbMat -> IO ()

-- | /arb_mat_add_error_mag/ /mat/ /err/ 
-- 
-- Adds /err/ in-place to the radii of the entries of /mat/.
foreign import ccall "arb_mat.h arb_mat_add_error_mag"
  arb_mat_add_error_mag :: Ptr CArbMat -> Ptr CMag -> IO ()

-- Eigenvalues and eigenvectors ------------------------------------------------

-- To compute eigenvalues and eigenvectors, one can convert to an
-- @acb_mat_t@ and use the functions in
-- @acb_mat.h: Eigenvalues and eigenvectors\<acb-mat-eigenvalues>@. In the
-- future dedicated methods for real matrices will be added here.
--
