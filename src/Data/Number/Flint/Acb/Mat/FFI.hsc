{-# language
    CApiFFI
  , FlexibleInstances
  , ForeignFunctionInterface
  , TupleSections
  #-}

module Data.Number.Flint.Acb.Mat.FFI (
  -- * Matrices over the complex numbers
    AcbMat (..)
  , CAcbMat (..)
  , newAcbMat
  , newAcbMatFromFmpzMat
  , newAcbMatFromFmpzMatRound
  , newAcbMatFromFmpqMat
  , newAcbMatFromArbMat
  , newAcbMatFromArbMatRound
  , withAcbMat
  , withNewAcbMat
  -- * Memory management
  , acb_mat_init
  , acb_mat_clear
  , acb_mat_allocated_bytes
  , acb_mat_window_init
  --, acb_mat_window_clear
  -- * Conversions
  , acb_mat_set
  , acb_mat_set_fmpz_mat
  , acb_mat_set_round_fmpz_mat
  , acb_mat_set_fmpq_mat
  , acb_mat_set_arb_mat
  , acb_mat_set_round_arb_mat
  -- * Random generation
  , acb_mat_randtest
  , acb_mat_randtest_eig
  -- * Input and output
  , acb_mat_get_strd
  , acb_mat_printd
  , acb_mat_fprintd
  -- * Comparisons
  , acb_mat_equal
  , acb_mat_overlaps
  , acb_mat_contains
  , acb_mat_contains_fmpz_mat
  , acb_mat_contains_fmpq_mat
  , acb_mat_eq
  , acb_mat_ne
  , acb_mat_is_real
  , acb_mat_is_empty
  , acb_mat_is_square
  , acb_mat_is_exact
  , acb_mat_is_zero
  , acb_mat_is_finite
  , acb_mat_is_triu
  , acb_mat_is_tril
  , acb_mat_is_diag
  -- * Special matrices
  , acb_mat_zero
  , acb_mat_one
  , acb_mat_ones
  , acb_mat_indeterminate
  , acb_mat_dft
  -- * Transpose
  , acb_mat_transpose
  , acb_mat_conjugate_transpose
  , acb_mat_conjugate
  -- * Norms
  , acb_mat_bound_inf_norm
  , acb_mat_frobenius_norm
  , acb_mat_bound_frobenius_norm
  -- * Arithmetic
  , acb_mat_neg
  , acb_mat_add
  , acb_mat_sub
  , acb_mat_mul_classical
  , acb_mat_mul_threaded
  , acb_mat_mul_reorder
  , acb_mat_mul
  , acb_mat_mul_entrywise
  , acb_mat_sqr_classical
  , acb_mat_sqr
  , acb_mat_pow_ui
  , acb_mat_approx_mul
  -- * Scalar arithmetic
  , acb_mat_scalar_mul_2exp_si
  , acb_mat_scalar_addmul_si
  , acb_mat_scalar_addmul_fmpz
  , acb_mat_scalar_addmul_arb
  , acb_mat_scalar_addmul_acb
  , acb_mat_scalar_mul_si
  , acb_mat_scalar_mul_fmpz
  , acb_mat_scalar_mul_arb
  , acb_mat_scalar_mul_acb
  , acb_mat_scalar_div_si
  , acb_mat_scalar_div_fmpz
  , acb_mat_scalar_div_arb
  , acb_mat_scalar_div_acb
  -- * Gaussian elimination and solving
  , acb_mat_lu_classical
  , acb_mat_lu_recursive
  , acb_mat_lu
  , acb_mat_solve_tril_classical
  , acb_mat_solve_tril_recursive
  , acb_mat_solve_tril
  , acb_mat_solve_triu_classical
  , acb_mat_solve_triu_recursive
  , acb_mat_solve_triu
  , acb_mat_solve_lu_precomp
  , acb_mat_solve
  , acb_mat_solve_lu
  , acb_mat_solve_precond
  , acb_mat_inv
  , acb_mat_det_lu
  , acb_mat_det_precond
  , acb_mat_det
  , acb_mat_approx_solve_triu
  , acb_mat_approx_solve_tril
  , acb_mat_approx_lu
  , acb_mat_approx_solve_lu_precomp
  , acb_mat_approx_solve
  , acb_mat_approx_inv
  -- * Characteristic polynomial and companion matrix
  , _acb_mat_charpoly
  , acb_mat_charpoly
  , _acb_mat_companion
  , acb_mat_companion
  -- * Special functions
  , acb_mat_exp_taylor_sum
  , acb_mat_exp
  , acb_mat_trace
  , _acb_mat_diag_prod
  , acb_mat_diag_prod
  -- * Component and error operations
  , acb_mat_get_mid
  , acb_mat_add_error_mag
  -- * Eigenvalues and eigenvectors
  , acb_mat_approx_eig_qr
  , acb_mat_eig_global_enclosure
  , acb_mat_eig_enclosure_rump
  , acb_mat_eig_simple_rump
  , acb_mat_eig_simple_vdhoeven_mourrain
  , acb_mat_eig_simple
  , acb_mat_eig_multiple_rump
  , acb_mat_eig_multiple
) where

-- Matrices over the complex numbers -------------------------------------------

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
import Data.Number.Flint.Arb.Mat

import Data.Number.Flint.Acb.Types
import Data.Number.Flint.Acb.Poly

#include <flint/acb_mat.h>

-- Types -----------------------------------------------------------------------

data AcbMat = AcbMat {-# UNPACK #-} !(ForeignPtr CAcbMat) 
data CAcbMat = CAcbMat (Ptr CAcb) CLong CLong (Ptr (Ptr CAcb)) 

instance Storable CAcbMat where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size acb_mat_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment acb_mat_t}
  peek = error "CAcbMat.peek: Not defined."
  poke = error "CAcbMat.poke: Not defined."
 
newAcbMat rows cols = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> acb_mat_init x rows cols
  addForeignPtrFinalizer p_acb_mat_clear x
  return $ AcbMat x

newAcbMatFromFmpzMat a = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> do
    withFmpzMat a $ \a -> do
      CFmpzMat _ rows cols _ <- peek a
      acb_mat_init x rows cols
      acb_mat_set_fmpz_mat x a
  addForeignPtrFinalizer p_acb_mat_clear x
  return $ AcbMat x

newAcbMatFromFmpzMatRound a prec = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> do
    withFmpzMat a $ \a -> do
      CFmpzMat _ rows cols _ <- peek a
      acb_mat_init x rows cols
      acb_mat_set_round_fmpz_mat x a prec
  addForeignPtrFinalizer p_acb_mat_clear x
 
newAcbMatFromFmpqMat a prec = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> do
    withFmpqMat a $ \a -> do
      CFmpqMat _ rows cols _ <- peek a
      acb_mat_init x rows cols
      acb_mat_set_fmpq_mat x a prec
  addForeignPtrFinalizer p_acb_mat_clear x
  return $ AcbMat x

newAcbMatFromArbMat a = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> do
    withArbMat a $ \a -> do
      CArbMat _ rows cols _ <- peek a
      acb_mat_init x rows cols
      acb_mat_set_arb_mat x a
  addForeignPtrFinalizer p_acb_mat_clear x
  return $ AcbMat x

newAcbMatFromArbMatRound a prec = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> do
    withArbMat a $ \a -> do
      CArbMat _ rows cols _ <- peek a
      acb_mat_init x rows cols
      acb_mat_set_round_arb_mat x a prec
  addForeignPtrFinalizer p_acb_mat_clear x

{-# INLINE withAcbMat #-}
withAcbMat (AcbMat x) f = do
  withForeignPtr x $ \px -> f px >>= return . (AcbMat x,)

{-# INLINE withNewAcbMat #-}
withNewAcbMat rows cols f = do
  x <- newAcbMat rows cols
  withAcbMat x f

-- Memory management -----------------------------------------------------------

-- | /acb_mat_init/ /mat/ /r/ /c/ 
-- 
-- Initializes the matrix, setting it to the zero matrix with /r/ rows and
-- /c/ columns.
foreign import ccall "acb_mat.h acb_mat_init"
  acb_mat_init :: Ptr CAcbMat -> CLong -> CLong -> IO ()

-- | /acb_mat_clear/ /mat/ 
-- 
-- Clears the matrix, deallocating all entries.
foreign import ccall "acb_mat.h acb_mat_clear"
  acb_mat_clear :: Ptr CAcbMat -> IO ()

foreign import ccall "acb_mat.h &acb_mat_clear"
  p_acb_mat_clear :: FunPtr (Ptr CAcbMat -> IO ())

-- | /acb_mat_allocated_bytes/ /x/ 
-- 
-- Returns the total number of bytes heap-allocated internally by this
-- object. The count excludes the size of the structure itself. Add
-- @sizeof(acb_mat_struct)@ to get the size of the object as a whole.
foreign import ccall "acb_mat.h acb_mat_allocated_bytes"
  acb_mat_allocated_bytes :: Ptr CAcbMat -> IO CLong

-- | /acb_mat_window_init/ /window/ /mat/ /r1/ /c1/ /r2/ /c2/ 
-- 
-- Initializes /window/ to a window matrix into the submatrix of /mat/
-- starting at the corner at row /r1/ and column /c1/ (inclusive) and
-- ending at row /r2/ and column /c2/ (exclusive).
foreign import ccall "acb_mat.h acb_mat_window_init"
  acb_mat_window_init :: Ptr CAcbMat -> Ptr CAcbMat -> CLong -> CLong -> CLong -> CLong -> IO ()

-- -- | /acb_mat_window_clear/ /window/ 
-- -- 
-- -- Frees the window matrix.
-- foreign import ccall "acb_mat.h acb_mat_window_clear"
--   acb_mat_window_clear :: Ptr CAcbMat -> IO ()

-- Conversions -----------------------------------------------------------------

foreign import ccall "acb_mat.h acb_mat_set"
  acb_mat_set :: Ptr CAcbMat -> Ptr CAcbMat -> IO ()

foreign import ccall "acb_mat.h acb_mat_set_fmpz_mat"
  acb_mat_set_fmpz_mat :: Ptr CAcbMat -> Ptr CFmpzMat -> IO ()

foreign import ccall "acb_mat.h acb_mat_set_round_fmpz_mat"
  acb_mat_set_round_fmpz_mat :: Ptr CAcbMat -> Ptr CFmpzMat -> CLong -> IO ()

foreign import ccall "acb_mat.h acb_mat_set_fmpq_mat"
  acb_mat_set_fmpq_mat :: Ptr CAcbMat -> Ptr CFmpqMat -> CLong -> IO ()

foreign import ccall "acb_mat.h acb_mat_set_arb_mat"
  acb_mat_set_arb_mat :: Ptr CAcbMat -> Ptr CArbMat -> IO ()

-- | /acb_mat_set_round_arb_mat/ /dest/ /src/ /prec/ 
-- 
-- Sets /dest/ to /src/. The operands must have identical dimensions.
foreign import ccall "acb_mat.h acb_mat_set_round_arb_mat"
  acb_mat_set_round_arb_mat :: Ptr CAcbMat -> Ptr CArbMat -> CLong -> IO ()

-- Random generation -----------------------------------------------------------

-- | /acb_mat_randtest/ /mat/ /state/ /prec/ /mag_bits/ 
-- 
-- Sets /mat/ to a random matrix with up to /prec/ bits of precision and
-- with exponents of width up to /mag_bits/.
foreign import ccall "acb_mat.h acb_mat_randtest"
  acb_mat_randtest :: Ptr CAcbMat -> Ptr CFRandState -> CLong -> CLong -> IO ()

-- | /acb_mat_randtest_eig/ /mat/ /state/ /E/ /prec/ 
-- 
-- Sets /mat/ to a random matrix with the prescribed eigenvalues supplied
-- as the vector /E/. The output matrix is required to be square. We
-- generate a random unitary matrix via a matrix exponential, and then
-- evaluate an inverse Schur decomposition.
foreign import ccall "acb_mat.h acb_mat_randtest_eig"
  acb_mat_randtest_eig :: Ptr CAcbMat -> Ptr CFRandState -> Ptr CAcb -> CLong -> IO ()

-- Input and output ------------------------------------------------------------

foreign import ccall "acb_mat acb_mat_get_strd"
  acb_mat_get_strd :: Ptr CAcbMat -> CLong -> IO CString
  
-- | /acb_mat_printd/ /mat/ /digits/ 
-- 
-- Prints each entry in the matrix with the specified number of decimal
-- digits.
acb_mat_printd :: Ptr CAcbMat -> CLong -> IO ()
acb_mat_printd mat digits = do
  cs <- acb_mat_get_strd mat digits
  s <- peekCString cs
  free cs
  putStr s
  
-- | /acb_mat_fprintd/ /file/ /mat/ /digits/ 
-- 
-- Prints each entry in the matrix with the specified number of decimal
-- digits to the stream /file/.
foreign import ccall "acb_mat.h acb_mat_fprintd"
  acb_mat_fprintd :: Ptr CFile -> Ptr CAcbMat -> CLong -> IO ()

-- Comparisons -----------------------------------------------------------------

-- Predicate methods return 1 if the property certainly holds and 0
-- otherwise.
--
-- | /acb_mat_equal/ /mat1/ /mat2/ 
-- 
-- Returns whether the matrices have the same dimensions and identical
-- intervals as entries.
foreign import ccall "acb_mat.h acb_mat_equal"
  acb_mat_equal :: Ptr CAcbMat -> Ptr CAcbMat -> IO CInt

-- | /acb_mat_overlaps/ /mat1/ /mat2/ 
-- 
-- Returns whether the matrices have the same dimensions and each entry in
-- /mat1/ overlaps with the corresponding entry in /mat2/.
foreign import ccall "acb_mat.h acb_mat_overlaps"
  acb_mat_overlaps :: Ptr CAcbMat -> Ptr CAcbMat -> IO CInt

foreign import ccall "acb_mat.h acb_mat_contains"
  acb_mat_contains :: Ptr CAcbMat -> Ptr CAcbMat -> IO CInt

foreign import ccall "acb_mat.h acb_mat_contains_fmpz_mat"
  acb_mat_contains_fmpz_mat :: Ptr CAcbMat -> Ptr CFmpzMat -> IO CInt

-- | /acb_mat_contains_fmpq_mat/ /mat1/ /mat2/ 
-- 
-- Returns whether the matrices have the same dimensions and each entry in
-- /mat2/ is contained in the corresponding entry in /mat1/.
foreign import ccall "acb_mat.h acb_mat_contains_fmpq_mat"
  acb_mat_contains_fmpq_mat :: Ptr CAcbMat -> Ptr CFmpqMat -> IO CInt

-- | /acb_mat_eq/ /mat1/ /mat2/ 
-- 
-- Returns whether /mat1/ and /mat2/ certainly represent the same matrix.
foreign import ccall "acb_mat.h acb_mat_eq"
  acb_mat_eq :: Ptr CAcbMat -> Ptr CAcbMat -> IO CInt

-- | /acb_mat_ne/ /mat1/ /mat2/ 
-- 
-- Returns whether /mat1/ and /mat2/ certainly do not represent the same
-- matrix.
foreign import ccall "acb_mat.h acb_mat_ne"
  acb_mat_ne :: Ptr CAcbMat -> Ptr CAcbMat -> IO CInt

-- | /acb_mat_is_real/ /mat/ 
-- 
-- Returns whether all entries in /mat/ have zero imaginary part.
foreign import ccall "acb_mat.h acb_mat_is_real"
  acb_mat_is_real :: Ptr CAcbMat -> IO CInt

-- | /acb_mat_is_empty/ /mat/ 
-- 
-- Returns whether the number of rows or the number of columns in /mat/ is
-- zero.
foreign import ccall "acb_mat.h acb_mat_is_empty"
  acb_mat_is_empty :: Ptr CAcbMat -> IO CInt

-- | /acb_mat_is_square/ /mat/ 
-- 
-- Returns whether the number of rows is equal to the number of columns in
-- /mat/.
foreign import ccall "acb_mat.h acb_mat_is_square"
  acb_mat_is_square :: Ptr CAcbMat -> IO CInt

-- | /acb_mat_is_exact/ /mat/ 
-- 
-- Returns whether all entries in /mat/ have zero radius.
foreign import ccall "acb_mat.h acb_mat_is_exact"
  acb_mat_is_exact :: Ptr CAcbMat -> IO CInt

-- | /acb_mat_is_zero/ /mat/ 
-- 
-- Returns whether all entries in /mat/ are exactly zero.
foreign import ccall "acb_mat.h acb_mat_is_zero"
  acb_mat_is_zero :: Ptr CAcbMat -> IO CInt

-- | /acb_mat_is_finite/ /mat/ 
-- 
-- Returns whether all entries in /mat/ are finite.
foreign import ccall "acb_mat.h acb_mat_is_finite"
  acb_mat_is_finite :: Ptr CAcbMat -> IO CInt

-- | /acb_mat_is_triu/ /mat/ 
-- 
-- Returns whether /mat/ is upper triangular; that is, all entries below
-- the main diagonal are exactly zero.
foreign import ccall "acb_mat.h acb_mat_is_triu"
  acb_mat_is_triu :: Ptr CAcbMat -> IO CInt

-- | /acb_mat_is_tril/ /mat/ 
-- 
-- Returns whether /mat/ is lower triangular; that is, all entries above
-- the main diagonal are exactly zero.
foreign import ccall "acb_mat.h acb_mat_is_tril"
  acb_mat_is_tril :: Ptr CAcbMat -> IO CInt

-- | /acb_mat_is_diag/ /mat/ 
-- 
-- Returns whether /mat/ is a diagonal matrix; that is, all entries off the
-- main diagonal are exactly zero.
foreign import ccall "acb_mat.h acb_mat_is_diag"
  acb_mat_is_diag :: Ptr CAcbMat -> IO CInt

-- Special matrices ------------------------------------------------------------

-- | /acb_mat_zero/ /mat/ 
-- 
-- Sets all entries in mat to zero.
foreign import ccall "acb_mat.h acb_mat_zero"
  acb_mat_zero :: Ptr CAcbMat -> IO ()

-- | /acb_mat_one/ /mat/ 
-- 
-- Sets the entries on the main diagonal to ones, and all other entries to
-- zero.
foreign import ccall "acb_mat.h acb_mat_one"
  acb_mat_one :: Ptr CAcbMat -> IO ()

-- | /acb_mat_ones/ /mat/ 
-- 
-- Sets all entries in the matrix to ones.
foreign import ccall "acb_mat.h acb_mat_ones"
  acb_mat_ones :: Ptr CAcbMat -> IO ()

-- | /acb_mat_indeterminate/ /mat/ 
-- 
-- Sets all entries in the matrix to indeterminate (NaN).
foreign import ccall "acb_mat.h acb_mat_indeterminate"
  acb_mat_indeterminate :: Ptr CAcbMat -> IO ()

-- | /acb_mat_dft/ /mat/ /type/ /prec/ 
-- 
-- Sets /mat/ to the DFT (discrete Fourier transform) matrix of order /n/
-- where /n/ is the smallest dimension of /mat/ (if /mat/ is not square,
-- the matrix is extended periodically along the larger dimension). Here,
-- we use the normalized DFT matrix
-- 
-- \[`\]
-- \[A_{j,k} = \frac{\omega^{jk}}{\sqrt{n}}, \quad \omega = e^{-2\pi i/n}.\]
-- 
-- The /type/ parameter is currently ignored and should be set to 0. In the
-- future, it might be used to select a different convention.
foreign import ccall "acb_mat.h acb_mat_dft"
  acb_mat_dft :: Ptr CAcbMat -> CInt -> CLong -> IO ()

-- Transpose -------------------------------------------------------------------

-- | /acb_mat_transpose/ /dest/ /src/ 
-- 
-- Sets /dest/ to the exact transpose /src/. The operands must have
-- compatible dimensions. Aliasing is allowed.
foreign import ccall "acb_mat.h acb_mat_transpose"
  acb_mat_transpose :: Ptr CAcbMat -> Ptr CAcbMat -> IO ()

-- | /acb_mat_conjugate_transpose/ /dest/ /src/ 
-- 
-- Sets /dest/ to the conjugate transpose of /src/. The operands must have
-- compatible dimensions. Aliasing is allowed.
foreign import ccall "acb_mat.h acb_mat_conjugate_transpose"
  acb_mat_conjugate_transpose :: Ptr CAcbMat -> Ptr CAcbMat -> IO ()

-- | /acb_mat_conjugate/ /dest/ /src/ 
-- 
-- Sets /dest/ to the elementwise complex conjugate of /src/.
foreign import ccall "acb_mat.h acb_mat_conjugate"
  acb_mat_conjugate :: Ptr CAcbMat -> Ptr CAcbMat -> IO ()

-- Norms -----------------------------------------------------------------------

-- | /acb_mat_bound_inf_norm/ /b/ /A/ 
-- 
-- Sets /b/ to an upper bound for the infinity norm (i.e. the largest
-- absolute value row sum) of /A/.
foreign import ccall "acb_mat.h acb_mat_bound_inf_norm"
  acb_mat_bound_inf_norm :: Ptr CMag -> Ptr CAcbMat -> IO ()

-- | /acb_mat_frobenius_norm/ /res/ /A/ /prec/ 
-- 
-- Sets /res/ to the Frobenius norm (i.e. the square root of the sum of
-- squares of entries) of /A/.
foreign import ccall "acb_mat.h acb_mat_frobenius_norm"
  acb_mat_frobenius_norm :: Ptr CAcb -> Ptr CAcbMat -> CLong -> IO ()

-- | /acb_mat_bound_frobenius_norm/ /res/ /A/ 
-- 
-- Sets /res/ to an upper bound for the Frobenius norm of /A/.
foreign import ccall "acb_mat.h acb_mat_bound_frobenius_norm"
  acb_mat_bound_frobenius_norm :: Ptr CMag -> Ptr CAcbMat -> IO ()

-- Arithmetic ------------------------------------------------------------------

-- | /acb_mat_neg/ /dest/ /src/ 
-- 
-- Sets /dest/ to the exact negation of /src/. The operands must have the
-- same dimensions.
foreign import ccall "acb_mat.h acb_mat_neg"
  acb_mat_neg :: Ptr CAcbMat -> Ptr CAcbMat -> IO ()

-- | /acb_mat_add/ /res/ /mat1/ /mat2/ /prec/ 
-- 
-- Sets res to the sum of /mat1/ and /mat2/. The operands must have the
-- same dimensions.
foreign import ccall "acb_mat.h acb_mat_add"
  acb_mat_add :: Ptr CAcbMat -> Ptr CAcbMat -> Ptr CAcbMat -> CLong -> IO ()

-- | /acb_mat_sub/ /res/ /mat1/ /mat2/ /prec/ 
-- 
-- Sets /res/ to the difference of /mat1/ and /mat2/. The operands must
-- have the same dimensions.
foreign import ccall "acb_mat.h acb_mat_sub"
  acb_mat_sub :: Ptr CAcbMat -> Ptr CAcbMat -> Ptr CAcbMat -> CLong -> IO ()

foreign import ccall "acb_mat.h acb_mat_mul_classical"
  acb_mat_mul_classical :: Ptr CAcbMat -> Ptr CAcbMat -> Ptr CAcbMat -> CLong -> IO ()

foreign import ccall "acb_mat.h acb_mat_mul_threaded"
  acb_mat_mul_threaded :: Ptr CAcbMat -> Ptr CAcbMat -> Ptr CAcbMat -> CLong -> IO ()

foreign import ccall "acb_mat.h acb_mat_mul_reorder"
  acb_mat_mul_reorder :: Ptr CAcbMat -> Ptr CAcbMat -> Ptr CAcbMat -> CLong -> IO ()

-- | /acb_mat_mul/ /res/ /mat1/ /mat2/ /prec/ 
-- 
-- Sets /res/ to the matrix product of /mat1/ and /mat2/. The operands must
-- have compatible dimensions for matrix multiplication.
-- 
-- The /classical/ version performs matrix multiplication in the trivial
-- way.
-- 
-- The /threaded/ version performs classical multiplication but splits the
-- computation over the number of threads returned by
-- /flint_get_num_threads()/.
-- 
-- The /reorder/ version reorders the data and performs one to four real
-- matrix multiplications via @arb_mat_mul@.
-- 
-- The default version chooses an algorithm automatically.
foreign import ccall "acb_mat.h acb_mat_mul"
  acb_mat_mul :: Ptr CAcbMat -> Ptr CAcbMat -> Ptr CAcbMat -> CLong -> IO ()

-- | /acb_mat_mul_entrywise/ /res/ /mat1/ /mat2/ /prec/ 
-- 
-- Sets /res/ to the entrywise product of /mat1/ and /mat2/. The operands
-- must have the same dimensions.
foreign import ccall "acb_mat.h acb_mat_mul_entrywise"
  acb_mat_mul_entrywise :: Ptr CAcbMat -> Ptr CAcbMat -> Ptr CAcbMat -> CLong -> IO ()

foreign import ccall "acb_mat.h acb_mat_sqr_classical"
  acb_mat_sqr_classical :: Ptr CAcbMat -> Ptr CAcbMat -> CLong -> IO ()

-- | /acb_mat_sqr/ /res/ /mat/ /prec/ 
-- 
-- Sets /res/ to the matrix square of /mat/. The operands must both be
-- square with the same dimensions.
foreign import ccall "acb_mat.h acb_mat_sqr"
  acb_mat_sqr :: Ptr CAcbMat -> Ptr CAcbMat -> CLong -> IO ()

-- | /acb_mat_pow_ui/ /res/ /mat/ /exp/ /prec/ 
-- 
-- Sets /res/ to /mat/ raised to the power /exp/. Requires that /mat/ is a
-- square matrix.
foreign import ccall "acb_mat.h acb_mat_pow_ui"
  acb_mat_pow_ui :: Ptr CAcbMat -> Ptr CAcbMat -> CULong -> CLong -> IO ()

-- | /acb_mat_approx_mul/ /res/ /mat1/ /mat2/ /prec/ 
-- 
-- Approximate matrix multiplication. The input radii are ignored and the
-- output matrix is set to an approximate floating-point result. For
-- performance reasons, the radii in the output matrix will /not/
-- necessarily be written (zeroed), but will remain zero if they are
-- already zeroed in /res/ before calling this function.
foreign import ccall "acb_mat.h acb_mat_approx_mul"
  acb_mat_approx_mul :: Ptr CAcbMat -> Ptr CAcbMat -> Ptr CAcbMat -> CLong -> IO ()

-- Scalar arithmetic -----------------------------------------------------------

-- | /acb_mat_scalar_mul_2exp_si/ /B/ /A/ /c/ 
-- 
-- Sets /B/ to /A/ multiplied by \(2^c\).
foreign import ccall "acb_mat.h acb_mat_scalar_mul_2exp_si"
  acb_mat_scalar_mul_2exp_si :: Ptr CAcbMat -> Ptr CAcbMat -> CLong -> IO ()

foreign import ccall "acb_mat.h acb_mat_scalar_addmul_si"
  acb_mat_scalar_addmul_si :: Ptr CAcbMat -> Ptr CAcbMat -> CLong -> CLong -> IO ()

foreign import ccall "acb_mat.h acb_mat_scalar_addmul_fmpz"
  acb_mat_scalar_addmul_fmpz :: Ptr CAcbMat -> Ptr CAcbMat -> Ptr CFmpz -> CLong -> IO ()

foreign import ccall "acb_mat.h acb_mat_scalar_addmul_arb"
  acb_mat_scalar_addmul_arb :: Ptr CAcbMat -> Ptr CAcbMat -> Ptr CArb -> CLong -> IO ()

-- | /acb_mat_scalar_addmul_acb/ /B/ /A/ /c/ /prec/ 
-- 
-- Sets /B/ to \(B + A \times c\).
foreign import ccall "acb_mat.h acb_mat_scalar_addmul_acb"
  acb_mat_scalar_addmul_acb :: Ptr CAcbMat -> Ptr CAcbMat -> Ptr CAcb -> CLong -> IO ()

foreign import ccall "acb_mat.h acb_mat_scalar_mul_si"
  acb_mat_scalar_mul_si :: Ptr CAcbMat -> Ptr CAcbMat -> CLong -> CLong -> IO ()

foreign import ccall "acb_mat.h acb_mat_scalar_mul_fmpz"
  acb_mat_scalar_mul_fmpz :: Ptr CAcbMat -> Ptr CAcbMat -> Ptr CFmpz -> CLong -> IO ()

foreign import ccall "acb_mat.h acb_mat_scalar_mul_arb"
  acb_mat_scalar_mul_arb :: Ptr CAcbMat -> Ptr CAcbMat -> Ptr CArb -> CLong -> IO ()

-- | /acb_mat_scalar_mul_acb/ /B/ /A/ /c/ /prec/ 
-- 
-- Sets /B/ to \(A \times c\).
foreign import ccall "acb_mat.h acb_mat_scalar_mul_acb"
  acb_mat_scalar_mul_acb :: Ptr CAcbMat -> Ptr CAcbMat -> Ptr CAcb -> CLong -> IO ()

foreign import ccall "acb_mat.h acb_mat_scalar_div_si"
  acb_mat_scalar_div_si :: Ptr CAcbMat -> Ptr CAcbMat -> CLong -> CLong -> IO ()

foreign import ccall "acb_mat.h acb_mat_scalar_div_fmpz"
  acb_mat_scalar_div_fmpz :: Ptr CAcbMat -> Ptr CAcbMat -> Ptr CFmpz -> CLong -> IO ()

foreign import ccall "acb_mat.h acb_mat_scalar_div_arb"
  acb_mat_scalar_div_arb :: Ptr CAcbMat -> Ptr CAcbMat -> Ptr CArb -> CLong -> IO ()

-- | /acb_mat_scalar_div_acb/ /B/ /A/ /c/ /prec/ 
-- 
-- Sets /B/ to \(A / c\).
foreign import ccall "acb_mat.h acb_mat_scalar_div_acb"
  acb_mat_scalar_div_acb :: Ptr CAcbMat -> Ptr CAcbMat -> Ptr CAcb -> CLong -> IO ()

-- Gaussian elimination and solving --------------------------------------------

foreign import ccall "acb_mat.h acb_mat_lu_classical"
  acb_mat_lu_classical :: Ptr CLong -> Ptr CAcbMat -> Ptr CAcbMat -> CLong -> IO CInt

foreign import ccall "acb_mat.h acb_mat_lu_recursive"
  acb_mat_lu_recursive :: Ptr CLong -> Ptr CAcbMat -> Ptr CAcbMat -> CLong -> IO CInt

-- | /acb_mat_lu/ /perm/ /LU/ /A/ /prec/ 
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
foreign import ccall "acb_mat.h acb_mat_lu"
  acb_mat_lu :: Ptr CLong -> Ptr CAcbMat -> Ptr CAcbMat -> CLong -> IO CInt

foreign import ccall "acb_mat.h acb_mat_solve_tril_classical"
  acb_mat_solve_tril_classical :: Ptr CAcbMat -> Ptr CAcbMat -> Ptr CAcbMat -> CInt -> CLong -> IO ()

foreign import ccall "acb_mat.h acb_mat_solve_tril_recursive"
  acb_mat_solve_tril_recursive :: Ptr CAcbMat -> Ptr CAcbMat -> Ptr CAcbMat -> CInt -> CLong -> IO ()

foreign import ccall "acb_mat.h acb_mat_solve_tril"
  acb_mat_solve_tril :: Ptr CAcbMat -> Ptr CAcbMat -> Ptr CAcbMat -> CInt -> CLong -> IO ()

foreign import ccall "acb_mat.h acb_mat_solve_triu_classical"
  acb_mat_solve_triu_classical :: Ptr CAcbMat -> Ptr CAcbMat -> Ptr CAcbMat -> CInt -> CLong -> IO ()

foreign import ccall "acb_mat.h acb_mat_solve_triu_recursive"
  acb_mat_solve_triu_recursive :: Ptr CAcbMat -> Ptr CAcbMat -> Ptr CAcbMat -> CInt -> CLong -> IO ()

-- | /acb_mat_solve_triu/ /X/ /U/ /B/ /unit/ /prec/ 
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
foreign import ccall "acb_mat.h acb_mat_solve_triu"
  acb_mat_solve_triu :: Ptr CAcbMat -> Ptr CAcbMat -> Ptr CAcbMat -> CInt -> CLong -> IO ()

-- | /acb_mat_solve_lu_precomp/ /X/ /perm/ /LU/ /B/ /prec/ 
-- 
-- Solves \(AX = B\) given the precomputed nonsingular LU decomposition
-- \(A = PLU\). The matrices \(X\) and \(B\) are allowed to be aliased with
-- each other, but \(X\) is not allowed to be aliased with \(LU\).
foreign import ccall "acb_mat.h acb_mat_solve_lu_precomp"
  acb_mat_solve_lu_precomp :: Ptr CAcbMat -> Ptr CLong -> Ptr CAcbMat -> Ptr CAcbMat -> CLong -> IO ()

foreign import ccall "acb_mat.h acb_mat_solve"
  acb_mat_solve :: Ptr CAcbMat -> Ptr CAcbMat -> Ptr CAcbMat -> CLong -> IO CInt

foreign import ccall "acb_mat.h acb_mat_solve_lu"
  acb_mat_solve_lu :: Ptr CAcbMat -> Ptr CAcbMat -> Ptr CAcbMat -> CLong -> IO CInt

-- | /acb_mat_solve_precond/ /X/ /A/ /B/ /prec/ 
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
--     precondition the system. This is usually several times slower than
--     direct LU decomposition, but the bounds do not blow up with /n/ if
--     the system is well-conditioned. This algorithm is usually the best
--     choice for large systems at low to moderate precision.
-- -   The default version selects between /lu/ and /precomp/
--     automatically.
-- 
-- The automatic choice should be reasonable most of the time, but users
-- may benefit from trying either /lu/ or /precond/ in specific
-- applications. For example, the /lu/ solver often performs better for
-- ill-conditioned systems where use of very high precision is unavoidable.
foreign import ccall "acb_mat.h acb_mat_solve_precond"
  acb_mat_solve_precond :: Ptr CAcbMat -> Ptr CAcbMat -> Ptr CAcbMat -> CLong -> IO CInt

-- | /acb_mat_inv/ /X/ /A/ /prec/ 
-- 
-- Sets \(X = A^{-1}\) where \(A\) is a square matrix, computed by solving
-- the system \(AX = I\).
-- 
-- If \(A\) cannot be inverted numerically (indicating either that \(A\) is
-- singular or that the precision is insufficient), the values in the
-- output matrix are left undefined and zero is returned. A nonzero return
-- value guarantees that the matrix is invertible and that the exact
-- inverse is contained in the output.
foreign import ccall "acb_mat.h acb_mat_inv"
  acb_mat_inv :: Ptr CAcbMat -> Ptr CAcbMat -> CLong -> IO CInt

foreign import ccall "acb_mat.h acb_mat_det_lu"
  acb_mat_det_lu :: Ptr CAcb -> Ptr CAcbMat -> CLong -> IO ()

foreign import ccall "acb_mat.h acb_mat_det_precond"
  acb_mat_det_precond :: Ptr CAcb -> Ptr CAcbMat -> CLong -> IO ()

-- | /acb_mat_det/ /det/ /A/ /prec/ 
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
foreign import ccall "acb_mat.h acb_mat_det"
  acb_mat_det :: Ptr CAcb -> Ptr CAcbMat -> CLong -> IO ()

foreign import ccall "acb_mat.h acb_mat_approx_solve_triu"
  acb_mat_approx_solve_triu :: Ptr CAcbMat -> Ptr CAcbMat -> Ptr CAcbMat -> CInt -> CLong -> IO ()

foreign import ccall "acb_mat.h acb_mat_approx_solve_tril"
  acb_mat_approx_solve_tril :: Ptr CAcbMat -> Ptr CAcbMat -> Ptr CAcbMat -> CInt -> CLong -> IO ()

foreign import ccall "acb_mat.h acb_mat_approx_lu"
  acb_mat_approx_lu :: Ptr CLong -> Ptr CAcbMat -> Ptr CAcbMat -> CLong -> IO CInt

foreign import ccall "acb_mat.h acb_mat_approx_solve_lu_precomp"
  acb_mat_approx_solve_lu_precomp :: Ptr CAcbMat -> Ptr CLong -> Ptr CAcbMat -> Ptr CAcbMat -> CLong -> IO ()

foreign import ccall "acb_mat.h acb_mat_approx_solve"
  acb_mat_approx_solve :: Ptr CAcbMat -> Ptr CAcbMat -> Ptr CAcbMat -> CLong -> IO CInt

-- | /acb_mat_approx_inv/ /X/ /A/ /prec/ 
-- 
-- These methods perform approximate solving /without any error control/.
-- The radii in the input matrices are ignored, the computations are done
-- numerically with floating-point arithmetic (using ordinary Gaussian
-- elimination and triangular solving, accelerated through the use of block
-- recursive strategies for large matrices), and the output matrices are
-- set to the approximate floating-point results with zeroed error bounds.
foreign import ccall "acb_mat.h acb_mat_approx_inv"
  acb_mat_approx_inv :: Ptr CAcbMat -> Ptr CAcbMat -> CLong -> IO CInt

-- Characteristic polynomial and companion matrix ------------------------------

foreign import ccall "acb_mat.h _acb_mat_charpoly"
  _acb_mat_charpoly :: Ptr CAcb -> Ptr CAcbMat -> CLong -> IO ()

-- | /acb_mat_charpoly/ /poly/ /mat/ /prec/ 
-- 
-- Sets /poly/ to the characteristic polynomial of /mat/ which must be a
-- square matrix. If the matrix has /n/ rows, the underscore method
-- requires space for \(n + 1\) output coefficients. Employs a
-- division-free algorithm using \(O(n^4)\) operations.
foreign import ccall "acb_mat.h acb_mat_charpoly"
  acb_mat_charpoly :: Ptr CAcbPoly -> Ptr CAcbMat -> CLong -> IO ()

foreign import ccall "acb_mat.h _acb_mat_companion"
  _acb_mat_companion :: Ptr CAcbMat -> Ptr CAcb -> CLong -> IO ()

-- | /acb_mat_companion/ /mat/ /poly/ /prec/ 
-- 
-- Sets the /n/ by /n/ matrix /mat/ to the companion matrix of the
-- polynomial /poly/ which must have degree /n/. The underscore method
-- reads \(n + 1\) input coefficients.
foreign import ccall "acb_mat.h acb_mat_companion"
  acb_mat_companion :: Ptr CAcbMat -> Ptr CAcbPoly -> CLong -> IO ()

-- Special functions -----------------------------------------------------------

-- | /acb_mat_exp_taylor_sum/ /S/ /A/ /N/ /prec/ 
-- 
-- Sets /S/ to the truncated exponential Taylor series
-- \(S = \sum_{k=0}^{N-1} A^k / k!\). See @arb_mat_exp_taylor_sum@ for
-- implementation notes.
foreign import ccall "acb_mat.h acb_mat_exp_taylor_sum"
  acb_mat_exp_taylor_sum :: Ptr CAcbMat -> Ptr CAcbMat -> CLong -> CLong -> IO ()

-- | /acb_mat_exp/ /B/ /A/ /prec/ 
-- 
-- Sets /B/ to the exponential of the matrix /A/, defined by the Taylor
-- series
-- 
-- \[`\]
-- \[\exp(A) = \sum_{k=0}^{\infty} \frac{A^k}{k!}.\]
-- 
-- The function is evaluated as \(\exp(A/2^r)^{2^r}\), where \(r\) is
-- chosen to give rapid convergence of the Taylor series. Error bounds are
-- computed as for @arb_mat_exp@.
foreign import ccall "acb_mat.h acb_mat_exp"
  acb_mat_exp :: Ptr CAcbMat -> Ptr CAcbMat -> CLong -> IO ()

-- | /acb_mat_trace/ /trace/ /mat/ /prec/ 
-- 
-- Sets /trace/ to the trace of the matrix, i.e. the sum of entries on the
-- main diagonal of /mat/. The matrix is required to be square.
foreign import ccall "acb_mat.h acb_mat_trace"
  acb_mat_trace :: Ptr CAcb -> Ptr CAcbMat -> CLong -> IO ()

foreign import ccall "acb_mat.h _acb_mat_diag_prod"
  _acb_mat_diag_prod :: Ptr CAcb -> Ptr CAcbMat -> CLong -> CLong -> CLong -> IO ()

-- | /acb_mat_diag_prod/ /res/ /mat/ /prec/ 
-- 
-- Sets /res/ to the product of the entries on the main diagonal of /mat/.
-- The underscore method computes the product of the entries between index
-- /a/ inclusive and /b/ exclusive (the indices must be in range).
foreign import ccall "acb_mat.h acb_mat_diag_prod"
  acb_mat_diag_prod :: Ptr CAcb -> Ptr CAcbMat -> CLong -> IO ()

-- Component and error operations ----------------------------------------------

-- | /acb_mat_get_mid/ /B/ /A/ 
-- 
-- Sets the entries of /B/ to the exact midpoints of the entries of /A/.
foreign import ccall "acb_mat.h acb_mat_get_mid"
  acb_mat_get_mid :: Ptr CAcbMat -> Ptr CAcbMat -> IO ()

-- | /acb_mat_add_error_mag/ /mat/ /err/ 
-- 
-- Adds /err/ in-place to the radii of the entries of /mat/.
foreign import ccall "acb_mat.h acb_mat_add_error_mag"
  acb_mat_add_error_mag :: Ptr CAcbMat -> Ptr CMag -> IO ()

-- Eigenvalues and eigenvectors ------------------------------------------------

-- The functions in this section are experimental. There are classes of
-- matrices where the algorithms fail to converge even as /prec/ is
-- increased, or for which the error bounds are much worse than necessary.
-- In some cases, it can help to manually precondition the matrix /A/ by
-- applying a similarity transformation \(T^{-1} A T\).
--



-- | /acb_mat_approx_eig_qr/ /E/ /L/ /R/ /A/ /tol/ /maxiter/ /prec/ 
-- 
-- Computes floating-point approximations of all the /n/ eigenvalues (and
-- optionally eigenvectors) of the given /n/ by /n/ matrix /A/. The
-- approximations of the eigenvalues are written to the vector /E/, in no
-- particular order. If /L/ is not /NULL/, approximations of the
-- corresponding left eigenvectors are written to the rows of /L/. If /R/
-- is not /NULL/, approximations of the corresponding right eigenvectors
-- are written to the columns of /R/.
-- 
-- The parameters /tol/ and /maxiter/ can be used to control the target
-- numerical error and the maximum number of iterations allowed before
-- giving up. Passing /NULL/ and 0 respectively results in default values
-- being used.
-- 
-- Uses the implicitly shifted QR algorithm with reduction to Hessenberg
-- form. No guarantees are made about the accuracy of the output. A nonzero
-- return value indicates that the QR iteration converged numerically, but
-- this is only a heuristic termination test and does not imply any
-- statement whatsoever about error bounds. The output may also be accurate
-- even if this function returns zero.
foreign import ccall "acb_mat.h acb_mat_approx_eig_qr"
  acb_mat_approx_eig_qr :: Ptr CAcb -> Ptr CAcbMat -> Ptr CAcbMat -> Ptr CAcbMat -> Ptr CMag -> CLong -> CLong -> IO CInt

-- | /acb_mat_eig_global_enclosure/ /eps/ /A/ /E/ /R/ /prec/ 
-- 
-- Given an /n/ by /n/ matrix /A/, a length-/n/ vector /E/ containing
-- approximations of the eigenvalues of /A/, and an /n/ by /n/ matrix /R/
-- containing approximations of the corresponding right eigenvectors,
-- computes a rigorous bound \(\varepsilon\) such that every eigenvalue
-- \(\lambda\) of /A/ satisfies
-- \(|\lambda - \hat \lambda_k| \le \varepsilon\) for some
-- \(\hat \lambda_k\) in /E/. In other words, the union of the balls
-- \(B_k = \{z : |z - \hat \lambda_k| \le \varepsilon\}\) is guaranteed to
-- be an enclosure of all eigenvalues of /A/.
-- 
-- Note that there is no guarantee that each ball \(B_k\) can be identified
-- with a single eigenvalue: it is possible that some balls contain several
-- eigenvalues while other balls contain no eigenvalues. In other words,
-- this method is not powerful enough to compute isolating balls for the
-- individual eigenvalues (or even for clusters of eigenvalues other than
-- the whole spectrum). Nevertheless, in practice the balls \(B_k\) will
-- represent eigenvalues one-to-one with high probability if the given
-- approximations are good.
-- 
-- The output can be used to certify that all eigenvalues of /A/ lie in
-- some region of the complex plane (such as a specific half-plane, strip,
-- disk, or annulus) without the need to certify the individual
-- eigenvalues. The output is easily converted into lower or upper bounds
-- for the absolute values or real or imaginary parts of the spectrum, and
-- with high probability these bounds will be tight. Using
-- @acb_add_error_mag@ and @acb_union@, the output can also be converted to
-- a single @acb_t@ enclosing the whole spectrum of /A/ in a rectangle, but
-- note that to test whether a condition holds for all eigenvalues of /A/,
-- it is typically better to iterate over the individual balls \(B_k\).
-- 
-- This function implements the fast algorithm in Theorem 1 in < [Miy2010]>
-- which extends the Bauer-Fike theorem. Approximations /E/ and /R/ can,
-- for instance, be computed using @acb_mat_approx_eig_qr@. No assumptions
-- are made about the structure of /A/ or the quality of the given
-- approximations.
foreign import ccall "acb_mat.h acb_mat_eig_global_enclosure"
  acb_mat_eig_global_enclosure :: Ptr CMag -> Ptr CAcbMat -> Ptr CAcb -> Ptr CAcbMat -> CLong -> IO ()

-- | /acb_mat_eig_enclosure_rump/ /lambda/ /J/ /R/ /A/ /lambda_approx/ /R_approx/ /prec/ 
-- 
-- Given an /n/ by /n/ matrix /A/ and an approximate eigenvalue-eigenvector
-- pair /lambda_approx/ and /R_approx/ (where /R_approx/ is an /n/ by 1
-- matrix), computes an enclosure /lambda/ guaranteed to contain at least
-- one of the eigenvalues of /A/, along with an enclosure /R/ for a
-- corresponding right eigenvector.
-- 
-- More generally, this function can handle clustered (or repeated)
-- eigenvalues. If /R_approx/ is an /n/ by /k/ matrix containing
-- approximate eigenvectors for a presumed cluster of /k/ eigenvalues near
-- /lambda_approx/, this function computes an enclosure /lambda/ guaranteed
-- to contain at least /k/ eigenvalues of /A/ along with a matrix /R/
-- guaranteed to contain a basis for the /k/-dimensional invariant subspace
-- associated with these eigenvalues. Note that for multiple eigenvalues,
-- determining the individual eigenvectors is an ill-posed problem;
-- describing an enclosure of the invariant subspace is the best we can
-- hope for.
-- 
-- For \(k = 1\), it is guaranteed that \(AR - R \lambda\) contains the
-- zero matrix. For \(k > 2\), this cannot generally be guaranteed (in
-- particular, /A/ might not diagonalizable). In this case, we can still
-- compute an approximately diagonal /k/ by /k/ interval matrix
-- \(J \approx \lambda I\) such that \(AR - RJ\) is guaranteed to contain
-- the zero matrix. This matrix has the property that the Jordan canonical
-- form of (any exact matrix contained in) /A/ has a /k/ by /k/ submatrix
-- equal to the Jordan canonical form of (some exact matrix contained in)
-- /J/. The output /J/ is optional (the user can pass /NULL/ to omit it).
-- 
-- The algorithm follows section 13.4 in < [Rum2010]>, corresponding to the
-- @verifyeig()@ routine in INTLAB. The initial approximations can, for
-- instance, be computed using @acb_mat_approx_eig_qr@. No assumptions are
-- made about the structure of /A/ or the quality of the given
-- approximations.
foreign import ccall "acb_mat.h acb_mat_eig_enclosure_rump"
  acb_mat_eig_enclosure_rump :: Ptr CAcb -> Ptr CAcbMat -> Ptr CAcbMat -> Ptr CAcbMat -> Ptr CAcb -> Ptr CAcbMat -> CLong -> IO ()

foreign import ccall "acb_mat.h acb_mat_eig_simple_rump"
  acb_mat_eig_simple_rump :: Ptr CAcb -> Ptr CAcbMat -> Ptr CAcbMat -> Ptr CAcbMat -> Ptr CAcb -> Ptr CAcbMat -> CLong -> IO CInt

foreign import ccall "acb_mat.h acb_mat_eig_simple_vdhoeven_mourrain"
  acb_mat_eig_simple_vdhoeven_mourrain :: Ptr CAcb -> Ptr CAcbMat -> Ptr CAcbMat -> Ptr CAcbMat -> Ptr CAcb -> Ptr CAcbMat -> CLong -> IO CInt

-- | /acb_mat_eig_simple/ /E/ /L/ /R/ /A/ /E_approx/ /R_approx/ /prec/ 
-- 
-- Computes all the eigenvalues (and optionally corresponding eigenvectors)
-- of the given /n/ by /n/ matrix /A/.
-- 
-- Attempts to prove that /A/ has /n/ simple (isolated) eigenvalues,
-- returning 1 if successful and 0 otherwise. On success, isolating complex
-- intervals for the eigenvalues are written to the vector /E/, in no
-- particular order. If /L/ is not /NULL/, enclosures of the corresponding
-- left eigenvectors are written to the rows of /L/. If /R/ is not /NULL/,
-- enclosures of the corresponding right eigenvectors are written to the
-- columns of /R/.
-- 
-- The left eigenvectors are normalized so that \(L = R^{-1}\). This
-- produces a diagonalization \(LAR = D\) where /D/ is the diagonal matrix
-- with the entries in /E/ on the diagonal.
-- 
-- The user supplies approximations /E_approx/ and /R_approx/ of the
-- eigenvalues and the right eigenvectors. The initial approximations can,
-- for instance, be computed using @acb_mat_approx_eig_qr@. No assumptions
-- are made about the structure of /A/ or the quality of the given
-- approximations.
-- 
-- Two algorithms are implemented:
-- 
-- -   The /rump/ version calls @acb_mat_eig_enclosure_rump@ repeatedly to
--     certify eigenvalue-eigenvector pairs one by one. The iteration is
--     stopped to return non-success if a new eigenvalue overlaps with
--     previously computed one. Finally, /L/ is computed by a matrix
--     inversion. This has complexity \(O(n^4)\).
-- -   The /vdhoeven_mourrain/ version uses the algorithm in < [HM2017]> to
--     certify all eigenvalues and eigenvectors in one step. This has
--     complexity \(O(n^3)\).
-- 
-- The default version currently uses /vdhoeven_mourrain/.
-- 
-- By design, these functions terminate instead of attempting to compute
-- eigenvalue clusters if some eigenvalues cannot be isolated. To compute
-- all eigenvalues of a matrix allowing for overlap,
-- @acb_mat_eig_multiple_rump@ may be used as a fallback, or
-- @acb_mat_eig_multiple@ may be used in the first place.
foreign import ccall "acb_mat.h acb_mat_eig_simple"
  acb_mat_eig_simple :: Ptr CAcb -> Ptr CAcbMat -> Ptr CAcbMat -> Ptr CAcbMat -> Ptr CAcb -> Ptr CAcbMat -> CLong -> IO CInt

foreign import ccall "acb_mat.h acb_mat_eig_multiple_rump"
  acb_mat_eig_multiple_rump :: Ptr CAcb -> Ptr CAcbMat -> Ptr CAcb -> Ptr CAcbMat -> CLong -> IO CInt

-- | /acb_mat_eig_multiple/ /E/ /A/ /E_approx/ /R_approx/ /prec/ 
-- 
-- Computes all the eigenvalues of the given /n/ by /n/ matrix /A/. On
-- success, the output vector /E/ contains /n/ complex intervals, each
-- representing one eigenvalue of /A/ with the correct multiplicities in
-- case of overlap. The output intervals are either disjoint or identical,
-- and identical intervals are guaranteed to be grouped consecutively. Each
-- complete run of /k/ identical intervals thus represents a cluster of
-- exactly /k/ eigenvalues which could not be separated from each other at
-- the current precision, but which could be isolated from the other
-- \(n - k\) eigenvalues of the matrix.
-- 
-- The user supplies approximations /E_approx/ and /R_approx/ of the
-- eigenvalues and the right eigenvectors. The initial approximations can,
-- for instance, be computed using @acb_mat_approx_eig_qr@. No assumptions
-- are made about the structure of /A/ or the quality of the given
-- approximations.
-- 
-- The /rump/ algorithm groups approximate eigenvalues that are close and
-- calls @acb_mat_eig_enclosure_rump@ repeatedly to validate each cluster.
-- The complexity is \(O(m n^3)\) for /m/ clusters.
-- 
-- The default version, as currently implemented, first attempts to call
-- @acb_mat_eig_simple_vdhoeven_mourrain@ hoping that the eigenvalues are
-- actually simple. It then uses the /rump/ algorithm as a fallback.
foreign import ccall "acb_mat.h acb_mat_eig_multiple"
  acb_mat_eig_multiple :: Ptr CAcb -> Ptr CAcbMat -> Ptr CAcb -> Ptr CAcbMat -> CLong -> IO CInt

