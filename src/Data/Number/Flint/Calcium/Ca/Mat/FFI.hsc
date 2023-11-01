module Data.Number.Flint.Calcium.Ca.Mat.FFI (
  -- * Matrices over the real and complex numbers
    CaMat (..)
  , CCaMat (..)
  , newCaMat
  , withCaMat
  , withNewCaMat
  -- * Types, macros and constants
  , ca_mat_entry
  , ca_mat_entry_ptr
  -- * Memory management
  , ca_mat_init
  , ca_mat_clear
  , ca_mat_swap
  , ca_mat_window_init
  , ca_mat_window_clear
  -- * Assignment and conversions
  , ca_mat_set
  , ca_mat_set_fmpz_mat
  , ca_mat_set_fmpq_mat
  , ca_mat_set_ca
  , ca_mat_transfer
  -- * Random generation
  , ca_mat_randtest
  , ca_mat_randtest_rational
  , ca_mat_randops
  -- * Input and output
  , ca_mat_get_str
  , ca_mat_fprint
  , ca_mat_print
  , ca_mat_printn
  -- * Special matrices
  , ca_mat_zero
  , ca_mat_one
  , ca_mat_ones
  , ca_mat_pascal
  , ca_mat_stirling
  , ca_mat_hilbert
  , ca_mat_dft
  -- * Comparisons and properties
  , ca_mat_check_equal
  , ca_mat_check_is_zero
  , ca_mat_check_is_one
  -- * Conjugate and transpose
  , ca_mat_transpose
  , ca_mat_conj
  , ca_mat_conj_transpose
  -- * Arithmetic
  , ca_mat_neg
  , ca_mat_add
  , ca_mat_sub
  , ca_mat_mul_classical
  , ca_mat_mul_same_nf
  , ca_mat_mul
  , ca_mat_mul_si
  , ca_mat_mul_fmpz
  , ca_mat_mul_fmpq
  , ca_mat_mul_ca
  , ca_mat_div_si
  , ca_mat_div_fmpz
  , ca_mat_div_fmpq
  , ca_mat_div_ca
  , ca_mat_add_ca
  , ca_mat_sub_ca
  , ca_mat_addmul_ca
  , ca_mat_submul_ca
  -- * Powers
  , ca_mat_sqr
  , ca_mat_pow_ui_binexp
  -- * Polynomial evaluation
  , _ca_mat_ca_poly_evaluate
  , ca_mat_ca_poly_evaluate
  -- * Gaussian elimination and LU decomposition
  , ca_mat_find_pivot
  , ca_mat_lu_classical
  , ca_mat_lu_recursive
  , ca_mat_lu
  , ca_mat_fflu
  , ca_mat_nonsingular_lu
  , ca_mat_nonsingular_fflu
  -- * Solving and inverse
  , ca_mat_inv
  , ca_mat_nonsingular_solve_adjugate
  , ca_mat_nonsingular_solve_fflu
  , ca_mat_nonsingular_solve_lu
  , ca_mat_nonsingular_solve
  , ca_mat_solve_tril_classical
  , ca_mat_solve_tril_recursive
  , ca_mat_solve_tril
  , ca_mat_solve_triu_classical
  , ca_mat_solve_triu_recursive
  , ca_mat_solve_triu
  , ca_mat_solve_fflu_precomp
  , ca_mat_solve_lu_precomp
  -- * Rank and echelon form
  , ca_mat_rank
  , ca_mat_rref_fflu
  , ca_mat_rref_lu
  , ca_mat_rref
  , ca_mat_right_kernel
  -- * Determinant and trace
  , ca_mat_trace
  , ca_mat_det_berkowitz
  , ca_mat_det_lu
  , ca_mat_det_bareiss
  , ca_mat_det_cofactor
  , ca_mat_det
  , ca_mat_adjugate_cofactor
  , ca_mat_adjugate_charpoly
  , ca_mat_adjugate
  -- * Characteristic polynomial
  , _ca_mat_charpoly_berkowitz
  , ca_mat_charpoly_berkowitz
  , _ca_mat_charpoly_danilevsky
  , ca_mat_charpoly_danilevsky
  , _ca_mat_charpoly
  , ca_mat_charpoly
  , ca_mat_companion
  -- * Eigenvalues and eigenvectors
  , ca_mat_eigenvalues
  , ca_mat_diagonalization
  -- * Jordan canonical form
  , ca_mat_jordan_blocks
  , ca_mat_set_jordan_blocks
  , ca_mat_jordan_transformation
  , ca_mat_jordan_form
  -- * Matrix functions
  , ca_mat_exp
  , ca_mat_log
) where

-- Matrices over the real and complex numbers ----------------------------------

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.C.Types
import Foreign.C.String
import Foreign.Storable

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Mat
import Data.Number.Flint.Fmpq
import Data.Number.Flint.Fmpq.Mat
import Data.Number.Flint.Calcium
import Data.Number.Flint.Calcium.Ca
import Data.Number.Flint.Calcium.Ca.Types

#include <flint/ca_mat.h>

-- ca_mat_t --------------------------------------------------------------------

instance Storable CCaMat where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size ca_mat_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment ca_mat_t}
  peek ptr = CCaMat
    <$> #{peek ca_mat_struct, entries} ptr
    <*> #{peek ca_mat_struct, r      } ptr
    <*> #{peek ca_mat_struct, c      } ptr
    <*> #{peek ca_mat_struct, rows   } ptr
  poke = error "CCaMat.poke: Not defined."
 
newCaMat rows cols ctx@(CaCtx fctx) = do
  x <- mallocForeignPtr
  withForeignPtr x $ \xp -> do
    withCaCtx ctx $ \ctxp -> do
      ca_mat_init xp rows cols ctxp
    addForeignPtrFinalizerEnv p_ca_mat_clear xp fctx
  return $ CaMat x
  
{-# INLINE withCaMat #-}
withCaMat (CaMat x) f = do
  withForeignPtr x $ \px -> f px >>= return . (CaMat x,)

{-# INLINE withNewCaMat #-}
withNewCaMat rows cols ctx f = do
  x <- newCaMat rows cols ctx
  withCaMat x f
  
--------------------------------------------------------------------------------

-- | /ca_mat_entry_ptr/ /mat/ /i/ /j/ 
--
-- Returns a pointer to the entry at row /i/ and column /j/. Equivalent to
-- @ca_mat_entry@ but implemented as a function.
foreign import ccall "ca_mat.h ca_mat_entry_ptr"
  ca_mat_entry_ptr :: Ptr CCaMat -> CLong -> CLong -> IO (Ptr CCa)

ca_mat_entry = ca_mat_entry_ptr

-- Memory management -----------------------------------------------------------

-- | /ca_mat_init/ /mat/ /r/ /c/ /ctx/ 
--
-- Initializes the matrix, setting it to the zero matrix with /r/ rows and
-- /c/ columns.
foreign import ccall "ca_mat.h ca_mat_init"
  ca_mat_init :: Ptr CCaMat -> CLong -> CLong -> Ptr CCaCtx -> IO ()

-- | /ca_mat_clear/ /mat/ /ctx/ 
--
-- Clears the matrix, deallocating all entries.
foreign import ccall "ca_mat.h ca_mat_clear"
  ca_mat_clear :: Ptr CCaMat -> Ptr CCaCtx -> IO ()

foreign import ccall "ca_mat.h &ca_mat_clear"
  p_ca_mat_clear :: FunPtr (Ptr CCaMat -> Ptr CCaCtx -> IO ())

-- | /ca_mat_swap/ /mat1/ /mat2/ /ctx/ 
--
-- Efficiently swaps /mat1/ and /mat2/.
foreign import ccall "ca_mat.h ca_mat_swap"
  ca_mat_swap :: Ptr CCaMat -> Ptr CCaMat -> Ptr CCaCtx -> IO ()

-- | /ca_mat_window_init/ /window/ /mat/ /r1/ /c1/ /r2/ /c2/ /ctx/ 
--
-- Initializes /window/ to a window matrix into the submatrix of /mat/
-- starting at the corner at row /r1/ and column /c1/ (inclusive) and
-- ending at row /r2/ and column /c2/ (exclusive).
foreign import ccall "ca_mat.h ca_mat_window_init"
  ca_mat_window_init :: Ptr CCaMat -> Ptr CCaMat -> CLong -> CLong -> CLong -> CLong -> Ptr CCaCtx -> IO ()

-- | /ca_mat_window_clear/ /window/ /ctx/ 
--
-- Frees the window matrix.
foreign import ccall "ca_mat.h ca_mat_window_clear"
  ca_mat_window_clear :: Ptr CCaMat -> Ptr CCaCtx -> IO ()

-- Assignment and conversions --------------------------------------------------

-- | /ca_mat_set/ /dest/ /src/ /ctx/ 
foreign import ccall "ca_mat.h ca_mat_set"
  ca_mat_set :: Ptr CCaMat -> Ptr CCaMat -> Ptr CCaCtx -> IO ()
-- | /ca_mat_set_fmpz_mat/ /dest/ /src/ /ctx/ 
foreign import ccall "ca_mat.h ca_mat_set_fmpz_mat"
  ca_mat_set_fmpz_mat :: Ptr CCaMat -> Ptr CFmpzMat -> Ptr CCaCtx -> IO ()
-- | /ca_mat_set_fmpq_mat/ /dest/ /src/ /ctx/ 
--
-- Sets /dest/ to /src/. The operands must have identical dimensions.
foreign import ccall "ca_mat.h ca_mat_set_fmpq_mat"
  ca_mat_set_fmpq_mat :: Ptr CCaMat -> Ptr CFmpqMat -> Ptr CCaCtx -> IO ()

-- | /ca_mat_set_ca/ /mat/ /c/ /ctx/ 
--
-- Sets /mat/ to the matrix with the scalar /c/ on the main diagonal and
-- zeros elsewhere.
foreign import ccall "ca_mat.h ca_mat_set_ca"
  ca_mat_set_ca :: Ptr CCaMat -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_mat_transfer/ /res/ /res_ctx/ /src/ /src_ctx/ 
--
-- Sets /res/ to /src/ where the corresponding context objects /res_ctx/
-- and /src_ctx/ may be different.
-- 
-- This operation preserves the mathematical value represented by /src/,
-- but may result in a different internal representation depending on the
-- settings of the context objects.
foreign import ccall "ca_mat.h ca_mat_transfer"
  ca_mat_transfer :: Ptr CCaMat -> Ptr CCaCtx -> Ptr CCaMat -> Ptr CCaCtx -> IO ()

-- Random generation -----------------------------------------------------------

-- | /ca_mat_randtest/ /mat/ /state/ /depth/ /bits/ /ctx/ 
--
-- Sets /mat/ to a random matrix with entries having complexity up to
-- /depth/ and /bits/ (see @ca_randtest@).
foreign import ccall "ca_mat.h ca_mat_randtest"
  ca_mat_randtest :: Ptr CCaMat -> Ptr CFRandState -> CLong -> CLong -> Ptr CCaCtx -> IO ()

-- | /ca_mat_randtest_rational/ /mat/ /state/ /bits/ /ctx/ 
--
-- Sets /mat/ to a random rational matrix with entries up to /bits/ bits in
-- size.
foreign import ccall "ca_mat.h ca_mat_randtest_rational"
  ca_mat_randtest_rational :: Ptr CCaMat -> Ptr CFRandState -> CLong -> Ptr CCaCtx -> IO ()

-- | /ca_mat_randops/ /mat/ /state/ /count/ /ctx/ 
--
-- Randomizes /mat/ in-place by performing elementary row or column
-- operations. More precisely, at most count random additions or
-- subtractions of distinct rows and columns will be performed. This leaves
-- the rank (and for square matrices, the determinant) unchanged.
foreign import ccall "ca_mat.h ca_mat_randops"
  ca_mat_randops :: Ptr CCaMat -> Ptr CFRandState -> CLong -> Ptr CCaCtx -> IO ()

-- Input and output ------------------------------------------------------------

foreign import ccall "ca_mat.h ca_mat_get_str"
  ca_mat_get_str :: Ptr CCaMat -> Ptr CCaCtx -> IO CString

foreign import ccall "ca_mat.h ca_mat_fprint"
  ca_mat_fprint :: Ptr CFile -> Ptr CCaMat -> Ptr CCaCtx -> IO ()

-- | /ca_mat_print/ /mat/ /ctx/ 
--
-- Prints /mat/ to standard output. The entries are printed on separate
-- lines.
ca_mat_print :: Ptr CCaMat -> Ptr CCaCtx -> IO ()
ca_mat_print mat ctx = do
  printCStr (flip ca_mat_get_str ctx) mat
  return ()

-- | /ca_mat_printn/ /mat/ /digits/ /ctx/ 
--
-- Prints a decimal representation of /mat/ with precision specified by
-- /digits/. The entries are comma-separated with square brackets and comma
-- separation for the rows.
foreign import ccall "ca_mat.h ca_mat_printn"
  ca_mat_printn :: Ptr CCaMat -> CLong -> Ptr CCaCtx -> IO ()

-- Special matrices ------------------------------------------------------------

-- | /ca_mat_zero/ /mat/ /ctx/ 
--
-- Sets all entries in /mat/ to zero.
foreign import ccall "ca_mat.h ca_mat_zero"
  ca_mat_zero :: Ptr CCaMat -> Ptr CCaCtx -> IO ()

-- | /ca_mat_one/ /mat/ /ctx/ 
--
-- Sets the entries on the main diagonal of /mat/ to one, and all other
-- entries to zero.
foreign import ccall "ca_mat.h ca_mat_one"
  ca_mat_one :: Ptr CCaMat -> Ptr CCaCtx -> IO ()

-- | /ca_mat_ones/ /mat/ /ctx/ 
--
-- Sets all entries in /mat/ to one.
foreign import ccall "ca_mat.h ca_mat_ones"
  ca_mat_ones :: Ptr CCaMat -> Ptr CCaCtx -> IO ()

-- | /ca_mat_pascal/ /mat/ /triangular/ /ctx/ 
--
-- Sets /mat/ to a Pascal matrix, whose entries are binomial coefficients.
-- If /triangular/ is 0, constructs a full symmetric matrix with the rows
-- of Pascal\'s triangle as successive antidiagonals. If /triangular/ is 1,
-- constructs the upper triangular matrix with the rows of Pascal\'s
-- triangle as columns, and if /triangular/ is -1, constructs the lower
-- triangular matrix with the rows of Pascal\'s triangle as rows.
foreign import ccall "ca_mat.h ca_mat_pascal"
  ca_mat_pascal :: Ptr CCaMat -> CInt -> Ptr CCaCtx -> IO ()

-- | /ca_mat_stirling/ /mat/ /kind/ /ctx/ 
--
-- Sets /mat/ to a Stirling matrix, whose entries are Stirling numbers. If
-- /kind/ is 0, the entries are set to the unsigned Stirling numbers of the
-- first kind. If /kind/ is 1, the entries are set to the signed Stirling
-- numbers of the first kind. If /kind/ is 2, the entries are set to the
-- Stirling numbers of the second kind.
foreign import ccall "ca_mat.h ca_mat_stirling"
  ca_mat_stirling :: Ptr CCaMat -> CInt -> Ptr CCaCtx -> IO ()

-- | /ca_mat_hilbert/ /mat/ /ctx/ 
--
-- Sets /mat/ to the Hilbert matrix, which has entries
-- \(A_{i,j} = 1/(i+j+1)\).
foreign import ccall "ca_mat.h ca_mat_hilbert"
  ca_mat_hilbert :: Ptr CCaMat -> Ptr CCaCtx -> IO ()

-- | /ca_mat_dft/ /mat/ /type/ /ctx/ 
--
-- Sets /mat/ to the DFT (discrete Fourier transform) matrix of order /n/
-- where /n/ is the smallest dimension of /mat/ (if /mat/ is not square,
-- the matrix is extended periodically along the larger dimension). The
-- /type/ parameter selects between four different versions of the DFT
-- matrix (in which \(\omega = e^{2\pi i/n}\)):
-- 
-- -   Type 0 -- entries \(A_{j,k} = \omega^{-jk}\)
-- -   Type 1 -- entries \(A_{j,k} = \omega^{jk} / n\)
-- -   Type 2 -- entries \(A_{j,k} = \omega^{-jk} / \sqrt{n}\)
-- -   Type 3 -- entries \(A_{j,k} = \omega^{jk} / \sqrt{n}\)
-- 
-- The type 0 and 1 matrices are inverse pairs, and similarly for the type
-- 2 and 3 matrices.
foreign import ccall "ca_mat.h ca_mat_dft"
  ca_mat_dft :: Ptr CCaMat -> CInt -> Ptr CCaCtx -> IO ()

-- Comparisons and properties --------------------------------------------------

-- | /ca_mat_check_equal/ /A/ /B/ /ctx/ 
--
-- Compares /A/ and /B/ for equality.
foreign import ccall "ca_mat.h ca_mat_check_equal"
  ca_mat_check_equal :: Ptr CCaMat -> Ptr CCaMat -> Ptr CCaCtx -> IO (Ptr CTruth)

-- | /ca_mat_check_is_zero/ /A/ /ctx/ 
--
-- Tests if /A/ is the zero matrix.
foreign import ccall "ca_mat.h ca_mat_check_is_zero"
  ca_mat_check_is_zero :: Ptr CCaMat -> Ptr CCaCtx -> IO (Ptr CTruth)

-- | /ca_mat_check_is_one/ /A/ /ctx/ 
--
-- Tests if /A/ has ones on the main diagonal and zeros elsewhere.
foreign import ccall "ca_mat.h ca_mat_check_is_one"
  ca_mat_check_is_one :: Ptr CCaMat -> Ptr CCaCtx -> IO (Ptr CTruth)

-- Conjugate and transpose -----------------------------------------------------

-- | /ca_mat_transpose/ /res/ /A/ /ctx/ 
--
-- Sets /res/ to the transpose of /A/.
foreign import ccall "ca_mat.h ca_mat_transpose"
  ca_mat_transpose :: Ptr CCaMat -> Ptr CCaMat -> Ptr CCaCtx -> IO ()

-- | /ca_mat_conj/ /res/ /A/ /ctx/ 
--
-- Sets /res/ to the entrywise complex conjugate of /A/.
foreign import ccall "ca_mat.h ca_mat_conj"
  ca_mat_conj :: Ptr CCaMat -> Ptr CCaMat -> Ptr CCaCtx -> IO ()

-- | /ca_mat_conj_transpose/ /res/ /A/ /ctx/ 
--
-- Sets /res/ to the conjugate transpose (Hermitian transpose) of /A/.
foreign import ccall "ca_mat.h ca_mat_conj_transpose"
  ca_mat_conj_transpose :: Ptr CCaMat -> Ptr CCaMat -> Ptr CCaCtx -> IO ()

-- Arithmetic ------------------------------------------------------------------

-- | /ca_mat_neg/ /res/ /A/ /ctx/ 
--
-- Sets /res/ to the negation of /A/.
foreign import ccall "ca_mat.h ca_mat_neg"
  ca_mat_neg :: Ptr CCaMat -> Ptr CCaMat -> Ptr CCaCtx -> IO ()

-- | /ca_mat_add/ /res/ /A/ /B/ /ctx/ 
--
-- Sets /res/ to the sum of /A/ and /B/.
foreign import ccall "ca_mat.h ca_mat_add"
  ca_mat_add :: Ptr CCaMat -> Ptr CCaMat -> Ptr CCaMat -> Ptr CCaCtx -> IO ()

-- | /ca_mat_sub/ /res/ /A/ /B/ /ctx/ 
--
-- Sets /res/ to the difference of /A/ and /B/.
foreign import ccall "ca_mat.h ca_mat_sub"
  ca_mat_sub :: Ptr CCaMat -> Ptr CCaMat -> Ptr CCaMat -> Ptr CCaCtx -> IO ()

-- | /ca_mat_mul_classical/ /res/ /A/ /B/ /ctx/ 
foreign import ccall "ca_mat.h ca_mat_mul_classical"
  ca_mat_mul_classical :: Ptr CCaMat -> Ptr CCaMat -> Ptr CCaMat -> Ptr CCaCtx -> IO ()
-- | /ca_mat_mul_same_nf/ /res/ /A/ /B/ /K/ /ctx/ 
foreign import ccall "ca_mat.h ca_mat_mul_same_nf"
  ca_mat_mul_same_nf :: Ptr CCaMat -> Ptr CCaMat -> Ptr CCaMat -> Ptr CCaField -> Ptr CCaCtx -> IO ()
-- | /ca_mat_mul/ /res/ /A/ /B/ /ctx/ 
--
-- Sets /res/ to the matrix product of /A/ and /B/. The /classical/ version
-- uses classical multiplication. The /same_nf/ version assumes (not
-- checked) that both /A/ and /B/ have coefficients in the same simple
-- algebraic number field /K/ or in \(\mathbb{Q}\). The default version
-- chooses an algorithm automatically.
foreign import ccall "ca_mat.h ca_mat_mul"
  ca_mat_mul :: Ptr CCaMat -> Ptr CCaMat -> Ptr CCaMat -> Ptr CCaCtx -> IO ()

-- | /ca_mat_mul_si/ /B/ /A/ /c/ /ctx/ 
foreign import ccall "ca_mat.h ca_mat_mul_si"
  ca_mat_mul_si :: Ptr CCaMat -> Ptr CCaMat -> CLong -> Ptr CCaCtx -> IO ()
-- | /ca_mat_mul_fmpz/ /B/ /A/ /c/ /ctx/ 
foreign import ccall "ca_mat.h ca_mat_mul_fmpz"
  ca_mat_mul_fmpz :: Ptr CCaMat -> Ptr CCaMat -> Ptr CFmpz -> Ptr CCaCtx -> IO ()
-- | /ca_mat_mul_fmpq/ /B/ /A/ /c/ /ctx/ 
foreign import ccall "ca_mat.h ca_mat_mul_fmpq"
  ca_mat_mul_fmpq :: Ptr CCaMat -> Ptr CCaMat -> Ptr CFmpq -> Ptr CCaCtx -> IO ()
-- | /ca_mat_mul_ca/ /B/ /A/ /c/ /ctx/ 
--
-- Sets /B/ to /A/ multiplied by the scalar /c/.
foreign import ccall "ca_mat.h ca_mat_mul_ca"
  ca_mat_mul_ca :: Ptr CCaMat -> Ptr CCaMat -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_mat_div_si/ /B/ /A/ /c/ /ctx/ 
foreign import ccall "ca_mat.h ca_mat_div_si"
  ca_mat_div_si :: Ptr CCaMat -> Ptr CCaMat -> CLong -> Ptr CCaCtx -> IO ()
-- | /ca_mat_div_fmpz/ /B/ /A/ /c/ /ctx/ 
foreign import ccall "ca_mat.h ca_mat_div_fmpz"
  ca_mat_div_fmpz :: Ptr CCaMat -> Ptr CCaMat -> Ptr CFmpz -> Ptr CCaCtx -> IO ()
-- | /ca_mat_div_fmpq/ /B/ /A/ /c/ /ctx/ 
foreign import ccall "ca_mat.h ca_mat_div_fmpq"
  ca_mat_div_fmpq :: Ptr CCaMat -> Ptr CCaMat -> Ptr CFmpq -> Ptr CCaCtx -> IO ()
-- | /ca_mat_div_ca/ /B/ /A/ /c/ /ctx/ 
--
-- Sets /B/ to /A/ divided by the scalar /c/.
foreign import ccall "ca_mat.h ca_mat_div_ca"
  ca_mat_div_ca :: Ptr CCaMat -> Ptr CCaMat -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_mat_add_ca/ /B/ /A/ /c/ /ctx/ 
foreign import ccall "ca_mat.h ca_mat_add_ca"
  ca_mat_add_ca :: Ptr CCaMat -> Ptr CCaMat -> Ptr CCa -> Ptr CCaCtx -> IO ()
-- | /ca_mat_sub_ca/ /B/ /A/ /c/ /ctx/ 
--
-- Sets /B/ to /A/ plus or minus the scalar /c/ (interpreted as a diagonal
-- matrix).
foreign import ccall "ca_mat.h ca_mat_sub_ca"
  ca_mat_sub_ca :: Ptr CCaMat -> Ptr CCaMat -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_mat_addmul_ca/ /B/ /A/ /c/ /ctx/ 
foreign import ccall "ca_mat.h ca_mat_addmul_ca"
  ca_mat_addmul_ca :: Ptr CCaMat -> Ptr CCaMat -> Ptr CCa -> Ptr CCaCtx -> IO ()
-- | /ca_mat_submul_ca/ /B/ /A/ /c/ /ctx/ 
--
-- Sets the matrix /B/ to /B/ plus (or minus) the matrix /A/ multiplied by
-- the scalar /c/.
foreign import ccall "ca_mat.h ca_mat_submul_ca"
  ca_mat_submul_ca :: Ptr CCaMat -> Ptr CCaMat -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- Powers ----------------------------------------------------------------------

-- | /ca_mat_sqr/ /B/ /A/ /ctx/ 
--
-- Sets /B/ to the square of /A/.
foreign import ccall "ca_mat.h ca_mat_sqr"
  ca_mat_sqr :: Ptr CCaMat -> Ptr CCaMat -> Ptr CCaCtx -> IO ()

-- | /ca_mat_pow_ui_binexp/ /B/ /A/ /exp/ /ctx/ 
--
-- Sets /B/ to /A/ raised to the power /exp/, evaluated using binary
-- exponentiation.
foreign import ccall "ca_mat.h ca_mat_pow_ui_binexp"
  ca_mat_pow_ui_binexp :: Ptr CCaMat -> Ptr CCaMat -> CULong -> Ptr CCaCtx -> IO ()

-- Polynomial evaluation -------------------------------------------------------

-- | /_ca_mat_ca_poly_evaluate/ /res/ /poly/ /len/ /A/ /ctx/ 
foreign import ccall "ca_mat.h _ca_mat_ca_poly_evaluate"
  _ca_mat_ca_poly_evaluate :: Ptr CCaMat -> Ptr CCa -> CLong -> Ptr CCaMat -> Ptr CCaCtx -> IO ()
-- | /ca_mat_ca_poly_evaluate/ /res/ /poly/ /A/ /ctx/ 
--
-- Sets /res/ to \(f(A)\) where /f/ is the polynomial given by /poly/ and
-- /A/ is a square matrix. Uses the Paterson-Stockmeyer algorithm.
foreign import ccall "ca_mat.h ca_mat_ca_poly_evaluate"
  ca_mat_ca_poly_evaluate :: Ptr CCaMat -> Ptr CCaPoly -> Ptr CCaMat -> Ptr CCaCtx -> IO ()

-- Gaussian elimination and LU decomposition -----------------------------------

-- | /ca_mat_find_pivot/ /pivot_row/ /mat/ /start_row/ /end_row/ /column/ /ctx/ 
--
-- Attempts to find a nonzero entry in /mat/ with column index /column/ and
-- row index between /start_row/ (inclusive) and /end_row/ (exclusive).
-- 
-- If the return value is @T_TRUE@, such an element exists, and /pivot_row/
-- is set to the row index. If the return value is @T_FALSE@, no such
-- element exists (all entries in this part of the column are zero). If the
-- return value is @T_UNKNOWN@, it is unknown whether such an element
-- exists (zero certification failed).
-- 
-- This function is destructive: any elements that are nontrivially zero
-- but can be certified zero will be overwritten by exact zeros.
foreign import ccall "ca_mat.h ca_mat_find_pivot"
  ca_mat_find_pivot :: Ptr CLong -> Ptr CCaMat -> CLong -> CLong -> CLong -> Ptr CCaCtx -> IO (Ptr CTruth)

-- | /ca_mat_lu_classical/ /rank/ /P/ /LU/ /A/ /rank_check/ /ctx/ 
foreign import ccall "ca_mat.h ca_mat_lu_classical"
  ca_mat_lu_classical :: Ptr CLong -> Ptr CLong -> Ptr CCaMat -> Ptr CCaMat -> CInt -> Ptr CCaCtx -> IO CInt
-- | /ca_mat_lu_recursive/ /rank/ /P/ /LU/ /A/ /rank_check/ /ctx/ 
foreign import ccall "ca_mat.h ca_mat_lu_recursive"
  ca_mat_lu_recursive :: Ptr CLong -> Ptr CLong -> Ptr CCaMat -> Ptr CCaMat -> CInt -> Ptr CCaCtx -> IO CInt
-- | /ca_mat_lu/ /rank/ /P/ /LU/ /A/ /rank_check/ /ctx/ 
--
-- Computes a generalized LU decomposition \(A = PLU\) of a given matrix
-- /A/, writing the rank of /A/ to /rank/.
-- 
-- If /A/ is a nonsingular square matrix, /LU/ will be set to a unit
-- diagonal lower triangular matrix /L/ and an upper triangular matrix /U/
-- (the diagonal of /L/ will not be stored explicitly).
-- 
-- If /A/ is an arbitrary matrix of rank /r/, /U/ will be in row echelon
-- form having /r/ nonzero rows, and /L/ will be lower triangular but
-- truncated to /r/ columns, having implicit ones on the /r/ first entries
-- of the main diagonal. All other entries will be zero.
-- 
-- If a nonzero value for @rank_check@ is passed, the function will abandon
-- the output matrix in an undefined state and set the rank to 0 if /A/ is
-- detected to be rank-deficient.
-- 
-- The algorithm can fail if it fails to certify that a pivot element is
-- zero or nonzero, in which case the correct rank cannot be determined.
-- The return value is 1 on success and 0 on failure. On failure, the data
-- in the output variables @rank@, @P@ and @LU@ will be meaningless.
-- 
-- The /classical/ version uses iterative Gaussian elimination. The
-- /recursive/ version uses a block recursive algorithm to take advantage
-- of fast matrix multiplication.
foreign import ccall "ca_mat.h ca_mat_lu"
  ca_mat_lu :: Ptr CLong -> Ptr CLong -> Ptr CCaMat -> Ptr CCaMat -> CInt -> Ptr CCaCtx -> IO CInt

-- | /ca_mat_fflu/ /rank/ /P/ /LU/ /den/ /A/ /rank_check/ /ctx/ 
--
-- Similar to @ca_mat_lu@, but computes a fraction-free LU decomposition
-- using the Bareiss algorithm. The denominator is written to /den/. Note
-- that despite being \"fraction-free\", this algorithm may introduce
-- fractions due to incomplete symbolic simplifications.
foreign import ccall "ca_mat.h ca_mat_fflu"
  ca_mat_fflu :: Ptr CLong -> Ptr CLong -> Ptr CCaMat -> Ptr CCa -> Ptr CCaMat -> CInt -> Ptr CCaCtx -> IO CInt

-- | /ca_mat_nonsingular_lu/ /P/ /LU/ /A/ /ctx/ 
--
-- Wrapper for @ca_mat_lu@. If /A/ can be proved to be
-- invertible\/nonsingular, returns @T_TRUE@ and sets /P/ and /LU/ to a LU
-- decomposition \(A = PLU\). If /A/ can be proved to be singular, returns
-- @T_FALSE@. If /A/ cannot be proved to be either singular or nonsingular,
-- returns @T_UNKNOWN@. When the return value is @T_FALSE@ or @T_UNKNOWN@,
-- the LU factorization is not completed and the values of /P/ and /LU/ are
-- arbitrary.
foreign import ccall "ca_mat.h ca_mat_nonsingular_lu"
  ca_mat_nonsingular_lu :: Ptr CLong -> Ptr CCaMat -> Ptr CCaMat -> Ptr CCaCtx -> IO (Ptr CTruth)

-- | /ca_mat_nonsingular_fflu/ /P/ /LU/ /den/ /A/ /ctx/ 
--
-- Wrapper for @ca_mat_fflu@. Similar to @ca_mat_nonsingular_lu@, but
-- computes a fraction-free LU decomposition using the Bareiss algorithm.
-- The denominator is written to /den/. Note that despite being
-- \"fraction-free\", this algorithm may introduce fractions due to
-- incomplete symbolic simplifications.
foreign import ccall "ca_mat.h ca_mat_nonsingular_fflu"
  ca_mat_nonsingular_fflu :: Ptr CLong -> Ptr CCaMat -> Ptr CCa -> Ptr CCaMat -> Ptr CCaCtx -> IO (Ptr CTruth)

-- Solving and inverse ---------------------------------------------------------

-- | /ca_mat_inv/ /X/ /A/ /ctx/ 
--
-- Determines if the square matrix /A/ is nonsingular, and if successful,
-- sets \(X = A^{-1}\) and returns @T_TRUE@. Returns @T_FALSE@ if /A/ is
-- singular, and @T_UNKNOWN@ if the rank of /A/ cannot be determined.
foreign import ccall "ca_mat.h ca_mat_inv"
  ca_mat_inv :: Ptr CCaMat -> Ptr CCaMat -> Ptr CCaCtx -> IO (Ptr CTruth)

-- | /ca_mat_nonsingular_solve_adjugate/ /X/ /A/ /B/ /ctx/ 
foreign import ccall "ca_mat.h ca_mat_nonsingular_solve_adjugate"
  ca_mat_nonsingular_solve_adjugate :: Ptr CCaMat -> Ptr CCaMat -> Ptr CCaMat -> Ptr CCaCtx -> IO (Ptr CTruth)
-- | /ca_mat_nonsingular_solve_fflu/ /X/ /A/ /B/ /ctx/ 
foreign import ccall "ca_mat.h ca_mat_nonsingular_solve_fflu"
  ca_mat_nonsingular_solve_fflu :: Ptr CCaMat -> Ptr CCaMat -> Ptr CCaMat -> Ptr CCaCtx -> IO (Ptr CTruth)
-- | /ca_mat_nonsingular_solve_lu/ /X/ /A/ /B/ /ctx/ 
foreign import ccall "ca_mat.h ca_mat_nonsingular_solve_lu"
  ca_mat_nonsingular_solve_lu :: Ptr CCaMat -> Ptr CCaMat -> Ptr CCaMat -> Ptr CCaCtx -> IO (Ptr CTruth)
-- | /ca_mat_nonsingular_solve/ /X/ /A/ /B/ /ctx/ 
--
-- Determines if the square matrix /A/ is nonsingular, and if successful,
-- solves \(AX = B\) and returns @T_TRUE@. Returns @T_FALSE@ if /A/ is
-- singular, and @T_UNKNOWN@ if the rank of /A/ cannot be determined.
foreign import ccall "ca_mat.h ca_mat_nonsingular_solve"
  ca_mat_nonsingular_solve :: Ptr CCaMat -> Ptr CCaMat -> Ptr CCaMat -> Ptr CCaCtx -> IO (Ptr CTruth)

-- | /ca_mat_solve_tril_classical/ /X/ /L/ /B/ /unit/ /ctx/ 
foreign import ccall "ca_mat.h ca_mat_solve_tril_classical"
  ca_mat_solve_tril_classical :: Ptr CCaMat -> Ptr CCaMat -> Ptr CCaMat -> CInt -> Ptr CCaCtx -> IO ()
-- | /ca_mat_solve_tril_recursive/ /X/ /L/ /B/ /unit/ /ctx/ 
foreign import ccall "ca_mat.h ca_mat_solve_tril_recursive"
  ca_mat_solve_tril_recursive :: Ptr CCaMat -> Ptr CCaMat -> Ptr CCaMat -> CInt -> Ptr CCaCtx -> IO ()
-- | /ca_mat_solve_tril/ /X/ /L/ /B/ /unit/ /ctx/ 
foreign import ccall "ca_mat.h ca_mat_solve_tril"
  ca_mat_solve_tril :: Ptr CCaMat -> Ptr CCaMat -> Ptr CCaMat -> CInt -> Ptr CCaCtx -> IO ()
-- | /ca_mat_solve_triu_classical/ /X/ /U/ /B/ /unit/ /ctx/ 
foreign import ccall "ca_mat.h ca_mat_solve_triu_classical"
  ca_mat_solve_triu_classical :: Ptr CCaMat -> Ptr CCaMat -> Ptr CCaMat -> CInt -> Ptr CCaCtx -> IO ()
-- | /ca_mat_solve_triu_recursive/ /X/ /U/ /B/ /unit/ /ctx/ 
foreign import ccall "ca_mat.h ca_mat_solve_triu_recursive"
  ca_mat_solve_triu_recursive :: Ptr CCaMat -> Ptr CCaMat -> Ptr CCaMat -> CInt -> Ptr CCaCtx -> IO ()
-- | /ca_mat_solve_triu/ /X/ /U/ /B/ /unit/ /ctx/ 
--
-- Solves the lower triangular system \(LX = B\) or the upper triangular
-- system \(UX = B\), respectively. It is assumed (not checked) that the
-- diagonal entries are nonzero. If /unit/ is set, the main diagonal of /L/
-- or /U/ is taken to consist of all ones, and in that case the actual
-- entries on the diagonal are not read at all and can contain other data.
-- 
-- The /classical/ versions perform the computations iteratively while the
-- /recursive/ versions perform the computations in a block recursive way
-- to benefit from fast matrix multiplication. The default versions choose
-- an algorithm automatically.
foreign import ccall "ca_mat.h ca_mat_solve_triu"
  ca_mat_solve_triu :: Ptr CCaMat -> Ptr CCaMat -> Ptr CCaMat -> CInt -> Ptr CCaCtx -> IO ()

-- | /ca_mat_solve_fflu_precomp/ /X/ /perm/ /A/ /den/ /B/ /ctx/ 
foreign import ccall "ca_mat.h ca_mat_solve_fflu_precomp"
  ca_mat_solve_fflu_precomp :: Ptr CCaMat -> Ptr CLong -> Ptr CCaMat -> Ptr CCa -> Ptr CCaMat -> Ptr CCaCtx -> IO ()
-- | /ca_mat_solve_lu_precomp/ /X/ /P/ /LU/ /B/ /ctx/ 
--
-- Solves \(AX = B\) given the precomputed nonsingular LU decomposition
-- \(A = PLU\) or fraction-free LU decomposition with denominator /den/.
-- The matrices \(X\) and \(B\) are allowed to be aliased with each other,
-- but \(X\) is not allowed to be aliased with \(LU\).
foreign import ccall "ca_mat.h ca_mat_solve_lu_precomp"
  ca_mat_solve_lu_precomp :: Ptr CCaMat -> Ptr CLong -> Ptr CCaMat -> Ptr CCaMat -> Ptr CCaCtx -> IO ()

-- Rank and echelon form -------------------------------------------------------

-- | /ca_mat_rank/ /rank/ /A/ /ctx/ 
--
-- Computes the rank of the matrix /A/. If successful, returns 1 and writes
-- the rank to @rank@. If unsuccessful, returns 0.
foreign import ccall "ca_mat.h ca_mat_rank"
  ca_mat_rank :: Ptr CLong -> Ptr CCaMat -> Ptr CCaCtx -> IO CInt

-- | /ca_mat_rref_fflu/ /rank/ /R/ /A/ /ctx/ 
foreign import ccall "ca_mat.h ca_mat_rref_fflu"
  ca_mat_rref_fflu :: Ptr CLong -> Ptr CCaMat -> Ptr CCaMat -> Ptr CCaCtx -> IO CInt
-- | /ca_mat_rref_lu/ /rank/ /R/ /A/ /ctx/ 
foreign import ccall "ca_mat.h ca_mat_rref_lu"
  ca_mat_rref_lu :: Ptr CLong -> Ptr CCaMat -> Ptr CCaMat -> Ptr CCaCtx -> IO CInt
-- | /ca_mat_rref/ /rank/ /R/ /A/ /ctx/ 
--
-- Computes the reduced row echelon form (rref) of a given matrix. On
-- success, sets /R/ to the rref of /A/, writes the rank to /rank/, and
-- returns 1. On failure to certify the correct rank, returns 0, leaving
-- the data in /rank/ and /R/ meaningless.
-- 
-- The /fflu/ version computes a fraction-free LU decomposition and then
-- converts the output ro rref form. The /lu/ version computes a regular LU
-- decomposition and then converts the output to rref form. The default
-- version uses an automatic algorithm choice and may implement additional
-- methods for special cases.
foreign import ccall "ca_mat.h ca_mat_rref"
  ca_mat_rref :: Ptr CLong -> Ptr CCaMat -> Ptr CCaMat -> Ptr CCaCtx -> IO CInt

-- | /ca_mat_right_kernel/ /X/ /A/ /ctx/ 
--
-- Sets /X/ to a basis of the right kernel (nullspace) of /A/. The output
-- matrix /X/ will be resized in-place to have a number of columns equal to
-- the nullity of /A/. Returns 1 on success. On failure, returns 0 and
-- leaves the data in /X/ meaningless.
foreign import ccall "ca_mat.h ca_mat_right_kernel"
  ca_mat_right_kernel :: Ptr CCaMat -> Ptr CCaMat -> Ptr CCaCtx -> IO CInt

-- Determinant and trace -------------------------------------------------------

-- | /ca_mat_trace/ /trace/ /mat/ /ctx/ 
--
-- Sets /trace/ to the sum of the entries on the main diagonal of /mat/.
foreign import ccall "ca_mat.h ca_mat_trace"
  ca_mat_trace :: Ptr CCa -> Ptr CCaMat -> Ptr CCaCtx -> IO ()

-- | /ca_mat_det_berkowitz/ /det/ /A/ /ctx/ 
foreign import ccall "ca_mat.h ca_mat_det_berkowitz"
  ca_mat_det_berkowitz :: Ptr CCa -> Ptr CCaMat -> Ptr CCaCtx -> IO ()
-- | /ca_mat_det_lu/ /det/ /A/ /ctx/ 
foreign import ccall "ca_mat.h ca_mat_det_lu"
  ca_mat_det_lu :: Ptr CCa -> Ptr CCaMat -> Ptr CCaCtx -> IO CInt
-- | /ca_mat_det_bareiss/ /det/ /A/ /ctx/ 
foreign import ccall "ca_mat.h ca_mat_det_bareiss"
  ca_mat_det_bareiss :: Ptr CCa -> Ptr CCaMat -> Ptr CCaCtx -> IO CInt
-- | /ca_mat_det_cofactor/ /det/ /A/ /ctx/ 
foreign import ccall "ca_mat.h ca_mat_det_cofactor"
  ca_mat_det_cofactor :: Ptr CCa -> Ptr CCaMat -> Ptr CCaCtx -> IO ()
-- | /ca_mat_det/ /det/ /A/ /ctx/ 
--
-- Sets /det/ to the determinant of the square matrix /A/. Various
-- algorithms are available:
-- 
-- -   The /berkowitz/ version uses the division-free Berkowitz algorithm
--     performing \(O(n^4)\) operations. Since no zero tests are required,
--     it is guaranteed to succeed.
-- -   The /cofactor/ version performs cofactor expansion. This is
--     currently only supported for matrices up to size 4.
-- -   The /lu/ and /bareiss/ versions use rational LU decomposition and
--     fraction-free LU decomposition (Bareiss algorithm) respectively,
--     requiring \(O(n^3)\) operations. These algorithms can fail if zero
--     certification fails (see @ca_mat_nonsingular_lu@); they return 1 for
--     success and 0 for failure. Note that the Bareiss algorithm, despite
--     being \"fraction-free\", may introduce fractions due to incomplete
--     symbolic simplifications.
-- 
-- The default function chooses an algorithm automatically. It will, in
-- addition, recognize trivially rational and integer matrices and evaluate
-- those determinants using @fmpq_mat_t@ or @fmpz_mat_t@.
-- 
-- The various algorithms can produce different symbolic forms of the same
-- determinant. Which algorithm performs better depends strongly and
-- sometimes unpredictably on the structure of the matrix.
foreign import ccall "ca_mat.h ca_mat_det"
  ca_mat_det :: Ptr CCa -> Ptr CCaMat -> Ptr CCaCtx -> IO ()

-- | /ca_mat_adjugate_cofactor/ /adj/ /det/ /A/ /ctx/ 
foreign import ccall "ca_mat.h ca_mat_adjugate_cofactor"
  ca_mat_adjugate_cofactor :: Ptr CCaMat -> Ptr CCa -> Ptr CCaMat -> Ptr CCaCtx -> IO ()
-- | /ca_mat_adjugate_charpoly/ /adj/ /det/ /A/ /ctx/ 
foreign import ccall "ca_mat.h ca_mat_adjugate_charpoly"
  ca_mat_adjugate_charpoly :: Ptr CCaMat -> Ptr CCa -> Ptr CCaMat -> Ptr CCaCtx -> IO ()
-- | /ca_mat_adjugate/ /adj/ /det/ /A/ /ctx/ 
--
-- Sets /adj/ to the adjuate matrix of /A/ and /det/ to the determinant of
-- /A/, both computed simultaneously. The /cofactor/ version uses cofactor
-- expansion. The /charpoly/ version computes and evaluates the
-- characteristic polynomial. The default version uses an automatic
-- algorithm choice.
foreign import ccall "ca_mat.h ca_mat_adjugate"
  ca_mat_adjugate :: Ptr CCaMat -> Ptr CCa -> Ptr CCaMat -> Ptr CCaCtx -> IO ()

-- Characteristic polynomial ---------------------------------------------------

-- | /_ca_mat_charpoly_berkowitz/ /cp/ /mat/ /ctx/ 
foreign import ccall "ca_mat.h _ca_mat_charpoly_berkowitz"
  _ca_mat_charpoly_berkowitz :: Ptr CCa -> Ptr CCaMat -> Ptr CCaCtx -> IO ()
-- | /ca_mat_charpoly_berkowitz/ /cp/ /mat/ /ctx/ 
foreign import ccall "ca_mat.h ca_mat_charpoly_berkowitz"
  ca_mat_charpoly_berkowitz :: Ptr CCaPoly -> Ptr CCaMat -> Ptr CCaCtx -> IO ()
-- | /_ca_mat_charpoly_danilevsky/ /cp/ /mat/ /ctx/ 
foreign import ccall "ca_mat.h _ca_mat_charpoly_danilevsky"
  _ca_mat_charpoly_danilevsky :: Ptr CCa -> Ptr CCaMat -> Ptr CCaCtx -> IO CInt
-- | /ca_mat_charpoly_danilevsky/ /cp/ /mat/ /ctx/ 
foreign import ccall "ca_mat.h ca_mat_charpoly_danilevsky"
  ca_mat_charpoly_danilevsky :: Ptr CCaPoly -> Ptr CCaMat -> Ptr CCaCtx -> IO CInt
-- | /_ca_mat_charpoly/ /cp/ /mat/ /ctx/ 
foreign import ccall "ca_mat.h _ca_mat_charpoly"
  _ca_mat_charpoly :: Ptr CCa -> Ptr CCaMat -> Ptr CCaCtx -> IO ()
-- | /ca_mat_charpoly/ /cp/ /mat/ /ctx/ 
--
-- Sets /poly/ to the characteristic polynomial of /mat/ which must be a
-- square matrix. If the matrix has /n/ rows, the underscore method
-- requires space for \(n + 1\) output coefficients.
-- 
-- The /berkowitz/ version uses a division-free algorithm requiring
-- \(O(n^4)\) operations. The /danilevsky/ version only performs \(O(n^3)\)
-- operations, but performs divisions and needs to check for zero which can
-- fail. This version returns 1 on success and 0 on failure. The default
-- version chooses an algorithm automatically.
foreign import ccall "ca_mat.h ca_mat_charpoly"
  ca_mat_charpoly :: Ptr CCaPoly -> Ptr CCaMat -> Ptr CCaCtx -> IO ()

-- | /ca_mat_companion/ /mat/ /poly/ /ctx/ 
--
-- Sets /mat/ to the companion matrix of /poly/. This function verifies
-- that the leading coefficient of /poly/ is provably nonzero and that the
-- output matrix has the right size, returning 1 on success. It returns 0
-- if the leading coefficient of /poly/ cannot be proved nonzero or if the
-- size of the output matrix does not match.
foreign import ccall "ca_mat.h ca_mat_companion"
  ca_mat_companion :: Ptr CCaMat -> Ptr CCaPoly -> Ptr CCaCtx -> IO CInt

-- Eigenvalues and eigenvectors ------------------------------------------------

-- | /ca_mat_eigenvalues/ /lambda/ /exp/ /mat/ /ctx/ 
--
-- Attempts to compute all complex eigenvalues of the given matrix /mat/.
-- On success, returns 1 and sets /lambda/ to the distinct eigenvalues with
-- corresponding multiplicities in /exp/. The eigenvalues are returned in
-- arbitrary order. On failure, returns 0 and leaves the values in /lambda/
-- and /exp/ arbitrary.
-- 
-- This function effectively computes the characteristic polynomial and
-- then calls @ca_poly_roots@.
foreign import ccall "ca_mat.h ca_mat_eigenvalues"
  ca_mat_eigenvalues :: Ptr CCaVec -> Ptr CULong -> Ptr CCaMat -> Ptr CCaCtx -> IO CInt

-- | /ca_mat_diagonalization/ /D/ /P/ /A/ /ctx/ 
--
-- Matrix diagonalization: attempts to compute a diagonal matrix /D/ and an
-- invertible matrix /P/ such that \(A = PDP^{-1}\). Returns @T_TRUE@ if
-- /A/ is diagonalizable and the computation succeeds, @T_FALSE@ if /A/ is
-- provably not diagonalizable, and @T_UNKNOWN@ if it is unknown whether
-- /A/ is diagonalizable. If the return value is not @T_TRUE@, the values
-- in /D/ and /P/ are arbitrary.
foreign import ccall "ca_mat.h ca_mat_diagonalization"
  ca_mat_diagonalization :: Ptr CCaMat -> Ptr CCaMat -> Ptr CCaMat -> Ptr CCaCtx -> IO (Ptr CTruth)

-- Jordan canonical form -------------------------------------------------------

-- | /ca_mat_jordan_blocks/ /lambda/ /num_blocks/ /block_lambda/ /block_size/ /A/ /ctx/ 
--
-- Computes the blocks of the Jordan canonical form of /A/. On success,
-- returns 1 and sets /lambda/ to the unique eigenvalues of /A/, sets
-- /num_blocks/ to the number of Jordan blocks, entry /i/ of /block_lambda/
-- to the index of the eigenvalue in Jordan block /i/, and entry /i/ of
-- /block_size/ to the size of Jordan block /i/. On failure, returns 0,
-- leaving arbitrary values in the output variables. The user should
-- allocate space in /block_lambda/ and /block_size/ for up to /n/ entries
-- where /n/ is the size of the matrix.
-- 
-- The Jordan form is unique up to the ordering of blocks, which is
-- arbitrary.
foreign import ccall "ca_mat.h ca_mat_jordan_blocks"
  ca_mat_jordan_blocks :: Ptr CCaVec -> Ptr CLong -> Ptr CLong -> Ptr CLong -> Ptr CCaMat -> Ptr CCaCtx -> IO CInt

-- | /ca_mat_set_jordan_blocks/ /mat/ /lambda/ /num_blocks/ /block_lambda/ /block_size/ /ctx/ 
--
-- Sets /mat/ to the concatenation of the Jordan blocks given in /lambda/,
-- /num_blocks/, /block_lambda/ and /block_size/. See
-- @ca_mat_jordan_blocks@ for an explanation of these variables.
foreign import ccall "ca_mat.h ca_mat_set_jordan_blocks"
  ca_mat_set_jordan_blocks :: Ptr CCaMat -> Ptr CCaVec -> CLong -> Ptr CLong -> Ptr CLong -> Ptr CCaCtx -> IO ()

-- | /ca_mat_jordan_transformation/ /mat/ /lambda/ /num_blocks/ /block_lambda/ /block_size/ /A/ /ctx/ 
--
-- Given the precomputed Jordan block decomposition (/lambda/,
-- /num_blocks/, /block_lambda/, /block_size/) of the square matrix /A/,
-- computes the corresponding transformation matrix /P/ such that
-- \(A = P J P^{-1}\). On success, writes /P/ to /mat/ and returns 1. On
-- failure, returns 0, leaving the value of /mat/ arbitrary.
foreign import ccall "ca_mat.h ca_mat_jordan_transformation"
  ca_mat_jordan_transformation :: Ptr CCaMat -> Ptr CCaVec -> CLong -> Ptr CLong -> Ptr CLong -> Ptr CCaMat -> Ptr CCaCtx -> IO CInt

-- | /ca_mat_jordan_form/ /J/ /P/ /A/ /ctx/ 
--
-- Computes the Jordan decomposition \(A = P J P^{-1}\) of the given square
-- matrix /A/. The user can pass /NULL/ for the output variable /P/, in
-- which case only /J/ is computed. On success, returns 1. On failure,
-- returns 0, leaving the values of /J/ and /P/ arbitrary.
-- 
-- This function is a convenience wrapper around @ca_mat_jordan_blocks@,
-- @ca_mat_set_jordan_blocks@ and @ca_mat_jordan_transformation@. For
-- computations with the Jordan decomposition, it is often better to use
-- those methods directly since they give direct access to the spectrum and
-- block structure.
foreign import ccall "ca_mat.h ca_mat_jordan_form"
  ca_mat_jordan_form :: Ptr CCaMat -> Ptr CCaMat -> Ptr CCaMat -> Ptr CCaCtx -> IO CInt

-- Matrix functions ------------------------------------------------------------

-- | /ca_mat_exp/ /res/ /A/ /ctx/ 
--
-- Matrix exponential: given a square matrix /A/, sets /res/ to \(e^A\) and
-- returns 1 on success. If unsuccessful, returns 0, leaving the values in
-- /res/ arbitrary.
-- 
-- This function uses Jordan decomposition. The matrix exponential always
-- exists, but computation can fail if computing the Jordan decomposition
-- fails.
foreign import ccall "ca_mat.h ca_mat_exp"
  ca_mat_exp :: Ptr CCaMat -> Ptr CCaMat -> Ptr CCaCtx -> IO CInt

-- | /ca_mat_log/ /res/ /A/ /ctx/ 
--
-- Matrix logarithm: given a square matrix /A/, sets /res/ to a logarithm
-- \(\log(A)\) and returns @T_TRUE@ on success. If /A/ can be proved to
-- have no logarithm, returns @T_FALSE@. If the existence of a logarithm
-- cannot be proved, returns @T_UNKNOWN@.
-- 
-- This function uses the Jordan decomposition, and the branch of the
-- matrix logarithm is defined by taking the principal values of the
-- logarithms of all eigenvalues.
foreign import ccall "ca_mat.h ca_mat_log"
  ca_mat_log :: Ptr CCaMat -> Ptr CCaMat -> Ptr CCaCtx -> IO (Ptr CTruth)

