{-# language
    CApiFFI
  , FlexibleInstances
  , ForeignFunctionInterface
  , MultiParamTypeClasses
  , TupleSections
  , TypeFamilies
  #-}

module Data.Number.Flint.Fq.Zech.Mat.FFI (
  -- * Matrices over finite fields (Zech logarithm representation)
    FqZechMat (..)
  , CFqZechMat (..)
  , newFqZechMat
  , withFqZechMat
  -- * Memory management
  , fq_zech_mat_init
  , fq_zech_mat_init_set
  , fq_zech_mat_clear
  , fq_zech_mat_set
  -- * Basic properties and manipulation
  , fq_zech_mat_entry
  , fq_zech_mat_entry_set
  , fq_zech_mat_nrows
  , fq_zech_mat_ncols
  , fq_zech_mat_swap
  , fq_zech_mat_swap_entrywise
  , fq_zech_mat_zero
  , fq_zech_mat_one
  -- * Conversions
  , fq_zech_mat_set_nmod_mat
  , fq_zech_mat_set_fmpz_mod_mat
  -- * Concatenate
  , fq_zech_mat_concat_vertical
  , fq_zech_mat_concat_horizontal
  -- * Printing
  , fq_zech_mat_print_pretty
  , fq_zech_mat_fprint_pretty
  , fq_zech_mat_print
  , fq_zech_mat_fprint
  -- * Window
  , fq_zech_mat_window_init
  , fq_zech_mat_window_clear
  -- * Random matrix generation
  , fq_zech_mat_randtest
  , fq_zech_mat_randpermdiag
  , fq_zech_mat_randrank
  , fq_zech_mat_randops
  , fq_zech_mat_randtril
  , fq_zech_mat_randtriu
  -- * Comparison
  , fq_zech_mat_equal
  , fq_zech_mat_is_zero
  , fq_zech_mat_is_one
  , fq_zech_mat_is_empty
  , fq_zech_mat_is_square
  -- * Addition and subtraction
  , fq_zech_mat_add
  , fq_zech_mat_sub
  , fq_zech_mat_neg
  -- * Matrix multiplication
  , fq_zech_mat_mul
  , fq_zech_mat_mul_classical
  , fq_zech_mat_mul_KS
  , fq_zech_mat_submul
  , fq_zech_mat_mul_vec
  , fq_zech_mat_mul_vec_ptr
  , fq_zech_mat_vec_mul
  , fq_zech_mat_vec_mul_ptr
  -- * LU decomposition
  , fq_zech_mat_lu
  , fq_zech_mat_lu_classical
  , fq_zech_mat_lu_recursive
  -- * Reduced row echelon form
  , fq_zech_mat_rref
  , fq_zech_mat_reduce_row
  -- * Triangular solving
  , fq_zech_mat_solve_tril
  , fq_zech_mat_solve_tril_classical
  , fq_zech_mat_solve_tril_recursive
  , fq_zech_mat_solve_triu
  , fq_zech_mat_solve_triu_classical
  , fq_zech_mat_solve_triu_recursive
  -- * Solving
  , fq_zech_mat_solve
  , fq_zech_mat_can_solve
  -- * Transforms
  , fq_zech_mat_similarity
  -- * Characteristic polynomial
  , fq_zech_mat_charpoly_danilevsky
  , fq_zech_mat_charpoly
  -- * Minimal polynomial
  , fq_zech_mat_minpoly
) where 

-- Matrices over finite fields (Zech logarithm representation) -----------------

import Foreign.C.String
import Foreign.C.Types
import qualified Foreign.Concurrent
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr )
import Foreign.Storable
import Foreign.Marshal ( free )

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Mod.Mat
import Data.Number.Flint.NMod.Poly
import Data.Number.Flint.NMod.Mat
import Data.Number.Flint.Fq
import Data.Number.Flint.Fq.NMod
import Data.Number.Flint.Fq.NMod.Mat
import Data.Number.Flint.Fq.Zech
import Data.Number.Flint.Fq.Zech.Types

#include <flint/flint.h>
#include <flint/fq_zech.h>
#include <flint/fq_zech_mat.h>

-- fq_zech_mat_t ---------------------------------------------------------------

instance Storable CFqZechMat where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fq_zech_mat_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fq_zech_mat_t}
  peek = undefined
  poke = undefined

newFqZechMat rows cols ctx@(FqZechCtx ftx) = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> do
    withFqZechCtx ctx $ \ctx -> do
      fq_zech_mat_init x rows cols ctx
    addForeignPtrFinalizerEnv p_fq_zech_mat_clear x ftx
  return $ FqZechMat x

{-# INLINE withFqZechMat #-}
withFqZechMat (FqZechMat x) f = do
  withForeignPtr x $ \px -> f px >>= return . (FqZechMat x,)

-- Memory management -----------------------------------------------------------

-- | /fq_zech_mat_init/ /mat/ /rows/ /cols/ /ctx/ 
--
-- Initialises @mat@ to a @rows@-by-@cols@ matrix with coefficients in
-- \(\mathbf{F}_{q}\) given by @ctx@. All elements are set to zero.
foreign import ccall "fq_zech_mat.h fq_zech_mat_init"
  fq_zech_mat_init :: Ptr CFqZechMat -> CLong -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_mat_init_set/ /mat/ /src/ /ctx/ 
--
-- Initialises @mat@ and sets its dimensions and elements to those of
-- @src@.
foreign import ccall "fq_zech_mat.h fq_zech_mat_init_set"
  fq_zech_mat_init_set :: Ptr CFqZechMat -> Ptr CFqZechMat -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_mat_clear/ /mat/ /ctx/ 
--
-- Clears the matrix and releases any memory it used. The matrix cannot be
-- used again until it is initialised. This function must be called exactly
-- once when finished using an @fq_zech_mat_t@ object.
foreign import ccall "fq_zech_mat.h fq_zech_mat_clear"
  fq_zech_mat_clear :: Ptr CFqZechMat -> Ptr CFqZechCtx -> IO ()

foreign import ccall "fq_zech_mat.h &fq_zech_mat_clear"
  p_fq_zech_mat_clear :: FunPtr (Ptr CFqZechMat -> Ptr CFqZechCtx -> IO ())

-- | /fq_zech_mat_set/ /mat/ /src/ /ctx/ 
--
-- Sets @mat@ to a copy of @src@. It is assumed that @mat@ and @src@ have
-- identical dimensions.
foreign import ccall "fq_zech_mat.h fq_zech_mat_set"
  fq_zech_mat_set :: Ptr CFqZechMat -> Ptr CFqZechMat -> Ptr CFqZechCtx -> IO ()

-- Basic properties and manipulation -------------------------------------------

-- | /fq_zech_mat_entry/ /mat/ /i/ /j/ 
--
-- Directly accesses the entry in @mat@ in row \(i\) and column \(j\),
-- indexed from zero. No bounds checking is performed.
foreign import ccall "fq_zech_mat.h fq_zech_mat_entry"
  fq_zech_mat_entry :: Ptr CFqZechMat
                    -> CLong -> CLong -> IO (Ptr (Ptr CFqZech))
                    
-- | /fq_zech_mat_entry_set/ /mat/ /i/ /j/ /x/ /ctx/ 
--
-- Sets the entry in @mat@ in row \(i\) and column \(j\) to @x@.
foreign import ccall "fq_zech_mat.h fq_zech_mat_entry_set"
  fq_zech_mat_entry_set :: Ptr CFqZechMat -> CLong -> CLong -> Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_mat_nrows/ /mat/ /ctx/ 
--
-- Returns the number of rows in @mat@.
foreign import ccall "fq_zech_mat.h fq_zech_mat_nrows"
  fq_zech_mat_nrows :: Ptr CFqZechMat -> Ptr CFqZechCtx -> IO CLong

-- | /fq_zech_mat_ncols/ /mat/ /ctx/ 
--
-- Returns the number of columns in @mat@.
foreign import ccall "fq_zech_mat.h fq_zech_mat_ncols"
  fq_zech_mat_ncols :: Ptr CFqZechMat -> Ptr CFqZechCtx -> IO CLong

-- | /fq_zech_mat_swap/ /mat1/ /mat2/ /ctx/ 
--
-- Swaps two matrices. The dimensions of @mat1@ and @mat2@ are allowed to
-- be different.
foreign import ccall "fq_zech_mat.h fq_zech_mat_swap"
  fq_zech_mat_swap :: Ptr CFqZechMat -> Ptr CFqZechMat -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_mat_swap_entrywise/ /mat1/ /mat2/ 
--
-- Swaps two matrices by swapping the individual entries rather than
-- swapping the contents of the structs.
foreign import ccall "fq_zech_mat.h fq_zech_mat_swap_entrywise"
  fq_zech_mat_swap_entrywise :: Ptr CFqZechMat -> Ptr CFqZechMat -> IO ()

-- | /fq_zech_mat_zero/ /mat/ /ctx/ 
--
-- Sets all entries of @mat@ to 0.
foreign import ccall "fq_zech_mat.h fq_zech_mat_zero"
  fq_zech_mat_zero :: Ptr CFqZechMat -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_mat_one/ /mat/ /ctx/ 
--
-- Sets all diagonal entries of @mat@ to 1 and all other entries to 0.
foreign import ccall "fq_zech_mat.h fq_zech_mat_one"
  fq_zech_mat_one :: Ptr CFqZechMat -> Ptr CFqZechCtx -> IO ()

-- Conversions -----------------------------------------------------------------

-- | /fq_zech_mat_set_nmod_mat/ /mat1/ /mat2/ /ctx/ 
--
-- Sets the matrix @mat1@ to the matrix @mat2@.
foreign import ccall "fq_zech_mat.h fq_zech_mat_set_nmod_mat"
  fq_zech_mat_set_nmod_mat :: Ptr CFqZechMat -> Ptr CNModMat -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_mat_set_fmpz_mod_mat/ /mat1/ /mat2/ /ctx/ 
--
-- Sets the matrix @mat1@ to the matrix @mat2@.
foreign import ccall "fq_zech_mat.h fq_zech_mat_set_fmpz_mod_mat"
  fq_zech_mat_set_fmpz_mod_mat :: Ptr CFqZechMat -> Ptr CFmpzModMat -> Ptr CFqZechCtx -> IO ()

-- Concatenate -----------------------------------------------------------------

-- | /fq_zech_mat_concat_vertical/ /res/ /mat1/ /mat2/ /ctx/ 
--
-- Sets @res@ to vertical concatenation of (@mat1@, @mat2@) in that order.
-- Matrix dimensions : @mat1@ : \(m \times n\), @mat2@ : \(k \times n\),
-- @res@ : \((m + k) \times n\).
foreign import ccall "fq_zech_mat.h fq_zech_mat_concat_vertical"
  fq_zech_mat_concat_vertical :: Ptr CFqZechMat -> Ptr CFqZechMat -> Ptr CFqZechMat -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_mat_concat_horizontal/ /res/ /mat1/ /mat2/ /ctx/ 
--
-- Sets @res@ to horizontal concatenation of (@mat1@, @mat2@) in that
-- order. Matrix dimensions : @mat1@ : \(m \times n\), @mat2@ :
-- \(m \times k\), @res@ : \(m \times (n + k)\).
foreign import ccall "fq_zech_mat.h fq_zech_mat_concat_horizontal"
  fq_zech_mat_concat_horizontal :: Ptr CFqZechMat -> Ptr CFqZechMat -> Ptr CFqZechMat -> Ptr CFqZechCtx -> IO ()

-- Printing --------------------------------------------------------------------

foreign import ccall "fq_zech_mat.h fq_zech_mat_get_str_pretty"
  fq_zech_mat_get_str_pretty :: Ptr CFqZechMat -> Ptr CFqZechCtx -> IO CString

foreign import ccall "fq_zech_mat.h fq_zech_mat_get_str"
  fq_zech_mat_get_str :: Ptr CFqZechMat -> Ptr CFqZechCtx -> IO CString
 
-- | /fq_zech_mat_print_pretty/ /mat/ /ctx/ 
--
-- Pretty-prints @mat@ to @stdout@. A header is printed followed by the
-- rows enclosed in brackets.
fq_zech_mat_print_pretty :: Ptr CFqZechMat -> Ptr CFqZechCtx -> IO ()
fq_zech_mat_print_pretty mat ctx = do
  printCStr (\mat -> fq_zech_mat_get_str_pretty mat ctx) mat
  return ()
  
-- | /fq_zech_mat_fprint_pretty/ /file/ /mat/ /ctx/ 
--
-- Pretty-prints @mat@ to @file@. A header is printed followed by the rows
-- enclosed in brackets.
-- 
-- In case of success, returns a positive value. In case of failure,
-- returns a non-positive value.
foreign import ccall "fq_zech_mat.h fq_zech_mat_fprint_pretty"
  fq_zech_mat_fprint_pretty :: Ptr CFile -> Ptr CFqZechMat -> Ptr CFqZechCtx -> IO CInt

-- | /fq_zech_mat_print/ /mat/ /ctx/ 
--
-- Prints @mat@ to @stdout@. A header is printed followed by the rows
-- enclosed in brackets.
fq_zech_mat_print :: Ptr CFqZechMat -> Ptr CFqZechCtx -> IO ()
fq_zech_mat_print mat ctx = do
  printCStr (\mat -> fq_zech_mat_get_str mat ctx) mat
  return ()
  
-- | /fq_zech_mat_fprint/ /file/ /mat/ /ctx/ 
--
-- Prints @mat@ to @file@. A header is printed followed by the rows
-- enclosed in brackets.
-- 
-- In case of success, returns a positive value. In case of failure,
-- returns a non-positive value.
foreign import ccall "fq_zech_mat.h fq_zech_mat_fprint"
  fq_zech_mat_fprint :: Ptr CFile -> Ptr CFqZechMat -> Ptr CFqZechCtx -> IO CInt

-- Window ----------------------------------------------------------------------

-- | /fq_zech_mat_window_init/ /window/ /mat/ /r1/ /c1/ /r2/ /c2/ /ctx/ 
--
-- Initializes the matrix @window@ to be an @r2 - r1@ by @c2 - c1@
-- submatrix of @mat@ whose @(0,0)@ entry is the @(r1, c1)@ entry of @mat@.
-- The memory for the elements of @window@ is shared with @mat@.
foreign import ccall "fq_zech_mat.h fq_zech_mat_window_init"
  fq_zech_mat_window_init :: Ptr CFqZechMat -> Ptr CFqZechMat -> CLong -> CLong -> CLong -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_mat_window_clear/ /window/ /ctx/ 
--
-- Clears the matrix @window@ and releases any memory that it uses. Note
-- that the memory to the underlying matrix that @window@ points to is not
-- freed.
foreign import ccall "fq_zech_mat.h fq_zech_mat_window_clear"
  fq_zech_mat_window_clear :: Ptr CFqZechMat -> Ptr CFqZechCtx -> IO ()

-- Random matrix generation ----------------------------------------------------

-- | /fq_zech_mat_randtest/ /mat/ /state/ /ctx/ 
--
-- Sets the elements of @mat@ to random elements of \(\mathbf{F}_{q}\),
-- given by @ctx@.
foreign import ccall "fq_zech_mat.h fq_zech_mat_randtest"
  fq_zech_mat_randtest :: Ptr CFqZechMat -> Ptr CFRandState -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_mat_randpermdiag/ /mat/ /state/ /diag/ /n/ /ctx/ 
--
-- Sets @mat@ to a random permutation of the diagonal matrix with \(n\)
-- leading entries given by the vector @diag@. It is assumed that the main
-- diagonal of @mat@ has room for at least \(n\) entries.
-- 
-- Returns \(0\) or \(1\), depending on whether the permutation is even or
-- odd respectively.
foreign import ccall "fq_zech_mat.h fq_zech_mat_randpermdiag"
  fq_zech_mat_randpermdiag :: Ptr CFqZechMat -> Ptr CFRandState -> Ptr (Ptr CFqZech) -> CLong -> Ptr CFqZechCtx -> IO CInt

-- | /fq_zech_mat_randrank/ /mat/ /state/ /rank/ /ctx/ 
--
-- Sets @mat@ to a random sparse matrix with the given rank, having exactly
-- as many non-zero elements as the rank, with the non-zero elements being
-- uniformly random elements of \(\mathbf{F}_{q}\).
-- 
-- The matrix can be transformed into a dense matrix with unchanged rank by
-- subsequently calling @fq_zech_mat_randops@.
foreign import ccall "fq_zech_mat.h fq_zech_mat_randrank"
  fq_zech_mat_randrank :: Ptr CFqZechMat -> Ptr CFRandState -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_mat_randops/ /mat/ /count/ /state/ /ctx/ 
--
-- Randomises @mat@ by performing elementary row or column operations. More
-- precisely, at most @count@ random additions or subtractions of distinct
-- rows and columns will be performed. This leaves the rank (and for square
-- matrices, determinant) unchanged.
foreign import ccall "fq_zech_mat.h fq_zech_mat_randops"
  fq_zech_mat_randops :: Ptr CFqZechMat -> CLong -> Ptr CFRandState -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_mat_randtril/ /mat/ /state/ /unit/ /ctx/ 
--
-- Sets @mat@ to a random lower triangular matrix. If @unit@ is 1, it will
-- have ones on the main diagonal, otherwise it will have random nonzero
-- entries on the main diagonal.
foreign import ccall "fq_zech_mat.h fq_zech_mat_randtril"
  fq_zech_mat_randtril :: Ptr CFqZechMat -> Ptr CFRandState -> CInt -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_mat_randtriu/ /mat/ /state/ /unit/ /ctx/ 
--
-- Sets @mat@ to a random upper triangular matrix. If @unit@ is 1, it will
-- have ones on the main diagonal, otherwise it will have random nonzero
-- entries on the main diagonal.
foreign import ccall "fq_zech_mat.h fq_zech_mat_randtriu"
  fq_zech_mat_randtriu :: Ptr CFqZechMat -> Ptr CFRandState -> CInt -> Ptr CFqZechCtx -> IO ()

-- Comparison ------------------------------------------------------------------

-- | /fq_zech_mat_equal/ /mat1/ /mat2/ /ctx/ 
--
-- Returns nonzero if mat1 and mat2 have the same dimensions and elements,
-- and zero otherwise.
foreign import ccall "fq_zech_mat.h fq_zech_mat_equal"
  fq_zech_mat_equal :: Ptr CFqZechMat -> Ptr CFqZechMat -> Ptr CFqZechCtx -> IO CInt

-- | /fq_zech_mat_is_zero/ /mat/ /ctx/ 
--
-- Returns a non-zero value if all entries @mat@ are zero, and otherwise
-- returns zero.
foreign import ccall "fq_zech_mat.h fq_zech_mat_is_zero"
  fq_zech_mat_is_zero :: Ptr CFqZechMat -> Ptr CFqZechCtx -> IO CInt

-- | /fq_zech_mat_is_one/ /mat/ /ctx/ 
--
-- Returns a non-zero value if all entries @mat@ are zero except the
-- diagonal entries which must be one, otherwise returns zero.
foreign import ccall "fq_zech_mat.h fq_zech_mat_is_one"
  fq_zech_mat_is_one :: Ptr CFqZechMat -> Ptr CFqZechCtx -> IO CInt

-- | /fq_zech_mat_is_empty/ /mat/ /ctx/ 
--
-- Returns a non-zero value if the number of rows or the number of columns
-- in @mat@ is zero, and otherwise returns zero.
foreign import ccall "fq_zech_mat.h fq_zech_mat_is_empty"
  fq_zech_mat_is_empty :: Ptr CFqZechMat -> Ptr CFqZechCtx -> IO CInt

-- | /fq_zech_mat_is_square/ /mat/ /ctx/ 
--
-- Returns a non-zero value if the number of rows is equal to the number of
-- columns in @mat@, and otherwise returns zero.
foreign import ccall "fq_zech_mat.h fq_zech_mat_is_square"
  fq_zech_mat_is_square :: Ptr CFqZechMat -> Ptr CFqZechCtx -> IO CInt

-- Addition and subtraction ----------------------------------------------------

-- | /fq_zech_mat_add/ /C/ /A/ /B/ /ctx/ 
--
-- Computes \(C = A + B\). Dimensions must be identical.
foreign import ccall "fq_zech_mat.h fq_zech_mat_add"
  fq_zech_mat_add :: Ptr CFqZechMat -> Ptr CFqZechMat -> Ptr CFqZechMat -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_mat_sub/ /C/ /A/ /B/ /ctx/ 
--
-- Computes \(C = A - B\). Dimensions must be identical.
foreign import ccall "fq_zech_mat.h fq_zech_mat_sub"
  fq_zech_mat_sub :: Ptr CFqZechMat -> Ptr CFqZechMat -> Ptr CFqZechMat -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_mat_neg/ /A/ /B/ /ctx/ 
--
-- Sets \(B = -A\). Dimensions must be identical.
foreign import ccall "fq_zech_mat.h fq_zech_mat_neg"
  fq_zech_mat_neg :: Ptr CFqZechMat -> Ptr CFqZechMat -> Ptr CFqZechCtx -> IO ()

-- Matrix multiplication -------------------------------------------------------

-- | /fq_zech_mat_mul/ /C/ /A/ /B/ /ctx/ 
--
-- Sets \(C = AB\). Dimensions must be compatible for matrix
-- multiplication. \(C\) is not allowed to be aliased with \(A\) or \(B\).
-- This function automatically chooses between classical and KS
-- multiplication.
foreign import ccall "fq_zech_mat.h fq_zech_mat_mul"
  fq_zech_mat_mul :: Ptr CFqZechMat -> Ptr CFqZechMat -> Ptr CFqZechMat -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_mat_mul_classical/ /C/ /A/ /B/ /ctx/ 
--
-- Sets \(C = AB\). Dimensions must be compatible for matrix
-- multiplication. \(C\) is not allowed to be aliased with \(A\) or \(B\).
-- Uses classical matrix multiplication.
foreign import ccall "fq_zech_mat.h fq_zech_mat_mul_classical"
  fq_zech_mat_mul_classical :: Ptr CFqZechMat -> Ptr CFqZechMat -> Ptr CFqZechMat -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_mat_mul_KS/ /C/ /A/ /B/ /ctx/ 
--
-- Sets \(C = AB\). Dimensions must be compatible for matrix
-- multiplication. \(C\) is not allowed to be aliased with \(A\) or \(B\).
-- Uses Kronecker substitution to perform the multiplication over the
-- integers.
foreign import ccall "fq_zech_mat.h fq_zech_mat_mul_KS"
  fq_zech_mat_mul_KS :: Ptr CFqZechMat -> Ptr CFqZechMat -> Ptr CFqZechMat -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_mat_submul/ /D/ /C/ /A/ /B/ /ctx/ 
--
-- Sets \(D = C + AB\). \(C\) and \(D\) may be aliased with each other but
-- not with \(A\) or \(B\).
foreign import ccall "fq_zech_mat.h fq_zech_mat_submul"
  fq_zech_mat_submul :: Ptr CFqZechMat -> Ptr CFqZechMat -> Ptr CFqZechMat -> Ptr CFqZechMat -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_mat_mul_vec/ /c/ /A/ /b/ /blen/ 
foreign import ccall "fq_zech_mat.h fq_zech_mat_mul_vec"
  fq_zech_mat_mul_vec :: Ptr (Ptr CFqZech) -> Ptr CFqZechMat -> Ptr (Ptr CFqZech) -> CLong -> IO ()
-- | /fq_zech_mat_mul_vec_ptr/ /c/ /A/ /b/ /blen/ 
--
-- Compute a matrix-vector product of @A@ and @(b, blen)@ and store the
-- result in @c@. The vector @(b, blen)@ is either truncated or
-- zero-extended to the number of columns of @A@. The number entries
-- written to @c@ is always equal to the number of rows of @A@.
foreign import ccall "fq_zech_mat.h fq_zech_mat_mul_vec_ptr"
  fq_zech_mat_mul_vec_ptr :: Ptr (Ptr (Ptr CFqZech)) -> Ptr CFqZechMat -> Ptr (Ptr (Ptr CFqZech)) -> CLong -> IO ()

-- | /fq_zech_mat_vec_mul/ /c/ /a/ /alen/ /B/ 
foreign import ccall "fq_zech_mat.h fq_zech_mat_vec_mul"
  fq_zech_mat_vec_mul :: Ptr (Ptr CFqZech) -> Ptr (Ptr CFqZech) -> CLong -> Ptr CFqZechMat -> IO ()
-- | /fq_zech_mat_vec_mul_ptr/ /c/ /a/ /alen/ /B/ 
--
-- Compute a vector-matrix product of @(a, alen)@ and @B@ and and store the
-- result in @c@. The vector @(a, alen)@ is either truncated or
-- zero-extended to the number of rows of @B@. The number entries written
-- to @c@ is always equal to the number of columns of @B@.
foreign import ccall "fq_zech_mat.h fq_zech_mat_vec_mul_ptr"
  fq_zech_mat_vec_mul_ptr :: Ptr (Ptr (Ptr CFqZech)) -> Ptr (Ptr (Ptr CFqZech)) -> CLong -> Ptr CFqZechMat -> IO ()

-- LU decomposition ------------------------------------------------------------

-- | /fq_zech_mat_lu/ /P/ /A/ /rank_check/ /ctx/ 
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
-- This function calls @fq_zech_mat_lu_recursive@.
foreign import ccall "fq_zech_mat.h fq_zech_mat_lu"
  fq_zech_mat_lu :: Ptr CLong -> Ptr CFqZechMat -> CInt -> Ptr CFqZechCtx -> IO CLong

-- | /fq_zech_mat_lu_classical/ /P/ /A/ /rank_check/ /ctx/ 
--
-- Computes a generalised LU decomposition \(LU = PA\) of a given matrix
-- \(A\), returning the rank of \(A\). The behavior of this function is
-- identical to that of @fq_zech_mat_lu@. Uses Gaussian elimination.
foreign import ccall "fq_zech_mat.h fq_zech_mat_lu_classical"
  fq_zech_mat_lu_classical :: Ptr CLong -> Ptr CFqZechMat -> CInt -> Ptr CFqZechCtx -> IO CLong

-- | /fq_zech_mat_lu_recursive/ /P/ /A/ /rank_check/ /ctx/ 
--
-- Computes a generalised LU decomposition \(LU = PA\) of a given matrix
-- \(A\), returning the rank of \(A\). The behavior of this function is
-- identical to that of @fq_zech_mat_lu@. Uses recursive block
-- decomposition, switching to classical Gaussian elimination for
-- sufficiently small blocks.
foreign import ccall "fq_zech_mat.h fq_zech_mat_lu_recursive"
  fq_zech_mat_lu_recursive :: Ptr CLong -> Ptr CFqZechMat -> CInt -> Ptr CFqZechCtx -> IO CLong

-- Reduced row echelon form ----------------------------------------------------

-- | /fq_zech_mat_rref/ /A/ /ctx/ 
--
-- Puts \(A\) in reduced row echelon form and returns the rank of \(A\).
-- 
-- The rref is computed by first obtaining an unreduced row echelon form
-- via LU decomposition and then solving an additional triangular system.
foreign import ccall "fq_zech_mat.h fq_zech_mat_rref"
  fq_zech_mat_rref :: Ptr CFqZechMat -> Ptr CFqZechCtx -> IO CLong

-- | /fq_zech_mat_reduce_row/ /A/ /P/ /L/ /n/ /ctx/ 
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
foreign import ccall "fq_zech_mat.h fq_zech_mat_reduce_row"
  fq_zech_mat_reduce_row :: Ptr CFqZechMat -> Ptr CLong -> Ptr CLong -> CLong -> Ptr CFqZechCtx -> IO CLong

-- Triangular solving ----------------------------------------------------------

-- | /fq_zech_mat_solve_tril/ /X/ /L/ /B/ /unit/ /ctx/ 
--
-- Sets \(X = L^{-1} B\) where \(L\) is a full rank lower triangular square
-- matrix. If @unit@ = 1, \(L\) is assumed to have ones on its main
-- diagonal, and the main diagonal will not be read. \(X\) and \(B\) are
-- allowed to be the same matrix, but no other aliasing is allowed.
-- Automatically chooses between the classical and recursive algorithms.
foreign import ccall "fq_zech_mat.h fq_zech_mat_solve_tril"
  fq_zech_mat_solve_tril :: Ptr CFqZechMat -> Ptr CFqZechMat -> Ptr CFqZechMat -> CInt -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_mat_solve_tril_classical/ /X/ /L/ /B/ /unit/ /ctx/ 
--
-- Sets \(X = L^{-1} B\) where \(L\) is a full rank lower triangular square
-- matrix. If @unit@ = 1, \(L\) is assumed to have ones on its main
-- diagonal, and the main diagonal will not be read. \(X\) and \(B\) are
-- allowed to be the same matrix, but no other aliasing is allowed. Uses
-- forward substitution.
foreign import ccall "fq_zech_mat.h fq_zech_mat_solve_tril_classical"
  fq_zech_mat_solve_tril_classical :: Ptr CFqZechMat -> Ptr CFqZechMat -> Ptr CFqZechMat -> CInt -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_mat_solve_tril_recursive/ /X/ /L/ /B/ /unit/ /ctx/ 
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
foreign import ccall "fq_zech_mat.h fq_zech_mat_solve_tril_recursive"
  fq_zech_mat_solve_tril_recursive :: Ptr CFqZechMat -> Ptr CFqZechMat -> Ptr CFqZechMat -> CInt -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_mat_solve_triu/ /X/ /U/ /B/ /unit/ /ctx/ 
--
-- Sets \(X = U^{-1} B\) where \(U\) is a full rank upper triangular square
-- matrix. If @unit@ = 1, \(U\) is assumed to have ones on its main
-- diagonal, and the main diagonal will not be read. \(X\) and \(B\) are
-- allowed to be the same matrix, but no other aliasing is allowed.
-- Automatically chooses between the classical and recursive algorithms.
foreign import ccall "fq_zech_mat.h fq_zech_mat_solve_triu"
  fq_zech_mat_solve_triu :: Ptr CFqZechMat -> Ptr CFqZechMat -> Ptr CFqZechMat -> CInt -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_mat_solve_triu_classical/ /X/ /U/ /B/ /unit/ /ctx/ 
--
-- Sets \(X = U^{-1} B\) where \(U\) is a full rank upper triangular square
-- matrix. If @unit@ = 1, \(U\) is assumed to have ones on its main
-- diagonal, and the main diagonal will not be read. \(X\) and \(B\) are
-- allowed to be the same matrix, but no other aliasing is allowed. Uses
-- forward substitution.
foreign import ccall "fq_zech_mat.h fq_zech_mat_solve_triu_classical"
  fq_zech_mat_solve_triu_classical :: Ptr CFqZechMat -> Ptr CFqZechMat -> Ptr CFqZechMat -> CInt -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_mat_solve_triu_recursive/ /X/ /U/ /B/ /unit/ /ctx/ 
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
foreign import ccall "fq_zech_mat.h fq_zech_mat_solve_triu_recursive"
  fq_zech_mat_solve_triu_recursive :: Ptr CFqZechMat -> Ptr CFqZechMat -> Ptr CFqZechMat -> CInt -> Ptr CFqZechCtx -> IO ()

-- Solving ---------------------------------------------------------------------

-- | /fq_zech_mat_solve/ /X/ /A/ /B/ /ctx/ 
--
-- Solves the matrix-matrix equation \(AX = B\).
-- 
-- Returns \(1\) if \(A\) has full rank; otherwise returns \(0\) and sets
-- the elements of \(X\) to undefined values.
-- 
-- The matrix \(A\) must be square.
foreign import ccall "fq_zech_mat.h fq_zech_mat_solve"
  fq_zech_mat_solve :: Ptr CFqZechMat -> Ptr CFqZechMat -> Ptr CFqZechMat -> Ptr CFqZechCtx -> IO CInt

-- | /fq_zech_mat_can_solve/ /X/ /A/ /B/ /ctx/ 
--
-- Solves the matrix-matrix equation \(AX = B\) over \(Fq\).
-- 
-- Returns \(1\) if a solution exists; otherwise returns \(0\) and sets the
-- elements of \(X\) to zero. If more than one solution exists, one of the
-- valid solutions is given.
-- 
-- There are no restrictions on the shape of \(A\) and it may be singular.
foreign import ccall "fq_zech_mat.h fq_zech_mat_can_solve"
  fq_zech_mat_can_solve :: Ptr CFqZechMat -> Ptr CFqZechMat -> Ptr CFqZechMat -> Ptr CFqZechCtx -> IO CInt

-- Transforms ------------------------------------------------------------------

-- | /fq_zech_mat_similarity/ /M/ /r/ /d/ /ctx/ 
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
foreign import ccall "fq_zech_mat.h fq_zech_mat_similarity"
  fq_zech_mat_similarity :: Ptr CFqZechMat -> CLong -> Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- Characteristic polynomial ---------------------------------------------------

-- | /fq_zech_mat_charpoly_danilevsky/ /p/ /M/ /ctx/ 
--
-- Compute the characteristic polynomial \(p\) of the matrix \(M\). The
-- matrix is assumed to be square.
foreign import ccall "fq_zech_mat.h fq_zech_mat_charpoly_danilevsky"
  fq_zech_mat_charpoly_danilevsky :: Ptr CFqZechPoly -> Ptr CFqZechMat -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_mat_charpoly/ /p/ /M/ 
--
-- Compute the characteristic polynomial \(p\) of the matrix \(M\). The
-- matrix is required to be square, otherwise an exception is raised.
foreign import ccall "fq_zech_mat.h fq_zech_mat_charpoly"
  fq_zech_mat_charpoly :: Ptr CFqZechPoly -> Ptr CFqZechMat -> IO ()

-- Minimal polynomial ----------------------------------------------------------

-- | /fq_zech_mat_minpoly/ /p/ /M/ /ctx/ 
--
-- Compute the minimal polynomial \(p\) of the matrix \(M\). The matrix is
-- required to be square, otherwise an exception is raised.
foreign import ccall "fq_zech_mat.h fq_zech_mat_minpoly"
  fq_zech_mat_minpoly :: Ptr CFqZechPoly -> Ptr CFqZechMat -> Ptr CFqZechCtx -> IO ()

