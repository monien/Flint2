module Data.Number.Flint.Fmpq.Mat.FFI (
  -- * Matrices over the rational numbers
    FmpqMat (..)
  , CFmpqMat (..)
  , newFmpqMat
  , withFmpqMat
  , withNewFmpqMat
  -- * Memory management
  , fmpq_mat_init
  , fmpq_mat_init_set
  , fmpq_mat_clear
  , fmpq_mat_swap
  , fmpq_mat_swap_entrywise
  -- * Entry access
  , fmpq_mat_entry
  , fmpq_mat_entry_num
  , fmpq_mat_entry_den
  , fmpq_mat_nrows
  , fmpq_mat_ncols
  -- * Basic assignment
  , fmpq_mat_set
  , fmpq_mat_zero
  , fmpq_mat_one
  , fmpq_mat_transpose
  , fmpq_mat_swap_rows
  , fmpq_mat_swap_cols
  , fmpq_mat_invert_rows
  , fmpq_mat_invert_cols
  -- * Addition, scalar multiplication
  , fmpq_mat_add
  , fmpq_mat_sub
  , fmpq_mat_neg
  , fmpq_mat_scalar_mul_fmpq
  , fmpq_mat_scalar_mul_fmpz
  , fmpq_mat_scalar_div_fmpz
  -- * Input and output
  , fmpq_mat_get_str
  , fmpq_mat_fprint
  , fmpq_mat_print
  -- * Random matrix generation
  , fmpq_mat_randbits
  , fmpq_mat_randtest
  -- * Window
  , fmpq_mat_window_init
  , fmpq_mat_window_clear
  -- * Concatenate
  , fmpq_mat_concat_vertical
  , fmpq_mat_concat_horizontal
  -- * Special matrices
  , fmpq_mat_hilbert_matrix
  -- * Basic comparison and properties
  , fmpq_mat_equal
  , fmpq_mat_is_integral
  , fmpq_mat_is_zero
  , fmpq_mat_is_one
  , fmpq_mat_is_empty
  , fmpq_mat_is_square
  -- * Integer matrix conversion
  , fmpq_mat_get_fmpz_mat
  , fmpq_mat_get_fmpz_mat_entrywise
  , fmpq_mat_get_fmpz_mat_matwise
  , fmpq_mat_get_fmpz_mat_rowwise
  , fmpq_mat_get_fmpz_mat_rowwise_2
  , fmpq_mat_get_fmpz_mat_colwise
  , fmpq_mat_set_fmpz_mat
  , fmpq_mat_set_fmpz_mat_div_fmpz
  -- * Modular reduction and rational reconstruction
  , fmpq_mat_get_fmpz_mat_mod_fmpz
  , fmpq_mat_set_fmpz_mat_mod_fmpz
  -- * Matrix multiplication
  , fmpq_mat_mul_direct
  , fmpq_mat_mul_cleared
  , fmpq_mat_mul
  , fmpq_mat_mul_fmpz_mat
  , fmpq_mat_mul_r_fmpz_mat
  , fmpq_mat_mul_fmpq_vec
  , fmpq_mat_fmpq_vec_mul
  -- * Kronecker product
  , fmpq_mat_kronecker_product
  -- * Trace
  , fmpq_mat_trace
  -- * Determinant
  , fmpq_mat_det
  -- * Nonsingular solving
  , fmpq_mat_solve_fraction_free
  , fmpq_mat_solve_fmpz_mat_fraction_free
  , fmpq_mat_can_solve_multi_mod
  , fmpq_mat_can_solve_fraction_free
  , fmpq_mat_can_solve
  -- * Inverse
  , fmpq_mat_inv
  -- * Echelon form
  , fmpq_mat_pivot
  , fmpq_mat_rref_classical
  , fmpq_mat_rref_fraction_free
  , fmpq_mat_rref
  -- * Gram-Schmidt Orthogonalisation
  , fmpq_mat_gso
  -- * Transforms
  , fmpq_mat_similarity
  -- * Characteristic polynomial
  , _fmpq_mat_charpoly
  , fmpq_mat_charpoly
  -- * Minimal polynomial
  , _fmpq_mat_minpoly
  , fmpq_mat_minpoly
) where

-- Matrices over the rational numbers ------------------------------------------

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr )
import Foreign.Storable
import Foreign.Marshal ( free )
import Foreign.Marshal.Array ( advancePtr )

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Mat
import Data.Number.Flint.Fmpq
import Data.Number.Flint.Fmpq.Poly

#include <flint/flint.h>
#include <flint/fmpq.h>
#include <flint/fmpq_mat.h>

-- fmpq_mat_t ------------------------------------------------------------------

data FmpqMat = FmpqMat {-# UNPACK #-} !(ForeignPtr CFmpqMat)
data CFmpqMat = CFmpqMat (Ptr CFmpq)  CLong CLong (Ptr (Ptr CFmpq))

instance Storable CFmpqMat where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fmpq_mat_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fmpq_mat_t}
  peek ptr = CFmpqMat
    <$> #{peek fmpq_mat_struct, entries} ptr
    <*> #{peek fmpq_mat_struct, r      } ptr
    <*> #{peek fmpq_mat_struct, c      } ptr
    <*> #{peek fmpq_mat_struct, rows   } ptr
  poke = error "CFmpqMat.poke: Not defined."

newFmpqMat rows cols = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> fmpq_mat_init x rows cols
  addForeignPtrFinalizer p_fmpq_mat_clear x
  return $ FmpqMat x

{-# INLINE withFmpqMat #-}
withFmpqMat (FmpqMat x) f = do
  withForeignPtr x $ \px -> f px >>= return . (FmpqMat x,)

{-# INLINE withNewFmpqMat #-}
withNewFmpqMat rows cols f = do
  x <- newFmpqMat rows cols
  withFmpqMat x f
 
-- Memory management -----------------------------------------------------------

-- | /fmpq_mat_init/ /mat/ /rows/ /cols/ 
-- 
-- Initialises a matrix with the given number of rows and columns for use.
foreign import ccall "fmpq_mat.h fmpq_mat_init"
  fmpq_mat_init :: Ptr CFmpqMat -> CLong -> CLong -> IO ()

-- | /fmpq_mat_init_set/ /mat1/ /mat2/ 
-- 
-- Initialises @mat1@ and sets it equal to @mat2@.
foreign import ccall "fmpq_mat.h fmpq_mat_init_set"
  fmpq_mat_init_set :: Ptr CFmpqMat -> Ptr CFmpqMat -> IO ()

-- | /fmpq_mat_clear/ /mat/ 
-- 
-- Frees all memory associated with the matrix. The matrix must be
-- reinitialised if it is to be used again.
foreign import ccall "fmpq_mat.h fmpq_mat_clear"
  fmpq_mat_clear :: Ptr CFmpqMat -> IO ()

foreign import ccall "fmpq_mat.h &fmpq_mat_clear"
  p_fmpq_mat_clear :: FunPtr (Ptr CFmpqMat -> IO ())

-- | /fmpq_mat_swap/ /mat1/ /mat2/ 
-- 
-- Swaps two matrices. The dimensions of @mat1@ and @mat2@ are allowed to
-- be different.
foreign import ccall "fmpq_mat.h fmpq_mat_swap"
  fmpq_mat_swap :: Ptr CFmpqMat -> Ptr CFmpqMat -> IO ()

-- | /fmpq_mat_swap_entrywise/ /mat1/ /mat2/ 
-- 
-- Swaps two matrices by swapping the individual entries rather than
-- swapping the contents of the structs.
foreign import ccall "fmpq_mat.h fmpq_mat_swap_entrywise"
  fmpq_mat_swap_entrywise :: Ptr CFmpqMat -> Ptr CFmpqMat -> IO ()

-- Entry access ----------------------------------------------------------------

-- | /fmpq_mat_entry/ /mat/ /i/ /j/ 
-- 
-- Gives a reference to the entry at row @i@ and column @j@. The reference
-- can be passed as an input or output variable to any @fmpq@ function for
-- direct manipulation of the matrix element. No bounds checking is
-- performed.
fmpq_mat_entry :: Ptr CFmpqMat -> CLong -> CLong -> IO (Ptr CFmpq)
fmpq_mat_entry mat i j = do
  CFmpqMat entries r c rows <- peek mat
  return $ entries `advancePtr` (fromIntegral (i*c + j))

-- | /fmpq_mat_entry_num/ /mat/ /i/ /j/ 
-- 
-- Gives a reference to the numerator of the entry at row @i@ and column
-- @j@. The reference can be passed as an input or output variable to any
-- @fmpz@ function for direct manipulation of the matrix element. No bounds
-- checking is performed.
foreign import ccall "fmpq_mat.h fmpq_mat_entry_num"
  fmpq_mat_entry_num :: Ptr CFmpqMat -> CLong -> CLong -> IO (Ptr CFmpz)

-- | /fmpq_mat_entry_den/ /mat/ /i/ /j/ 
-- 
-- Gives a reference to the denominator of the entry at row @i@ and column
-- @j@. The reference can be passed as an input or output variable to any
-- @fmpz@ function for direct manipulation of the matrix element. No bounds
-- checking is performed.
foreign import ccall "fmpq_mat.h fmpq_mat_entry_den"
  fmpq_mat_entry_den :: Ptr CFmpqMat -> CLong -> CLong -> IO (Ptr CFmpz)

-- | /fmpq_mat_nrows/ /mat/ 
-- 
-- Return the number of rows of the matrix @mat@.
foreign import ccall "fmpq_mat.h fmpq_mat_nrows"
  fmpq_mat_nrows :: Ptr CFmpqMat -> IO CLong

-- | /fmpq_mat_ncols/ /mat/ 
-- 
-- Return the number of columns of the matrix @mat@.
foreign import ccall "fmpq_mat.h fmpq_mat_ncols"
  fmpq_mat_ncols :: Ptr CFmpqMat -> IO CLong

-- Basic assignment ------------------------------------------------------------

-- | /fmpq_mat_set/ /dest/ /src/ 
-- 
-- Sets the entries in @dest@ to the same values as in @src@, assuming the
-- two matrices have the same dimensions.
foreign import ccall "fmpq_mat.h fmpq_mat_set"
  fmpq_mat_set :: Ptr CFmpqMat -> Ptr CFmpqMat -> IO ()

-- | /fmpq_mat_zero/ /mat/ 
-- 
-- Sets @mat@ to the zero matrix.
foreign import ccall "fmpq_mat.h fmpq_mat_zero"
  fmpq_mat_zero :: Ptr CFmpqMat -> IO ()

-- | /fmpq_mat_one/ /mat/ 
-- 
-- Let \(m\) be the minimum of the number of rows and columns in the matrix
-- @mat@. This function sets the first \(m \times m\) block to the identity
-- matrix, and the remaining block to zero.
foreign import ccall "fmpq_mat.h fmpq_mat_one"
  fmpq_mat_one :: Ptr CFmpqMat -> IO ()

-- | /fmpq_mat_transpose/ /rop/ /op/ 
-- 
-- Sets the matrix @rop@ to the transpose of the matrix @op@, assuming that
-- their dimensions are compatible.
foreign import ccall "fmpq_mat.h fmpq_mat_transpose"
  fmpq_mat_transpose :: Ptr CFmpqMat -> Ptr CFmpqMat -> IO ()

-- | /fmpq_mat_swap_rows/ /mat/ /perm/ /r/ /s/ 
-- 
-- Swaps rows @r@ and @s@ of @mat@. If @perm@ is non-@NULL@, the
-- permutation of the rows will also be applied to @perm@.
foreign import ccall "fmpq_mat.h fmpq_mat_swap_rows"
  fmpq_mat_swap_rows :: Ptr CFmpqMat -> Ptr CLong -> CLong -> CLong -> IO ()

-- | /fmpq_mat_swap_cols/ /mat/ /perm/ /r/ /s/ 
-- 
-- Swaps columns @r@ and @s@ of @mat@. If @perm@ is non-@NULL@, the
-- permutation of the columns will also be applied to @perm@.
foreign import ccall "fmpq_mat.h fmpq_mat_swap_cols"
  fmpq_mat_swap_cols :: Ptr CFmpqMat -> Ptr CLong -> CLong -> CLong -> IO ()

-- | /fmpq_mat_invert_rows/ /mat/ /perm/ 
-- 
-- Swaps rows @i@ and @r - i@ of @mat@ for @0 \<= i \< r\/2@, where @r@ is
-- the number of rows of @mat@. If @perm@ is non-@NULL@, the permutation of
-- the rows will also be applied to @perm@.
foreign import ccall "fmpq_mat.h fmpq_mat_invert_rows"
  fmpq_mat_invert_rows :: Ptr CFmpqMat -> Ptr CLong -> IO ()

-- | /fmpq_mat_invert_cols/ /mat/ /perm/ 
-- 
-- Swaps columns @i@ and @c - i@ of @mat@ for @0 \<= i \< c\/2@, where @c@
-- is the number of columns of @mat@. If @perm@ is non-@NULL@, the
-- permutation of the columns will also be applied to @perm@.
foreign import ccall "fmpq_mat.h fmpq_mat_invert_cols"
  fmpq_mat_invert_cols :: Ptr CFmpqMat -> Ptr CLong -> IO ()

-- Addition, scalar multiplication ---------------------------------------------

-- | /fmpq_mat_add/ /mat/ /mat1/ /mat2/ 
-- 
-- Sets @mat@ to the sum of @mat1@ and @mat2@, assuming that all three
-- matrices have the same dimensions.
foreign import ccall "fmpq_mat.h fmpq_mat_add"
  fmpq_mat_add :: Ptr CFmpqMat -> Ptr CFmpqMat -> Ptr CFmpqMat -> IO ()

-- | /fmpq_mat_sub/ /mat/ /mat1/ /mat2/ 
-- 
-- Sets @mat@ to the difference of @mat1@ and @mat2@, assuming that all
-- three matrices have the same dimensions.
foreign import ccall "fmpq_mat.h fmpq_mat_sub"
  fmpq_mat_sub :: Ptr CFmpqMat -> Ptr CFmpqMat -> Ptr CFmpqMat -> IO ()

-- | /fmpq_mat_neg/ /rop/ /op/ 
-- 
-- Sets @rop@ to the negative of @op@, assuming that the two matrices have
-- the same dimensions.
foreign import ccall "fmpq_mat.h fmpq_mat_neg"
  fmpq_mat_neg :: Ptr CFmpqMat -> Ptr CFmpqMat -> IO ()

-- | /fmpq_mat_scalar_mul_fmpq/ /rop/ /op/ /x/ 
-- 
-- Sets @rop@ to @op@ multiplied by the rational \(x\), assuming that the
-- two matrices have the same dimensions.
-- 
-- Note that the rational @x@ may not be aliased with any part of the
-- entries of @rop@.
foreign import ccall "fmpq_mat.h fmpq_mat_scalar_mul_fmpq"
  fmpq_mat_scalar_mul_fmpq :: Ptr CFmpqMat -> Ptr CFmpqMat -> Ptr CFmpq -> IO ()

-- | /fmpq_mat_scalar_mul_fmpz/ /rop/ /op/ /x/ 
-- 
-- Sets @rop@ to @op@ multiplied by the integer \(x\), assuming that the
-- two matrices have the same dimensions.
-- 
-- Note that the integer \(x\) may not be aliased with any part of the
-- entries of @rop@.
foreign import ccall "fmpq_mat.h fmpq_mat_scalar_mul_fmpz"
  fmpq_mat_scalar_mul_fmpz :: Ptr CFmpqMat -> Ptr CFmpqMat -> Ptr CFmpz -> IO ()

-- | /fmpq_mat_scalar_div_fmpz/ /rop/ /op/ /x/ 
-- 
-- Sets @rop@ to @op@ divided by the integer \(x\), assuming that the two
-- matrices have the same dimensions and that \(x\) is non-zero.
-- 
-- Note that the integer \(x\) may not be aliased with any part of the
-- entries of @rop@.
foreign import ccall "fmpq_mat.h fmpq_mat_scalar_div_fmpz"
  fmpq_mat_scalar_div_fmpz :: Ptr CFmpqMat -> Ptr CFmpqMat -> Ptr CFmpz -> IO ()

-- Input and output ------------------------------------------------------------

-- | /fmpq_mat_get_str/ /mat/
--
-- Returns a string representation.
foreign import ccall "fmpq_mat.h fmpq_mat_get_str"
  fmpq_mat_get_str :: Ptr CFmpqMat -> IO CString

-- | /fmpq_mat_fprint/ /file/ /mat/ 
-- 
-- Prints the matrix @mat@ to the stream @file@.
foreign import ccall "fmpq_mat.h fmpq_mat_fprint"
  fmpq_mat_fprint :: Ptr CFile -> Ptr CFmpqMat -> IO ()

-- | /fmpq_mat_print/ /mat/ 
-- 
-- Prints the matrix @mat@ to standard output.
fmpq_mat_print :: Ptr CFmpqMat -> IO CInt
fmpq_mat_print mat = printCStr (fmpq_mat_get_str) mat

-- Random matrix generation ----------------------------------------------------

-- | /fmpq_mat_randbits/ /mat/ /state/ /bits/ 
-- 
-- This is equivalent to applying @fmpq_randbits@ to all entries in the
-- matrix.
foreign import ccall "fmpq_mat.h fmpq_mat_randbits"
  fmpq_mat_randbits :: Ptr CFmpqMat -> Ptr CFRandState -> CFBitCnt -> IO ()

-- | /fmpq_mat_randtest/ /mat/ /state/ /bits/ 
-- 
-- This is equivalent to applying @fmpq_randtest@ to all entries in the
-- matrix.
foreign import ccall "fmpq_mat.h fmpq_mat_randtest"
  fmpq_mat_randtest :: Ptr CFmpqMat -> Ptr CFRandState -> CFBitCnt -> IO ()

-- Window ----------------------------------------------------------------------

-- | /fmpq_mat_window_init/ /window/ /mat/ /r1/ /c1/ /r2/ /c2/ 
-- 
-- Initializes the matrix @window@ to be an @r2 - r1@ by @c2 - c1@
-- submatrix of @mat@ whose @(0,0)@ entry is the @(r1, c1)@ entry of @mat@.
-- The memory for the elements of @window@ is shared with @mat@.
foreign import ccall "fmpq_mat.h fmpq_mat_window_init"
  fmpq_mat_window_init :: Ptr CFmpqMat -> Ptr CFmpqMat -> CLong -> CLong -> CLong -> CLong -> IO ()

-- | /fmpq_mat_window_clear/ /window/ 
-- 
-- Clears the matrix @window@ and releases any memory that it uses. Note
-- that the memory to the underlying matrix that @window@ points to is not
-- freed.
foreign import ccall "fmpq_mat.h fmpq_mat_window_clear"
  fmpq_mat_window_clear :: Ptr CFmpqMat -> IO ()

-- Concatenate -----------------------------------------------------------------

-- | /fmpq_mat_concat_vertical/ /res/ /mat1/ /mat2/ 
-- 
-- Sets @res@ to vertical concatenation of (@mat1@, @mat2@) in that order.
-- Matrix dimensions : @mat1@ : \(m \times n\), @mat2@ : \(k \times n\),
-- @res@ : \((m + k) \times n\).
foreign import ccall "fmpq_mat.h fmpq_mat_concat_vertical"
  fmpq_mat_concat_vertical :: Ptr CFmpqMat -> Ptr CFmpqMat -> Ptr CFmpqMat -> IO ()

-- | /fmpq_mat_concat_horizontal/ /res/ /mat1/ /mat2/ 
-- 
-- Sets @res@ to horizontal concatenation of (@mat1@, @mat2@) in that
-- order. Matrix dimensions : @mat1@ : \(m \times n\), @mat2@ :
-- \(m \times k\), @res@ : \(m \times (n + k)\).
foreign import ccall "fmpq_mat.h fmpq_mat_concat_horizontal"
  fmpq_mat_concat_horizontal :: Ptr CFmpqMat -> Ptr CFmpqMat -> Ptr CFmpqMat -> IO ()

-- Special matrices ------------------------------------------------------------

-- | /fmpq_mat_hilbert_matrix/ /mat/ 
-- 
-- Sets @mat@ to a Hilbert matrix of the given size. That is, the entry at
-- row \(i\) and column \(j\) is set to \(1/(i+j+1)\).
foreign import ccall "fmpq_mat.h fmpq_mat_hilbert_matrix"
  fmpq_mat_hilbert_matrix :: Ptr CFmpqMat -> IO ()

-- Basic comparison and properties ---------------------------------------------

-- | /fmpq_mat_equal/ /mat1/ /mat2/ 
-- 
-- Returns nonzero if @mat1@ and @mat2@ have the same shape and all their
-- entries agree, and returns zero otherwise. Assumes the entries in both
-- @mat1@ and @mat2@ are in canonical form.
foreign import ccall "fmpq_mat.h fmpq_mat_equal"
  fmpq_mat_equal :: Ptr CFmpqMat -> Ptr CFmpqMat -> IO CInt

-- | /fmpq_mat_is_integral/ /mat/ 
-- 
-- Returns nonzero if all entries in @mat@ are integer-valued, and returns
-- zero otherwise. Assumes that the entries in @mat@ are in canonical form.
foreign import ccall "fmpq_mat.h fmpq_mat_is_integral"
  fmpq_mat_is_integral :: Ptr CFmpqMat -> IO CInt

-- | /fmpq_mat_is_zero/ /mat/ 
-- 
-- Returns nonzero if all entries in @mat@ are zero, and returns zero
-- otherwise.
foreign import ccall "fmpq_mat.h fmpq_mat_is_zero"
  fmpq_mat_is_zero :: Ptr CFmpqMat -> IO CInt

-- | /fmpq_mat_is_one/ /mat/ 
-- 
-- Returns nonzero if @mat@ ones along the diagonal and zeros elsewhere,
-- and returns zero otherwise.
foreign import ccall "fmpq_mat.h fmpq_mat_is_one"
  fmpq_mat_is_one :: Ptr CFmpqMat -> IO CInt

-- | /fmpq_mat_is_empty/ /mat/ 
-- 
-- Returns a non-zero value if the number of rows or the number of columns
-- in @mat@ is zero, and otherwise returns zero.
foreign import ccall "fmpq_mat.h fmpq_mat_is_empty"
  fmpq_mat_is_empty :: Ptr CFmpqMat -> IO CInt

-- | /fmpq_mat_is_square/ /mat/ 
-- 
-- Returns a non-zero value if the number of rows is equal to the number of
-- columns in @mat@, and otherwise returns zero.
foreign import ccall "fmpq_mat.h fmpq_mat_is_square"
  fmpq_mat_is_square :: Ptr CFmpqMat -> IO CInt

-- Integer matrix conversion ---------------------------------------------------

-- | /fmpq_mat_get_fmpz_mat/ /dest/ /mat/ 
-- 
-- Sets @dest@ to @mat@ and returns nonzero if all entries in @mat@ are
-- integer-valued. If not all entries in @mat@ are integer-valued, sets
-- @dest@ to an undefined matrix and returns zero. Assumes that the entries
-- in @mat@ are in canonical form.
foreign import ccall "fmpq_mat.h fmpq_mat_get_fmpz_mat"
  fmpq_mat_get_fmpz_mat :: Ptr CFmpzMat -> Ptr CFmpqMat -> IO CInt

-- | /fmpq_mat_get_fmpz_mat_entrywise/ /num/ /den/ /mat/ 
-- 
-- Sets the integer matrices @num@ and @den@ respectively to the numerators
-- and denominators of the entries in @mat@.
foreign import ccall "fmpq_mat.h fmpq_mat_get_fmpz_mat_entrywise"
  fmpq_mat_get_fmpz_mat_entrywise :: Ptr CFmpzMat -> Ptr CFmpzMat -> Ptr CFmpqMat -> IO ()

-- | /fmpq_mat_get_fmpz_mat_matwise/ /num/ /den/ /mat/ 
-- 
-- Converts all entries in @mat@ to a common denominator, storing the
-- rescaled numerators in @num@ and the denominator in @den@. The
-- denominator will be minimal if the entries in @mat@ are in canonical
-- form.
foreign import ccall "fmpq_mat.h fmpq_mat_get_fmpz_mat_matwise"
  fmpq_mat_get_fmpz_mat_matwise :: Ptr CFmpzMat -> Ptr CFmpz -> Ptr CFmpqMat -> IO ()

-- | /fmpq_mat_get_fmpz_mat_rowwise/ /num/ /den/ /mat/ 
-- 
-- Clears denominators in @mat@ row by row. The rescaled numerators are
-- written to @num@, and the denominator of row @i@ is written to position
-- @i@ in @den@ which can be a preinitialised @fmpz@ vector. Alternatively,
-- @NULL@ can be passed as the @den@ variable, in which case the
-- denominators will not be stored.
foreign import ccall "fmpq_mat.h fmpq_mat_get_fmpz_mat_rowwise"
  fmpq_mat_get_fmpz_mat_rowwise :: Ptr CFmpzMat -> Ptr CFmpz -> Ptr CFmpqMat -> IO ()

-- | /fmpq_mat_get_fmpz_mat_rowwise_2/ /num/ /num2/ /den/ /mat/ /mat2/ 
-- 
-- Clears denominators row by row of both @mat@ and @mat2@, writing the
-- respective numerators to @num@ and @num2@. This is equivalent to
-- concatenating @mat@ and @mat2@ horizontally, calling
-- @fmpq_mat_get_fmpz_mat_rowwise@, and extracting the two submatrices in
-- the result.
foreign import ccall "fmpq_mat.h fmpq_mat_get_fmpz_mat_rowwise_2"
  fmpq_mat_get_fmpz_mat_rowwise_2 :: Ptr CFmpzMat -> Ptr CFmpzMat -> Ptr CFmpz -> Ptr CFmpqMat -> Ptr CFmpqMat -> IO ()

-- | /fmpq_mat_get_fmpz_mat_colwise/ /num/ /den/ /mat/ 
-- 
-- Clears denominators in @mat@ column by column. The rescaled numerators
-- are written to @num@, and the denominator of column @i@ is written to
-- position @i@ in @den@ which can be a preinitialised @fmpz@ vector.
-- Alternatively, @NULL@ can be passed as the @den@ variable, in which case
-- the denominators will not be stored.
foreign import ccall "fmpq_mat.h fmpq_mat_get_fmpz_mat_colwise"
  fmpq_mat_get_fmpz_mat_colwise :: Ptr CFmpzMat -> Ptr CFmpz -> Ptr CFmpqMat -> IO ()

-- | /fmpq_mat_set_fmpz_mat/ /dest/ /src/ 
-- 
-- Sets @dest@ to @src@.
foreign import ccall "fmpq_mat.h fmpq_mat_set_fmpz_mat"
  fmpq_mat_set_fmpz_mat :: Ptr CFmpqMat -> Ptr CFmpzMat -> IO ()

-- | /fmpq_mat_set_fmpz_mat_div_fmpz/ /mat/ /num/ /den/ 
-- 
-- Sets @mat@ to the integer matrix @num@ divided by the common denominator
-- @den@.
foreign import ccall "fmpq_mat.h fmpq_mat_set_fmpz_mat_div_fmpz"
  fmpq_mat_set_fmpz_mat_div_fmpz :: Ptr CFmpqMat -> Ptr CFmpzMat -> Ptr CFmpz -> IO ()

-- Modular reduction and rational reconstruction -------------------------------

-- | /fmpq_mat_get_fmpz_mat_mod_fmpz/ /dest/ /mat/ /mod/ 
-- 
-- Sets each entry in @dest@ to the corresponding entry in @mat@, reduced
-- modulo @mod@.
foreign import ccall "fmpq_mat.h fmpq_mat_get_fmpz_mat_mod_fmpz"
  fmpq_mat_get_fmpz_mat_mod_fmpz :: Ptr CFmpzMat -> Ptr CFmpqMat -> Ptr CFmpz -> IO ()

-- | /fmpq_mat_set_fmpz_mat_mod_fmpz/ /X/ /Xmod/ /mod/ 
-- 
-- Set @X@ to the entrywise rational reconstruction integer matrix @Xmod@
-- modulo @mod@, and returns nonzero if the reconstruction is successful.
-- If rational reconstruction fails for any element, returns zero and sets
-- the entries in @X@ to undefined values.
foreign import ccall "fmpq_mat.h fmpq_mat_set_fmpz_mat_mod_fmpz"
  fmpq_mat_set_fmpz_mat_mod_fmpz :: Ptr CFmpqMat -> Ptr CFmpzMat -> Ptr CFmpz -> IO CInt

-- Matrix multiplication -------------------------------------------------------

-- | /fmpq_mat_mul_direct/ /C/ /A/ /B/ 
-- 
-- Sets @C@ to the matrix product @AB@, computed naively using rational
-- arithmetic. This is typically very slow and should only be used in
-- circumstances where clearing denominators would consume too much memory.
foreign import ccall "fmpq_mat.h fmpq_mat_mul_direct"
  fmpq_mat_mul_direct :: Ptr CFmpqMat -> Ptr CFmpqMat -> Ptr CFmpqMat -> IO ()

-- | /fmpq_mat_mul_cleared/ /C/ /A/ /B/ 
-- 
-- Sets @C@ to the matrix product @AB@, computed by clearing denominators
-- and multiplying over the integers.
foreign import ccall "fmpq_mat.h fmpq_mat_mul_cleared"
  fmpq_mat_mul_cleared :: Ptr CFmpqMat -> Ptr CFmpqMat -> Ptr CFmpqMat -> IO ()

-- | /fmpq_mat_mul/ /C/ /A/ /B/ 
-- 
-- Sets @C@ to the matrix product @AB@. This simply calls
-- @fmpq_mat_mul_cleared@.
foreign import ccall "fmpq_mat.h fmpq_mat_mul"
  fmpq_mat_mul :: Ptr CFmpqMat -> Ptr CFmpqMat -> Ptr CFmpqMat -> IO ()

-- | /fmpq_mat_mul_fmpz_mat/ /C/ /A/ /B/ 
-- 
-- Sets @C@ to the matrix product @AB@, with @B@ an integer matrix. This
-- function works efficiently by clearing denominators of @A@.
foreign import ccall "fmpq_mat.h fmpq_mat_mul_fmpz_mat"
  fmpq_mat_mul_fmpz_mat :: Ptr CFmpqMat -> Ptr CFmpqMat -> Ptr CFmpzMat -> IO ()

-- | /fmpq_mat_mul_r_fmpz_mat/ /C/ /A/ /B/ 
-- 
-- Sets @C@ to the matrix product @AB@, with @A@ an integer matrix. This
-- function works efficiently by clearing denominators of @B@.
foreign import ccall "fmpq_mat.h fmpq_mat_mul_r_fmpz_mat"
  fmpq_mat_mul_r_fmpz_mat :: Ptr CFmpqMat -> Ptr CFmpzMat -> Ptr CFmpqMat -> IO ()

-- | /fmpq_mat_mul_fmpq_vec/ /c/ /A/ /b/ /blen/ 
-- 
-- Compute a matrix-vector product of @A@ and @(b, blen)@ and store the
-- result in @c@. The vector @(b, blen)@ is either truncated or
-- zero-extended to the number of columns of @A@. The number entries
-- written to @c@ is always equal to the number of rows of @A@.
foreign import ccall "fmpq_mat.h fmpq_mat_mul_fmpq_vec"
  fmpq_mat_mul_fmpq_vec :: Ptr CFmpq -> Ptr CFmpqMat -> Ptr CFmpq -> CLong -> IO ()

-- | /fmpq_mat_fmpq_vec_mul/ /c/ /a/ /alen/ /B/ 
-- 
-- Compute a vector-matrix product of @(a, alen)@ and @B@ and and store the
-- result in @c@. The vector @(a, alen)@ is either truncated or
-- zero-extended to the number of rows of @B@. The number entries written
-- to @c@ is always equal to the number of columns of @B@.
foreign import ccall "fmpq_mat.h fmpq_mat_fmpq_vec_mul"
  fmpq_mat_fmpq_vec_mul :: Ptr CFmpq -> Ptr CFmpq -> CLong -> Ptr CFmpqMat -> IO ()

-- Kronecker product -----------------------------------------------------------

-- | /fmpq_mat_kronecker_product/ /C/ /A/ /B/ 
-- 
-- Sets @C@ to the Kronecker product of @A@ and @B@.
foreign import ccall "fmpq_mat.h fmpq_mat_kronecker_product"
  fmpq_mat_kronecker_product :: Ptr CFmpqMat -> Ptr CFmpqMat -> Ptr CFmpqMat -> IO ()

-- Trace -----------------------------------------------------------------------

-- | /fmpq_mat_trace/ /trace/ /mat/ 
-- 
-- Computes the trace of the matrix, i.e. the sum of the entries on the
-- main diagonal. The matrix is required to be square.
foreign import ccall "fmpq_mat.h fmpq_mat_trace"
  fmpq_mat_trace :: Ptr CFmpq -> Ptr CFmpqMat -> IO ()

-- Determinant -----------------------------------------------------------------

-- | /fmpq_mat_det/ /det/ /mat/ 
-- 
-- Sets @det@ to the determinant of @mat@. In the general case, the
-- determinant is computed by clearing denominators and computing a
-- determinant over the integers. Matrices of size 0, 1 or 2 are handled
-- directly.
foreign import ccall "fmpq_mat.h fmpq_mat_det"
  fmpq_mat_det :: Ptr CFmpq -> Ptr CFmpqMat -> IO ()

-- Nonsingular solving ---------------------------------------------------------

-- | /fmpq_mat_solve_fraction_free/ /X/ /A/ /B/ 
-- 
-- Solves @AX = B@ for nonsingular @A@. Returns nonzero if @A@ is
-- nonsingular or if the right hand side is empty, and zero otherwise.
-- 
-- All algorithms clear denominators to obtain a rescaled system over the
-- integers. The /fraction_free/ algorithm uses FFLU solving over the
-- integers. The /dixon/ and /multi_mod/ algorithms use Dixon p-adic
-- lifting or multimodular solving, followed by rational reconstruction
-- with an adaptive stopping test. The /dixon/ and /multi_mod/ algorithms
-- are generally the best choice for large systems.
-- 
-- The default method chooses an algorithm automatically.
foreign import ccall "fmpq_mat.h fmpq_mat_solve_fraction_free"
  fmpq_mat_solve_fraction_free :: Ptr CFmpqMat -> Ptr CFmpqMat -> Ptr CFmpqMat -> IO CInt

-- | /fmpq_mat_solve_fmpz_mat_fraction_free/ /X/ /A/ /B/ 
-- 
-- Solves @AX = B@ for nonsingular @A@, where /A/ and /B/ are integer
-- matrices. Returns nonzero if @A@ is nonsingular or if the right hand
-- side is empty, and zero otherwise.
foreign import ccall "fmpq_mat.h fmpq_mat_solve_fmpz_mat_fraction_free"
  fmpq_mat_solve_fmpz_mat_fraction_free :: Ptr CFmpqMat -> Ptr CFmpzMat -> Ptr CFmpzMat -> IO CInt

-- | /fmpq_mat_can_solve_multi_mod/ /X/ /A/ /B/ 
-- 
-- Returns \(1\) if @AX = B@ has a solution and if so, sets @X@ to one such
-- solution. The matrices can have any shape but must have the same number
-- of rows.
foreign import ccall "fmpq_mat.h fmpq_mat_can_solve_multi_mod"
  fmpq_mat_can_solve_multi_mod :: Ptr CFmpqMat -> Ptr CFmpqMat -> Ptr CFmpqMat -> IO CInt

-- | /fmpq_mat_can_solve_fraction_free/ /X/ /A/ /B/ 
-- 
-- Returns \(1\) if @AX = B@ has a solution and if so, sets @X@ to one such
-- solution. The matrices can have any shape but must have the same number
-- of rows.
foreign import ccall "fmpq_mat.h fmpq_mat_can_solve_fraction_free"
  fmpq_mat_can_solve_fraction_free :: Ptr CFmpqMat -> Ptr CFmpqMat -> Ptr CFmpqMat -> IO CInt

-- | /fmpq_mat_can_solve/ /X/ /A/ /B/ 
-- 
-- Returns \(1\) if @AX = B@ has a solution and if so, sets @X@ to one such
-- solution. The matrices can have any shape but must have the same number
-- of rows.
foreign import ccall "fmpq_mat.h fmpq_mat_can_solve"
  fmpq_mat_can_solve :: Ptr CFmpqMat -> Ptr CFmpqMat -> Ptr CFmpqMat -> IO CInt

-- Inverse ---------------------------------------------------------------------

-- | /fmpq_mat_inv/ /B/ /A/ 
-- 
-- Sets @B@ to the inverse matrix of @A@ and returns nonzero. Returns zero
-- if @A@ is singular. @A@ must be a square matrix.
foreign import ccall "fmpq_mat.h fmpq_mat_inv"
  fmpq_mat_inv :: Ptr CFmpqMat -> Ptr CFmpqMat -> IO CInt

-- Echelon form ----------------------------------------------------------------

-- | /fmpq_mat_pivot/ /perm/ /mat/ /r/ /c/ 
-- 
-- Helper function for row reduction. Returns 1 if the entry of @mat@ at
-- row \(r\) and column \(c\) is nonzero. Otherwise searches for a nonzero
-- entry in the same column among rows \(r+1, r+2, \ldots\). If a nonzero
-- entry is found at row \(s\), swaps rows \(r\) and \(s\) and the
-- corresponding entries in @perm@ (unless @NULL@) and returns -1. If no
-- nonzero pivot entry is found, leaves the inputs unchanged and returns 0.
foreign import ccall "fmpq_mat.h fmpq_mat_pivot"
  fmpq_mat_pivot :: Ptr CLong -> Ptr CFmpqMat -> CLong -> CLong -> IO CInt

-- | /fmpq_mat_rref_classical/ /B/ /A/ 
-- 
-- Sets @B@ to the reduced row echelon form of @A@ and returns the rank.
-- Performs Gauss-Jordan elimination directly over the rational numbers.
-- This algorithm is usually inefficient and is mainly intended to be used
-- for testing purposes.
foreign import ccall "fmpq_mat.h fmpq_mat_rref_classical"
  fmpq_mat_rref_classical :: Ptr CFmpqMat -> Ptr CFmpqMat -> IO CLong

-- | /fmpq_mat_rref_fraction_free/ /B/ /A/ 
-- 
-- Sets @B@ to the reduced row echelon form of @A@ and returns the rank.
-- Clears denominators and performs fraction-free Gauss-Jordan elimination
-- using @fmpz_mat@ functions.
foreign import ccall "fmpq_mat.h fmpq_mat_rref_fraction_free"
  fmpq_mat_rref_fraction_free :: Ptr CFmpqMat -> Ptr CFmpqMat -> IO CLong

-- | /fmpq_mat_rref/ /B/ /A/ 
-- 
-- Sets @B@ to the reduced row echelon form of @A@ and returns the rank.
-- This function automatically chooses between the classical and
-- fraction-free algorithms depending on the size of the matrix.
foreign import ccall "fmpq_mat.h fmpq_mat_rref"
  fmpq_mat_rref :: Ptr CFmpqMat -> Ptr CFmpqMat -> IO CLong

-- Gram-Schmidt Orthogonalisation ----------------------------------------------

-- | /fmpq_mat_gso/ /B/ /A/ 
-- 
-- Takes a subset of \(\mathbb{Q}^m\) \(S = \{a_1, a_2, \ldots ,a_n\}\) (as
-- the columns of a \(m \times n\) matrix @A@) and generates an orthogonal
-- set \(S' = \{b_1, b_2, \ldots ,b_n\}\) (as the columns of the
-- \(m \times n\) matrix @B@) that spans the same subspace of
-- \(\mathbb{Q}^m\) as \(S\).
foreign import ccall "fmpq_mat.h fmpq_mat_gso"
  fmpq_mat_gso :: Ptr CFmpqMat -> Ptr CFmpqMat -> IO ()

-- Transforms ------------------------------------------------------------------

-- | /fmpq_mat_similarity/ /A/ /r/ /d/ 
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
foreign import ccall "fmpq_mat.h fmpq_mat_similarity"
  fmpq_mat_similarity :: Ptr CFmpqMat -> CLong -> Ptr CFmpq -> IO ()

-- Characteristic polynomial ---------------------------------------------------

-- | /_fmpq_mat_charpoly/ /coeffs/ /den/ /mat/ 
-- 
-- Set @(coeffs, den)@ to the characteristic polynomial of the given
-- \(n\times n\) matrix.
foreign import ccall "fmpq_mat.h _fmpq_mat_charpoly"
  _fmpq_mat_charpoly :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpqMat -> IO ()

-- | /fmpq_mat_charpoly/ /pol/ /mat/ 
-- 
-- Set @pol@ to the characteristic polynomial of the given \(n\times n\)
-- matrix. If @mat@ is not square, an exception is raised.
foreign import ccall "fmpq_mat.h fmpq_mat_charpoly"
  fmpq_mat_charpoly :: Ptr CFmpqPoly -> Ptr CFmpqMat -> IO ()

-- Minimal polynomial ----------------------------------------------------------

-- | /_fmpq_mat_minpoly/ /coeffs/ /den/ /mat/ 
-- 
-- Set @(coeffs, den)@ to the minimal polynomial of the given \(n\times n\)
-- matrix and return the length of the polynomial.
foreign import ccall "fmpq_mat.h _fmpq_mat_minpoly"
  _fmpq_mat_minpoly :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpqMat -> IO CLong

-- | /fmpq_mat_minpoly/ /pol/ /mat/ 
-- 
-- Set @pol@ to the minimal polynomial of the given \(n\times n\) matrix.
-- If @mat@ is not square, an exception is raised.
foreign import ccall "fmpq_mat.h fmpq_mat_minpoly"
  fmpq_mat_minpoly :: Ptr CFmpqPoly -> Ptr CFmpqMat -> IO ()

