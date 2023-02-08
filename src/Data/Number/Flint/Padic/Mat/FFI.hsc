{-# language
  CApiFFI
, FlexibleInstances
, ForeignFunctionInterface
, MultiParamTypeClasses
, TupleSections
, TypeFamilies
#-}

module Data.Number.Flint.Padic.Mat.FFI (
  -- * Matrices over p-adic numbers
    PadicMat (..)
  , CPadicMat (..)
  , newPadicMat
  , withPadicMat
  -- * Macros
  , padic_mat
  , padic_mat_entry
  -- , padic_mat_val
  -- , padic_mat_prec
  , padic_mat_get_val
  , padic_mat_get_prec
  , padic_mat_nrows
  , padic_mat_ncols
  -- * Memory management
  , padic_mat_init
  , padic_mat_init2
  , padic_mat_clear
  , _padic_mat_canonicalise
  , _padic_mat_reduce
  , padic_mat_reduce
  , padic_mat_is_empty
  , padic_mat_is_square
  , padic_mat_is_canonical
  -- * Basic assignment
  , padic_mat_set
  , padic_mat_swap
  , padic_mat_swap_entrywise
  , padic_mat_zero
  , padic_mat_one
  -- * Conversions
  , padic_mat_set_fmpq_mat
  , padic_mat_get_fmpq_mat
  -- * Entries
  , padic_mat_get_entry_padic
  , padic_mat_set_entry_padic
  -- * Comparison
  , padic_mat_equal
  , padic_mat_is_zero
  -- * Input and output
  , padic_mat_get_str
  , padic_mat_get_str_pretty
  , padic_mat_fprint
  , padic_mat_fprint_pretty
  , padic_mat_print
  , padic_mat_print_pretty
  -- * Random matrix generation
  , padic_mat_randtest
  -- * Transpose
  , padic_mat_transpose
  -- * Addition and subtraction
  , _padic_mat_add
  , padic_mat_add
  , _padic_mat_sub
  , padic_mat_sub
  , _padic_mat_neg
  , padic_mat_neg
  -- * Scalar operations
  , _padic_mat_scalar_mul_padic
  , padic_mat_scalar_mul_padic
  , _padic_mat_scalar_mul_fmpz
  , padic_mat_scalar_mul_fmpz
  , padic_mat_scalar_div_fmpz
  -- * Multiplication
  , padic_mat_mul
) where 

-- matrices over p-adic numbers ------------------------------------------------

import Control.Monad

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr, castPtr )
import Foreign.Storable
import Foreign.Marshal ( free )

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Mat
import Data.Number.Flint.Fmpq.Mat
import Data.Number.Flint.Padic

#include <flint/flint.h>
#include <flint/padic.h>
#include <flint/padic_mat.h>

-- padic_mat_t -----------------------------------------------------------------

data PadicMat = PadicMat {-# UNPACK #-} !(ForeignPtr CPadicMat)
data CPadicMat = CPadicMat CFmpzMat CLong CLong

instance Storable CPadicMat where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size padic_mat_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment padic_mat_t}
  peek ptr = return CPadicMat
    `ap` #{peek padic_mat_struct, mat} ptr
    `ap` #{peek padic_mat_struct, val} ptr
    `ap` #{peek padic_mat_struct, N  } ptr
  poke = undefined

newPadicMat rows cols prec = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> padic_mat_init x rows cols prec
  addForeignPtrFinalizer p_padic_mat_clear x
  return $ PadicMat x

{-# INLINE withPadicMat #-}
withPadicMat (PadicMat x) f = do
  withForeignPtr x $ \px -> f px >>= return . (PadicMat x,)

-- Module documentation --------------------------------------------------------

-- We represent a matrix over \(\mathbf{Q}_p\) as a product \(p^v M\),
-- where \(p\) is a prime number, \(v \in \mathbf{Z}\) and \(M\) a matrix
-- over \(\mathbf{Z}\). We say this matrix is in /canonical form/ if either
-- \(M\) is zero, in which case we choose \(v = 0\), too, or if \(M\)
-- contains at least one p-adic unit. We say this matrix is /reduced/
-- modulo \(p^N\) if it is canonical form and if all coefficients of \(M\)
-- lie in the range \([0, p^{N-v})\).
--

-- | /padic_mat/ /A/ 
-- 
-- Returns a pointer to the unit part of the matrix, which is a matrix over
-- \(\mathbf{Z}\).
-- 
-- The return value can be used as an argument to the functions in the
-- @fmpz_mat@ module.
padic_mat :: Ptr CPadicMat -> IO (Ptr CFmpzMat)
padic_mat ptr = return $ castPtr ptr
  
-- | /padic_mat_entry/ /A/ /i/ /j/ 
-- 
-- Returns a pointer to unit part of the entry in position \((i, j)\). Note
-- that this is not necessarily a unit.
-- 
-- The return value can be used as an argument to the functions in the
-- @fmpz@ module.
foreign import ccall "padic_mat.h padic_mat_entry"
  padic_mat_entry :: Ptr CPadicMat -> CLong -> CLong -> IO (Ptr CFmpz)

-- | /padic_mat_get_val/ /A/ 
-- 
-- Returns the valuation of the matrix.
foreign import ccall "padic_mat.h padic_mat_get_val"
  padic_mat_get_val :: Ptr CPadicMat -> IO CLong

-- | /padic_mat_get_prec/ /A/ 
-- 
-- Returns the \(p\)-adic precision of the matrix.
foreign import ccall "padic_mat.h padic_mat_get_prec"
  padic_mat_get_prec :: Ptr CPadicMat -> IO CLong

-- | /padic_mat_nrows/ /A/ 
-- 
-- Returns the number of rows of the matrix \(A\).
foreign import ccall "padic_mat.h padic_mat_nrows"
  padic_mat_nrows :: Ptr CPadicMat -> IO CLong

-- | /padic_mat_ncols/ /A/ 
-- 
-- Returns the number of columns of the matrix \(A\).
foreign import ccall "padic_mat.h padic_mat_ncols"
  padic_mat_ncols :: Ptr CPadicMat -> IO CLong

-- Memory management -----------------------------------------------------------

-- | /padic_mat_init/ /A/ /r/ /c/ 
-- 
-- Initialises the matrix \(A\) as a zero matrix with the specified numbers
-- of rows and columns and precision @PADIC_DEFAULT_PREC@.
foreign import ccall "padic_mat.h padic_mat_init"
  padic_mat_init :: Ptr CPadicMat -> CLong -> CLong -> CLong -> IO ()

-- | /padic_mat_init2/ /A/ /r/ /c/ /prec/ 
-- 
-- Initialises the matrix \(A\) as a zero matrix with the specified numbers
-- of rows and columns and the given precision.
foreign import ccall "padic_mat.h padic_mat_init2"
  padic_mat_init2 :: Ptr CPadicMat -> CLong -> CLong -> CLong -> IO ()

-- | /padic_mat_clear/ /A/ 
-- 
-- Clears the matrix \(A\).
foreign import ccall "padic_mat.h padic_mat_clear"
  padic_mat_clear :: Ptr CPadicMat -> IO ()

foreign import ccall "padic_mat.h &padic_mat_clear"
  p_padic_mat_clear :: FunPtr (Ptr CPadicMat -> IO ())

-- | /_padic_mat_canonicalise/ /A/ /ctx/ 
-- 
-- Ensures that the matrix \(A\) is in canonical form.
foreign import ccall "padic_mat.h _padic_mat_canonicalise"
  _padic_mat_canonicalise :: Ptr CPadicMat -> Ptr CPadicCtx -> IO ()

-- | /_padic_mat_reduce/ /A/ /ctx/ 
-- 
-- Ensures that the matrix \(A\) is reduced modulo \(p^N\), assuming that
-- it is in canonical form already.
foreign import ccall "padic_mat.h _padic_mat_reduce"
  _padic_mat_reduce :: Ptr CPadicMat -> Ptr CPadicCtx -> IO ()

-- | /padic_mat_reduce/ /A/ /ctx/ 
-- 
-- Ensures that the matrix \(A\) is reduced modulo \(p^N\), without
-- assuming that it is necessarily in canonical form.
foreign import ccall "padic_mat.h padic_mat_reduce"
  padic_mat_reduce :: Ptr CPadicMat -> Ptr CPadicCtx -> IO ()

-- | /padic_mat_is_empty/ /A/ 
-- 
-- Returns whether the matrix \(A\) is empty, that is, whether it has zero
-- rows or zero columns.
foreign import ccall "padic_mat.h padic_mat_is_empty"
  padic_mat_is_empty :: Ptr CPadicMat -> IO CInt

-- | /padic_mat_is_square/ /A/ 
-- 
-- Returns whether the matrix \(A\) is square.
foreign import ccall "padic_mat.h padic_mat_is_square"
  padic_mat_is_square :: Ptr CPadicMat -> IO CInt

-- | /padic_mat_is_canonical/ /A/ /p/ 
-- 
-- Returns whether the matrix \(A\) is in canonical form.
foreign import ccall "padic_mat.h padic_mat_is_canonical"
  padic_mat_is_canonical :: Ptr CPadicMat -> Ptr CFmpz -> IO CInt

-- Basic assignment ------------------------------------------------------------

-- | /padic_mat_set/ /B/ /A/ 
-- 
-- Sets \(B\) to a copy of \(A\), respecting the precision of \(B\).
foreign import ccall "padic_mat.h padic_mat_set"
  padic_mat_set :: Ptr CPadicMat -> Ptr CPadicMat -> IO ()

-- | /padic_mat_swap/ /A/ /B/ 
-- 
-- Swaps the two matrices \(A\) and \(B\). This is done efficiently by
-- swapping pointers.
foreign import ccall "padic_mat.h padic_mat_swap"
  padic_mat_swap :: Ptr CPadicMat -> Ptr CPadicMat -> IO ()

-- | /padic_mat_swap_entrywise/ /mat1/ /mat2/ 
-- 
-- Swaps two matrices by swapping the individual entries rather than
-- swapping the contents of the structs.
foreign import ccall "padic_mat.h padic_mat_swap_entrywise"
  padic_mat_swap_entrywise :: Ptr CPadicMat -> Ptr CPadicMat -> IO ()

-- | /padic_mat_zero/ /A/ 
-- 
-- Sets the matrix \(A\) to zero.
foreign import ccall "padic_mat.h padic_mat_zero"
  padic_mat_zero :: Ptr CPadicMat -> IO ()

-- | /padic_mat_one/ /A/ 
-- 
-- Sets the matrix \(A\) to the identity matrix. If the precision is
-- negative then the matrix will be the zero matrix.
foreign import ccall "padic_mat.h padic_mat_one"
  padic_mat_one :: Ptr CPadicMat -> IO ()

-- Conversions -----------------------------------------------------------------

-- | /padic_mat_set_fmpq_mat/ /B/ /A/ /ctx/ 
-- 
-- Sets the \(p\)-adic matrix \(B\) to the rational matrix \(A\), reduced
-- according to the given context.
foreign import ccall "padic_mat.h padic_mat_set_fmpq_mat"
  padic_mat_set_fmpq_mat :: Ptr CPadicMat -> Ptr CFmpqMat -> Ptr CPadicCtx -> IO ()

-- | /padic_mat_get_fmpq_mat/ /B/ /A/ /ctx/ 
-- 
-- Sets the rational matrix \(B\) to the \(p\)-adic matrices \(A\); no
-- reduction takes place.
foreign import ccall "padic_mat.h padic_mat_get_fmpq_mat"
  padic_mat_get_fmpq_mat :: Ptr CFmpqMat -> Ptr CPadicMat -> Ptr CPadicCtx -> IO ()

-- Entries ---------------------------------------------------------------------

-- Because of the choice of the data structure, representing the matrix as
-- \(p^v M\), setting an entry of the matrix might lead to changes in all
-- entries in the matrix \(M\). Also, a specific entry is not readily
-- available as a \(p\)-adic number. Thus, there are separate functions
-- available for getting and setting entries.
--
-- | /padic_mat_get_entry_padic/ /rop/ /op/ /i/ /j/ /ctx/ 
-- 
-- Sets @rop@ to the entry in position \((i, j)\) in the matrix @op@.
foreign import ccall "padic_mat.h padic_mat_get_entry_padic"
  padic_mat_get_entry_padic :: Ptr CPadic -> Ptr CPadicMat -> CLong -> CLong -> Ptr CPadicCtx -> IO ()

-- | /padic_mat_set_entry_padic/ /rop/ /i/ /j/ /op/ /ctx/ 
-- 
-- Sets the entry in position \((i, j)\) in the matrix to @rop@.
foreign import ccall "padic_mat.h padic_mat_set_entry_padic"
  padic_mat_set_entry_padic :: Ptr CPadicMat -> CLong -> CLong -> Ptr CPadic -> Ptr CPadicCtx -> IO ()

-- Comparison ------------------------------------------------------------------

-- | /padic_mat_equal/ /A/ /B/ 
-- 
-- Returns whether the two matrices \(A\) and \(B\) are equal.
foreign import ccall "padic_mat.h padic_mat_equal"
  padic_mat_equal :: Ptr CPadicMat -> Ptr CPadicMat -> IO CInt

-- | /padic_mat_is_zero/ /A/ 
-- 
-- Returns whether the matrix \(A\) is zero.
foreign import ccall "padic_mat.h padic_mat_is_zero"
  padic_mat_is_zero :: Ptr CPadicMat -> IO CInt

-- Input and output ------------------------------------------------------------

foreign import ccall "padic_mat.h padic_mat_get_str"
  padic_mat_get_str:: Ptr CPadicMat -> Ptr CPadicCtx -> IO CString
  
foreign import ccall "padic_mat.h padic_mat_get_str_pretty"
  padic_mat_get_str_pretty:: Ptr CPadicMat -> Ptr CPadicCtx -> IO CString
  
-- | /padic_mat_fprint/ /file/ /A/ /ctx/ 
-- 
-- Prints a simple representation of the matrix \(A\) to the output stream
-- @file@. The format is the number of rows, a space, the number of
-- columns, two spaces, followed by a list of all the entries, one row
-- after the other.
-- 
-- In the current implementation, always returns \(1\).
foreign import ccall "padic_mat.h padic_mat_fprint"
  padic_mat_fprint :: Ptr CFile -> Ptr CPadicMat -> Ptr CPadicCtx -> IO CInt

-- | /padic_mat_fprint_pretty/ /file/ /A/ /ctx/ 
-- 
-- Prints a /pretty/ representation of the matrix \(A\) to the output
-- stream @file@.
-- 
-- In the current implementation, always returns \(1\).
foreign import ccall "padic_mat.h padic_mat_fprint_pretty"
  padic_mat_fprint_pretty :: Ptr CFile -> Ptr CPadicMat -> Ptr CPadicCtx -> IO CInt

-- | /padic_mat_print/ /file/ /A/ /ctx/ 
-- 
-- Prints a simple representation of the matrix \(A\) to @stdout@. The
-- format is the number of rows, a space, the number of columns, two
-- spaces, followed by a list of all the entries, one row after the
-- other.
-- 
-- In the current implementation, always returns \(1\).
padic_mat_print :: Ptr CPadicMat -> Ptr CPadicCtx -> IO CInt
padic_mat_print mat ctx = printCStr (flip padic_mat_get_str ctx) mat

-- | /padic_mat_print_pretty/ /file/ /A/ /ctx/ 
-- 
-- Prints a /pretty/ representation of the matrix \(A\) to @stdout@.
-- 
-- In the current implementation, always returns \(1\).
padic_mat_print_pretty :: Ptr CPadicMat -> Ptr CPadicCtx -> IO CInt
padic_mat_print_pretty mat ctx = printCStr (flip padic_mat_get_str_pretty ctx) mat

-- Random matrix generation ----------------------------------------------------

-- | /padic_mat_randtest/ /A/ /state/ /ctx/ 
-- 
-- Sets \(A\) to a random matrix.
-- 
-- The valuation will be in the range \([- \lceil N/10\rceil, N)\),
-- \([N - \lceil -N/10\rceil, N)\), or \([-10, 0)\) as \(N\) is positive,
-- negative or zero.
foreign import ccall "padic_mat.h padic_mat_randtest"
  padic_mat_randtest :: Ptr CPadicMat -> Ptr CFRandState -> Ptr CPadicCtx -> IO ()

-- Transpose -------------------------------------------------------------------

-- | /padic_mat_transpose/ /B/ /A/ 
-- 
-- Sets \(B\) to \(A^t\).
foreign import ccall "padic_mat.h padic_mat_transpose"
  padic_mat_transpose :: Ptr CPadicMat -> Ptr CPadicMat -> IO ()

-- Addition and subtraction ----------------------------------------------------

-- | /_padic_mat_add/ /C/ /A/ /B/ /ctx/ 
-- 
-- Sets \(C\) to the exact sum \(A + B\), ensuring that the result is in
-- canonical form.
foreign import ccall "padic_mat.h _padic_mat_add"
  _padic_mat_add :: Ptr CPadicMat -> Ptr CPadicMat -> Ptr CPadicMat -> Ptr CPadicCtx -> IO ()

-- | /padic_mat_add/ /C/ /A/ /B/ /ctx/ 
-- 
-- Sets \(C\) to the sum \(A + B\) modulo \(p^N\).
foreign import ccall "padic_mat.h padic_mat_add"
  padic_mat_add :: Ptr CPadicMat -> Ptr CPadicMat -> Ptr CPadicMat -> Ptr CPadicCtx -> IO ()

-- | /_padic_mat_sub/ /C/ /A/ /B/ /ctx/ 
-- 
-- Sets \(C\) to the exact difference \(A - B\), ensuring that the result
-- is in canonical form.
foreign import ccall "padic_mat.h _padic_mat_sub"
  _padic_mat_sub :: Ptr CPadicMat -> Ptr CPadicMat -> Ptr CPadicMat -> Ptr CPadicCtx -> IO ()

-- | /padic_mat_sub/ /C/ /A/ /B/ /ctx/ 
-- 
-- Sets \(C\) to \(A - B\), ensuring that the result is reduced.
foreign import ccall "padic_mat.h padic_mat_sub"
  padic_mat_sub :: Ptr CPadicMat -> Ptr CPadicMat -> Ptr CPadicMat -> Ptr CPadicCtx -> IO ()

-- | /_padic_mat_neg/ /B/ /A/ 
-- 
-- Sets \(B\) to \(-A\) in canonical form.
foreign import ccall "padic_mat.h _padic_mat_neg"
  _padic_mat_neg :: Ptr CPadicMat -> Ptr CPadicMat -> IO ()

-- | /padic_mat_neg/ /B/ /A/ /ctx/ 
-- 
-- Sets \(B\) to \(-A\), ensuring the result is reduced.
foreign import ccall "padic_mat.h padic_mat_neg"
  padic_mat_neg :: Ptr CPadicMat -> Ptr CPadicMat -> Ptr CPadicCtx -> IO ()

-- Scalar operations -----------------------------------------------------------

-- | /_padic_mat_scalar_mul_padic/ /B/ /A/ /c/ /ctx/ 
-- 
-- Sets \(B\) to \(c A\), ensuring that the result is in canonical form.
foreign import ccall "padic_mat.h _padic_mat_scalar_mul_padic"
  _padic_mat_scalar_mul_padic :: Ptr CPadicMat -> Ptr CPadicMat -> Ptr CPadic -> Ptr CPadicCtx -> IO ()

-- | /padic_mat_scalar_mul_padic/ /B/ /A/ /c/ /ctx/ 
-- 
-- Sets \(B\) to \(c A\), ensuring that the result is reduced.
foreign import ccall "padic_mat.h padic_mat_scalar_mul_padic"
  padic_mat_scalar_mul_padic :: Ptr CPadicMat -> Ptr CPadicMat -> Ptr CPadic -> Ptr CPadicCtx -> IO ()

-- | /_padic_mat_scalar_mul_fmpz/ /B/ /A/ /c/ /ctx/ 
-- 
-- Sets \(B\) to \(c A\), ensuring that the result is in canonical form.
foreign import ccall "padic_mat.h _padic_mat_scalar_mul_fmpz"
  _padic_mat_scalar_mul_fmpz :: Ptr CPadicMat -> Ptr CPadicMat -> Ptr CFmpz -> Ptr CPadicCtx -> IO ()

-- | /padic_mat_scalar_mul_fmpz/ /B/ /A/ /c/ /ctx/ 
-- 
-- Sets \(B\) to \(c A\), ensuring that the result is reduced.
foreign import ccall "padic_mat.h padic_mat_scalar_mul_fmpz"
  padic_mat_scalar_mul_fmpz :: Ptr CPadicMat -> Ptr CPadicMat -> Ptr CFmpz -> Ptr CPadicCtx -> IO ()

-- | /padic_mat_scalar_div_fmpz/ /B/ /A/ /c/ /ctx/ 
-- 
-- Sets \(B\) to \(c^{-1} A\), assuming that \(c \neq 0\). Ensures that the
-- result \(B\) is reduced.
foreign import ccall "padic_mat.h padic_mat_scalar_div_fmpz"
  padic_mat_scalar_div_fmpz :: Ptr CPadicMat -> Ptr CPadicMat -> Ptr CFmpz -> Ptr CPadicCtx -> IO ()

-- Multiplication --------------------------------------------------------------

-- | /padic_mat_mul/ /C/ /A/ /B/ /ctx/ 
-- 
-- Sets \(C\) to the product \(A B\) of the two matrices \(A\) and \(B\),
-- ensuring that \(C\) is reduced.
foreign import ccall "padic_mat.h padic_mat_mul"
  padic_mat_mul :: Ptr CPadicMat -> Ptr CPadicMat -> Ptr CPadicMat -> Ptr CPadicCtx -> IO ()

