module Data.Number.Flint.Calcium.Fexpr.FFI (
  -- * Flat-packed symbolic expressions
  -- * Introduction
  -- * Computing and embedding data
  -- * Flat-packed representation
  -- * Memory management
    Fexpr (..)
  , CFexpr ()
  , newFexpr
  , withFexpr
  , withNewFexpr
  , fexpr_init
  , fexpr_clear
  , _fexpr_vec_init
  , _fexpr_vec_clear
  , fexpr_fit_size
  , fexpr_set
  , fexpr_swap
  -- * Types
  , fexpr_type_small_int
  , fexpr_type_small_symbol
  , fexpr_type_small_string
  , fexpr_type_big_int_pos
  , fexpr_type_big_int_neg
  , fexpr_type_big_symbol
  , fexpr_type_big_string
  , fexpr_type_call0
  , fexpr_type_call1
  , fexpr_type_call2
  , fexpr_type_call3
  , fexpr_type_call4
  , fexpr_type_calln
  -- * Size information
  , fexpr_depth
  , fexpr_num_leaves
  , fexpr_size
  , fexpr_size_bytes
  , fexpr_allocated_bytes
  -- * Comparisons
  , fexpr_equal
  , fexpr_equal_si
  , fexpr_equal_ui
  , fexpr_hash
  , fexpr_cmp_fast
  -- * Atoms
  , fexpr_is_integer
  , fexpr_is_symbol
  , fexpr_is_string
  , fexpr_is_atom
  , fexpr_zero
  , fexpr_is_zero
  , fexpr_is_neg_integer
  , fexpr_set_si
  , fexpr_set_ui
  , fexpr_set_fmpz
  , fexpr_get_fmpz
  , fexpr_set_symbol_builtin
  , fexpr_is_builtin_symbol
  , fexpr_is_any_builtin_symbol
  , fexpr_set_symbol_str
  , fexpr_get_symbol_str
  , fexpr_set_string
  , fexpr_get_string
  -- * Input and output
  , fexpr_write
  , fexpr_print
  , fexpr_get_str
  -- * LaTeX output
  , fexpr_write_latex
  , fexpr_print_latex
  , fexpr_get_str_latex
  -- | The /flags/ parameter allows specifying options for LaTeX
  -- output. The following flags are supported:
  , fexpr_latex_small
  , fexpr_latex_logic 
  -- * Function call structure
  , fexpr_nargs
  , fexpr_func
  , fexpr_view_func
  , fexpr_arg
  , fexpr_view_arg
  , fexpr_view_next
  , fexpr_is_builtin_call
  , fexpr_is_any_builtin_call
  -- * Composition
  , fexpr_call0
  , fexpr_call1
  , fexpr_call2
  , fexpr_call3
  , fexpr_call4
  , fexpr_call_vec
  , fexpr_call_builtin1
  , fexpr_call_builtin2
  -- * Subexpressions and replacement
  , fexpr_contains
  , fexpr_replace
  , fexpr_replace2
  , fexpr_replace_vec
  -- * Arithmetic expressions
  , fexpr_set_fmpq
  , fexpr_set_arf
  , fexpr_set_d
  , fexpr_set_re_im_d
  , fexpr_neg
  , fexpr_add
  , fexpr_sub
  , fexpr_mul
  , fexpr_div
  , fexpr_pow
  , fexpr_is_arithmetic_operation
  , fexpr_arithmetic_nodes
  , fexpr_get_fmpz_mpoly_q
  , fexpr_set_fmpz_mpoly
  , fexpr_set_fmpz_mpoly_q
  , fexpr_expanded_normal_form
  -- * Vectors
  , newFexprVec
  , withFexprVec
  , withNewFexprVec
  , fexpr_vec_init
  , fexpr_vec_clear
  , fexpr_vec_print
  , fexpr_vec_swap
  , fexpr_vec_fit_length
  , fexpr_vec_set
  , fexpr_vec_append
  , fexpr_vec_insert_unique
  , fexpr_vec_set_length
  , _fexpr_vec_sort_fast
) where 

-- Flat-packed symbolic expressions --------------------------------------------

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.C.Types
import Foreign.C.String
import Foreign.Storable

import Data.Word
import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.MPoly
import Data.Number.Flint.Fmpz.MPoly.Q
import Data.Number.Flint.Fmpq
import Data.Number.Flint.Arb.Types
import Data.Number.Flint.Calcium

#include <flint/fexpr.h>

-- fexpr_t ---------------------------------------------------------------------

data Fexpr = Fexpr {-# UNPACK #-} !(ForeignPtr CFexpr)
data CFexpr = CFexpr (Ptr CULong) CLong

instance Storable CFexpr where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fexpr_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fexpr_t}
  peek ptr = CFexpr
    <$> #{peek fexpr_struct, data } ptr
    <*> #{peek fexpr_struct, alloc} ptr
  poke ptr (CFexpr d a) = do
    #{poke fexpr_struct, data } ptr d
    #{poke fexpr_struct, alloc} ptr a

newFexpr = do
  p <- mallocForeignPtr
  withForeignPtr p fexpr_init
  addForeignPtrFinalizer p_fexpr_clear p
  return $ Fexpr p

withFexpr (Fexpr p) f = do
  withForeignPtr p $ \fp -> (Fexpr p,) <$> f fp

withNewFexpr f = do
  x <- newFexpr
  withFexpr x f

type FexprType = CULong

fexpr_type_small_int    =  (#const FEXPR_TYPE_SMALL_INT   ) :: FexprType
fexpr_type_small_symbol =  (#const FEXPR_TYPE_SMALL_SYMBOL) :: FexprType
fexpr_type_small_string =  (#const FEXPR_TYPE_SMALL_STRING) :: FexprType
fexpr_type_big_int_pos  =  (#const FEXPR_TYPE_BIG_INT_POS ) :: FexprType
fexpr_type_big_int_neg  =  (#const FEXPR_TYPE_BIG_INT_NEG ) :: FexprType
fexpr_type_big_symbol   =  (#const FEXPR_TYPE_BIG_SYMBOL  ) :: FexprType
fexpr_type_big_string   =  (#const FEXPR_TYPE_BIG_STRING  ) :: FexprType
fexpr_type_call0        =  (#const FEXPR_TYPE_CALL0 	  ) :: FexprType
fexpr_type_call1        =  (#const FEXPR_TYPE_CALL1 	  ) :: FexprType
fexpr_type_call2        =  (#const FEXPR_TYPE_CALL2 	  ) :: FexprType
fexpr_type_call3        =  (#const FEXPR_TYPE_CALL3 	  ) :: FexprType
fexpr_type_call4        =  (#const FEXPR_TYPE_CALL4 	  ) :: FexprType
fexpr_type_calln        =  (#const FEXPR_TYPE_CALLN 	  ) :: FexprType
     
-- Memory management -----------------------------------------------------------

-- | /fexpr_init/ /expr/ 
--
-- Initializes /expr/ for use. Its value is set to the atomic integer 0.
foreign import ccall "fexpr.h fexpr_init"
  fexpr_init :: Ptr CFexpr -> IO ()

-- | /fexpr_clear/ /expr/ 
--
-- Clears /expr/, freeing its allocated memory.
foreign import ccall "fexpr.h fexpr_clear"
  fexpr_clear :: Ptr CFexpr -> IO ()

foreign import ccall "fexpr.h &fexpr_clear"
  p_fexpr_clear :: FunPtr (Ptr CFexpr -> IO ())

-- | /_fexpr_vec_init/ /len/ 
--
-- Returns a heap-allocated vector of /len/ initialized expressions.
foreign import ccall "fexpr.h _fexpr_vec_init"
  _fexpr_vec_init :: CLong -> IO (Ptr Fexpr)

-- | /_fexpr_vec_clear/ /vec/ /len/ 
--
-- Clears the /len/ expressions in /vec/ and frees /vec/ itself.
foreign import ccall "fexpr.h _fexpr_vec_clear"
  _fexpr_vec_clear :: Ptr Fexpr -> CLong -> IO ()

-- | /fexpr_fit_size/ /expr/ /size/ 
--
-- Ensures that /expr/ has room for /size/ words.
foreign import ccall "fexpr.h fexpr_fit_size"
  fexpr_fit_size :: Ptr CFexpr -> CLong -> IO ()

-- | /fexpr_set/ /res/ /expr/ 
--
-- Sets /res/ to the a copy of /expr/.
foreign import ccall "fexpr.h fexpr_set"
  fexpr_set :: Ptr CFexpr -> Ptr CFexpr -> IO ()

-- | /fexpr_swap/ /a/ /b/ 
--
-- Swaps /a/ and /b/ efficiently.
foreign import ccall "fexpr.h fexpr_swap"
  fexpr_swap :: Ptr CFexpr -> Ptr CFexpr -> IO ()

-- Size information ------------------------------------------------------------

-- | /fexpr_depth/ /expr/ 
--
-- Returns the depth of /expr/ as a symbolic expression tree.
foreign import ccall "fexpr.h fexpr_depth"
  fexpr_depth :: Ptr CFexpr -> IO CLong

-- | /fexpr_num_leaves/ /expr/ 
--
-- Returns the number of leaves (atoms, counted with repetition) in the
-- expression /expr/.
foreign import ccall "fexpr.h fexpr_num_leaves"
  fexpr_num_leaves :: Ptr CFexpr -> IO CLong

-- | /fexpr_size/ /expr/ 
--
-- Returns the number of words in the internal representation of /expr/.
foreign import ccall "fexpr.h fexpr_size"
  fexpr_size :: Ptr CFexpr -> IO CLong

-- | /fexpr_size_bytes/ /expr/ 
--
-- Returns the number of bytes in the internal representation of /expr/.
-- The count excludes the size of the structure itself. Add
-- @sizeof(fexpr_struct)@ to get the size of the object as a whole.
foreign import ccall "fexpr.h fexpr_size_bytes"
  fexpr_size_bytes :: Ptr CFexpr -> IO CLong

-- | /fexpr_allocated_bytes/ /expr/ 
--
-- Returns the number of allocated bytes in the internal representation of
-- /expr/. The count excludes the size of the structure itself. Add
-- @sizeof(fexpr_struct)@ to get the size of the object as a whole.
foreign import ccall "fexpr.h fexpr_allocated_bytes"
  fexpr_allocated_bytes :: Ptr CFexpr -> IO CLong

-- Comparisons -----------------------------------------------------------------

-- | /fexpr_equal/ /a/ /b/ 
--
-- Checks if /a/ and /b/ are exactly equal as expressions.
foreign import ccall "fexpr.h fexpr_equal"
  fexpr_equal :: Ptr CFexpr -> Ptr CFexpr -> IO CInt

-- | /fexpr_equal_si/ /expr/ /c/ 
--
foreign import ccall "fexpr.h fexpr_equal_si"
  fexpr_equal_si :: Ptr CFexpr -> CLong -> IO CInt

-- | /fexpr_equal_ui/ /expr/ /c/ 
--
-- Checks if /expr/ is an atomic integer exactly equal to /c/.
foreign import ccall "fexpr.h fexpr_equal_ui"
  fexpr_equal_ui :: Ptr CFexpr -> CULong -> IO CInt

-- | /fexpr_hash/ /expr/ 
--
-- Returns a hash of the expression /expr/.
foreign import ccall "fexpr.h fexpr_hash"
  fexpr_hash :: Ptr CFexpr -> IO CULong

-- | /fexpr_cmp_fast/ /a/ /b/ 
--
-- Compares /a/ and /b/ using an ordering based on the internal
-- representation, returning -1, 0 or 1. This can be used, for instance, to
-- maintain sorted arrays of expressions for binary search; the sort order
-- has no mathematical significance.
foreign import ccall "fexpr.h fexpr_cmp_fast"
  fexpr_cmp_fast :: Ptr CFexpr -> Ptr CFexpr -> IO CInt

-- Atoms -----------------------------------------------------------------------

-- | /fexpr_is_integer/ /expr/ 
--
-- Returns whether /expr/ is an atomic integer
foreign import ccall "fexpr.h fexpr_is_integer"
  fexpr_is_integer :: Ptr CFexpr -> IO CInt

-- | /fexpr_is_symbol/ /expr/ 
--
-- Returns whether /expr/ is an atomic symbol.
foreign import ccall "fexpr.h fexpr_is_symbol"
  fexpr_is_symbol :: Ptr CFexpr -> IO CInt

-- | /fexpr_is_string/ /expr/ 
--
-- Returns whether /expr/ is an atomic string.
foreign import ccall "fexpr.h fexpr_is_string"
  fexpr_is_string :: Ptr CFexpr -> IO CInt

-- | /fexpr_is_atom/ /expr/ 
--
-- Returns whether /expr/ is any atom.
foreign import ccall "fexpr.h fexpr_is_atom"
  fexpr_is_atom :: Ptr CFexpr -> IO CInt

-- | /fexpr_zero/ /res/ 
--
-- Sets /res/ to the atomic integer 0.
foreign import ccall "fexpr.h fexpr_zero"
  fexpr_zero :: Ptr CFexpr -> IO ()

-- | /fexpr_is_zero/ /expr/ 
--
-- Returns whether /expr/ is the atomic integer 0.
foreign import ccall "fexpr.h fexpr_is_zero"
  fexpr_is_zero :: Ptr CFexpr -> IO CInt

-- | /fexpr_is_neg_integer/ /expr/ 
--
-- Returns whether /expr/ is any negative atomic integer.
foreign import ccall "fexpr.h fexpr_is_neg_integer"
  fexpr_is_neg_integer :: Ptr CFexpr -> IO CInt

-- | /fexpr_set_si/ /res/ /c/ 
foreign import ccall "fexpr.h fexpr_set_si"
  fexpr_set_si :: Ptr CFexpr -> CLong -> IO ()
-- | /fexpr_set_ui/ /res/ /c/ 
foreign import ccall "fexpr.h fexpr_set_ui"
  fexpr_set_ui :: Ptr CFexpr -> CULong -> IO ()
-- | /fexpr_set_fmpz/ /res/ /c/ 
--
-- Sets /res/ to the atomic integer /c/.
foreign import ccall "fexpr.h fexpr_set_fmpz"
  fexpr_set_fmpz :: Ptr CFexpr -> Ptr CFmpz -> IO ()

-- | /fexpr_get_fmpz/ /res/ /expr/ 
--
-- Sets /res/ to the atomic integer in /expr/. This aborts if /expr/ is not
-- an atomic integer.
foreign import ccall "fexpr.h fexpr_get_fmpz"
  fexpr_get_fmpz :: Ptr CFmpz -> Ptr CFexpr -> IO CInt

-- | /fexpr_set_symbol_builtin/ /res/ /id/ 
--
-- Sets /res/ to the builtin symbol with internal index /id/ (see
-- @fexpr-builtin@).
foreign import ccall "fexpr.h fexpr_set_symbol_builtin"
  fexpr_set_symbol_builtin :: Ptr CFexpr -> CLong -> IO ()

-- | /fexpr_is_builtin_symbol/ /expr/ /id/ 
--
-- Returns whether /expr/ is the builtin symbol with index /id/ (see
-- @fexpr-builtin@).
foreign import ccall "fexpr.h fexpr_is_builtin_symbol"
  fexpr_is_builtin_symbol :: Ptr CFexpr -> CLong -> IO CInt

-- | /fexpr_is_any_builtin_symbol/ /expr/ 
--
-- Returns whether /expr/ is any builtin symbol (see @fexpr-builtin@).
foreign import ccall "fexpr.h fexpr_is_any_builtin_symbol"
  fexpr_is_any_builtin_symbol :: Ptr CFexpr -> IO CInt

-- | /fexpr_set_symbol_str/ /res/ /s/ 
--
-- Sets /res/ to the symbol given by /s/.
foreign import ccall "fexpr.h fexpr_set_symbol_str"
  fexpr_set_symbol_str :: Ptr CFexpr -> CString -> IO ()

-- | /fexpr_get_symbol_str/ /expr/ 
--
-- Returns the symbol in /expr/ as a string. The string must be freed with
-- @flint_free@. This aborts if /expr/ is not an atomic symbol.
foreign import ccall "fexpr.h fexpr_get_symbol_str"
  fexpr_get_symbol_str :: Ptr CFexpr -> IO CString

-- | /fexpr_set_string/ /res/ /s/ 
--
-- Sets /res/ to the atomic string /s/.
foreign import ccall "fexpr.h fexpr_set_string"
  fexpr_set_string :: Ptr CFexpr -> CString -> IO ()

-- | /fexpr_get_string/ /expr/ 
--
-- Assuming that /expr/ is an atomic string, returns a copy of this string.
-- The string must be freed with @flint_free@.
foreign import ccall "fexpr.h fexpr_get_string"
  fexpr_get_string :: Ptr CFexpr -> IO CString

-- Input and output ------------------------------------------------------------

-- | /fexpr_write/ /stream/ /expr/ 
--
-- Writes /expr/ to /stream/.
foreign import ccall "fexpr.h fexpr_write"
  fexpr_write :: Ptr CCalciumStream -> Ptr CFexpr -> IO ()

-- | /fexpr_print/ /expr/ 
--
-- Prints /expr/ to standard output.
fexpr_print :: Ptr CFexpr -> IO ()
fexpr_print expr = do
  printCStr fexpr_get_str expr
  return ()
  
-- | /fexpr_get_str/ /expr/ 
--
-- Returns a string representation of /expr/. The string must be freed with
-- @flint_free@.
-- 
-- Warning: string literals appearing in expressions are currently not
-- escaped.
foreign import ccall "fexpr.h fexpr_get_str"
  fexpr_get_str :: Ptr CFexpr -> IO CString

-- LaTeX output ----------------------------------------------------------------

-- | /fexpr_write_latex/ /stream/ /expr/ /flags/ 
--
-- Writes the LaTeX representation of /expr/ to /stream/.
foreign import ccall "fexpr.h fexpr_write_latex"
  fexpr_write_latex :: Ptr CCalciumStream -> Ptr CFexpr -> CULong -> IO ()

-- | /fexpr_print_latex/ /expr/ /flags/ 
--
-- Prints the LaTeX representation of /expr/ to standard output.
fexpr_print_latex :: Ptr CFexpr -> CULong -> IO ()
fexpr_print_latex expr flags = do
  printCStr (flip fexpr_get_str_latex flags) expr
  return ()
  
-- | /fexpr_get_str_latex/ /expr/ /flags/ 
--
-- Returns a string of the LaTeX representation of /expr/. The string must
-- be freed with @flint_free@.
-- 
-- Warning: string literals appearing in expressions are currently not
-- escaped.
foreign import ccall "fexpr.h fexpr_get_str_latex"
  fexpr_get_str_latex :: Ptr CFexpr -> CULong -> IO CString

type FexprLatexFlag = CULong

fexpr_latex_small, fexpr_latex_logic :: FexprLatexFlag

-- | /fexpr_latex_small/
--
-- Generate more compact formulas, most importantly by printing
-- fractions inline as \(p/q\) instead of as \(\frac{p}{q}\).  This
-- flag is automatically activated within subscripts and superscripts
-- and in certain other parts of formulas.
fexpr_latex_small = #const FEXPR_LATEX_SMALL

-- | /fexpr_latex_logic/
--
-- Use symbols for logical operators such as Not, And, Or, which by
-- default are rendered as words for legibility.
fexpr_latex_logic = #const FEXPR_LATEX_LOGIC

-- Function call structure -----------------------------------------------------

-- | /fexpr_nargs/ /expr/ 
--
-- Returns the number of arguments /n/ in the function call
-- \(f(e_1,\ldots,e_n)\) represented by /expr/. If /expr/ is an atom,
-- returns -1.
foreign import ccall "fexpr.h fexpr_nargs"
  fexpr_nargs :: Ptr CFexpr -> IO CLong

-- | /fexpr_func/ /res/ /expr/ 
--
-- Assuming that /expr/ represents a function call \(f(e_1,\ldots,e_n)\),
-- sets /res/ to the function expression /f/.
foreign import ccall "fexpr.h fexpr_func"
  fexpr_func :: Ptr CFexpr -> Ptr CFexpr -> IO ()

-- | /fexpr_view_func/ /view/ /expr/ 
--
-- As @fexpr_func@, but sets /view/ to a shallow view instead of copying
-- the expression. The variable /view/ must not be initialized before use
-- or cleared after use, and /expr/ must not be modified or cleared as long
-- as /view/ is in use.
foreign import ccall "fexpr.h fexpr_view_func"
  fexpr_view_func :: Ptr CFexpr -> Ptr CFexpr -> IO ()

-- | /fexpr_arg/ /res/ /expr/ /i/ 
--
-- Assuming that /expr/ represents a function call \(f(e_1,\ldots,e_n)\),
-- sets /res/ to the argument \(e_{i+1}\). Note that indexing starts from
-- 0. The index must be in bounds, with \(0 \le i < n\).
foreign import ccall "fexpr.h fexpr_arg"
  fexpr_arg :: Ptr CFexpr -> Ptr CFexpr -> CLong -> IO ()

-- | /fexpr_view_arg/ /view/ /expr/ /i/ 
--
-- As @fexpr_arg@, but sets /view/ to a shallow view instead of copying the
-- expression. The variable /view/ must not be initialized before use or
-- cleared after use, and /expr/ must not be modified or cleared as long as
-- /view/ is in use.
foreign import ccall "fexpr.h fexpr_view_arg"
  fexpr_view_arg :: Ptr CFexpr -> Ptr CFexpr -> CLong -> IO ()

-- | /fexpr_view_next/ /view/ 
--
-- Assuming that /view/ is a shallow view of a function argument \(e_i\) in
-- a function call \(f(e_1,\ldots,e_n)\), sets /view/ to a view of the next
-- argument \(e_{i+1}\). This function can be called when /view/ refers to
-- the last argument \(e_n\), provided that /view/ is not used afterwards.
-- This function can also be called when /view/ refers to the function /f/,
-- in which case it will make /view/ point to \(e_1\).
foreign import ccall "fexpr.h fexpr_view_next"
  fexpr_view_next :: Ptr CFexpr -> IO ()

-- | /fexpr_is_builtin_call/ /expr/ /id/ 
--
-- Returns whether /expr/ has the form \(f(\ldots)\) where /f/ is a builtin
-- function defined by /id/ (see @fexpr-builtin@).
foreign import ccall "fexpr.h fexpr_is_builtin_call"
  fexpr_is_builtin_call :: Ptr CFexpr -> CLong -> IO CInt

-- | /fexpr_is_any_builtin_call/ /expr/ 
--
-- Returns whether /expr/ has the form \(f(\ldots)\) where /f/ is any
-- builtin function (see @fexpr-builtin@).
foreign import ccall "fexpr.h fexpr_is_any_builtin_call"
  fexpr_is_any_builtin_call :: Ptr CFexpr -> IO CInt

-- Composition -----------------------------------------------------------------

-- | /fexpr_call0/ /res/ /f/ 
foreign import ccall "fexpr.h fexpr_call0"
  fexpr_call0 :: Ptr CFexpr -> Ptr CFexpr -> IO ()
-- | /fexpr_call1/ /res/ /f/ /x1/ 
foreign import ccall "fexpr.h fexpr_call1"
  fexpr_call1 :: Ptr CFexpr -> Ptr CFexpr -> Ptr CFexpr -> IO ()
-- | /fexpr_call2/ /res/ /f/ /x1/ /x2/ 
foreign import ccall "fexpr.h fexpr_call2"
  fexpr_call2 :: Ptr CFexpr -> Ptr CFexpr -> Ptr CFexpr -> Ptr CFexpr -> IO ()
-- | /fexpr_call3/ /res/ /f/ /x1/ /x2/ /x3/ 
foreign import ccall "fexpr.h fexpr_call3"
  fexpr_call3 :: Ptr CFexpr -> Ptr CFexpr -> Ptr CFexpr -> Ptr CFexpr -> Ptr CFexpr -> IO ()
-- | /fexpr_call4/ /res/ /f/ /x1/ /x2/ /x3/ /x4/ 
foreign import ccall "fexpr.h fexpr_call4"
  fexpr_call4 :: Ptr CFexpr -> Ptr CFexpr -> Ptr CFexpr -> Ptr CFexpr -> Ptr CFexpr -> Ptr CFexpr -> IO ()
-- | /fexpr_call_vec/ /res/ /f/ /args/ /len/ 
--
-- Creates the function call \(f(x_1,\ldots,x_n)\). The /vec/ version takes
-- the arguments as an array /args/ and /n/ is given by /len/. Warning:
-- aliasing between inputs and outputs is not implemented.
foreign import ccall "fexpr.h fexpr_call_vec"
  fexpr_call_vec :: Ptr CFexpr -> Ptr CFexpr -> Ptr Fexpr -> CLong -> IO ()

-- | /fexpr_call_builtin1/ /res/ /f/ /x1/ 
foreign import ccall "fexpr.h fexpr_call_builtin1"
  fexpr_call_builtin1 :: Ptr CFexpr -> CLong -> Ptr CFexpr -> IO ()
-- | /fexpr_call_builtin2/ /res/ /f/ /x1/ /x2/ 
--
-- Creates the function call \(f(x_1,\ldots,x_n)\), where /f/ defines a
-- builtin symbol.
foreign import ccall "fexpr.h fexpr_call_builtin2"
  fexpr_call_builtin2 :: Ptr CFexpr -> CLong -> Ptr CFexpr -> Ptr CFexpr -> IO ()

-- Subexpressions and replacement ----------------------------------------------

-- | /fexpr_contains/ /expr/ /x/ 
--
-- Returns whether /expr/ contains the expression /x/ as a subexpression
-- (this includes the case where /expr/ and /x/ are equal).
foreign import ccall "fexpr.h fexpr_contains"
  fexpr_contains :: Ptr CFexpr -> Ptr CFexpr -> IO CInt

-- | /fexpr_replace/ /res/ /expr/ /x/ /y/ 
--
-- Sets /res/ to the expression /expr/ with all occurrences of the
-- subexpression /x/ replaced by the expression /y/. Returns a boolean
-- value indicating whether any replacements have been performed. Aliasing
-- is allowed between /res/ and /expr/ but not between /res/ and /x/ or
-- /y/.
foreign import ccall "fexpr.h fexpr_replace"
  fexpr_replace :: Ptr CFexpr -> Ptr CFexpr -> Ptr CFexpr -> Ptr CFexpr -> IO CInt

-- | /fexpr_replace2/ /res/ /expr/ /x1/ /y1/ /x2/ /y2/ 
--
-- Like @fexpr_replace@, but simultaneously replaces /x1/ by /y1/ and /x2/
-- by /y2/.
foreign import ccall "fexpr.h fexpr_replace2"
  fexpr_replace2 :: Ptr CFexpr -> Ptr CFexpr -> Ptr CFexpr -> Ptr CFexpr -> Ptr CFexpr -> Ptr CFexpr -> IO CInt

-- | /fexpr_replace_vec/ /res/ /expr/ /xs/ /ys/ 
--
-- Sets /res/ to the expression /expr/ with all occurrences of the
-- subexpressions given by entries in /xs/ replaced by the corresponding
-- expressions in /ys/. It is required that /xs/ and /ys/ have the same
-- length. Returns a boolean value indicating whether any replacements have
-- been performed. Aliasing is allowed between /res/ and /expr/ but not
-- between /res/ and the entries of /xs/ or /ys/.
foreign import ccall "fexpr.h fexpr_replace_vec"
  fexpr_replace_vec :: Ptr CFexpr -> Ptr CFexpr -> Ptr CFexprVec -> Ptr CFexprVec -> IO CInt

-- Arithmetic expressions ------------------------------------------------------

-- | /fexpr_set_fmpq/ /res/ /x/ 
--
-- Sets /res/ to the rational number /x/. This creates an atomic integer if
-- the denominator of /x/ is one, and otherwise creates a division
-- expression.
foreign import ccall "fexpr.h fexpr_set_fmpq"
  fexpr_set_fmpq :: Ptr CFexpr -> Ptr CFmpq -> IO ()

-- | /fexpr_set_arf/ /res/ /x/ 
foreign import ccall "fexpr.h fexpr_set_arf"
  fexpr_set_arf :: Ptr CFexpr -> Ptr CArf -> IO ()
-- | /fexpr_set_d/ /res/ /x/ 
--
-- Sets /res/ to an expression for the value of the floating-point number
-- /x/. NaN is represented as @Undefined@. For a regular value, this
-- creates an atomic integer or a rational fraction if the exponent is
-- small, and otherwise creates an expression of the form
-- @Mul(m, Pow(2, e))@.
foreign import ccall "fexpr.h fexpr_set_d"
  fexpr_set_d :: Ptr CFexpr -> CDouble -> IO ()

-- | /fexpr_set_re_im_d/ /res/ /x/ /y/ 
--
-- Sets /res/ to an expression for the complex number with real part /x/
-- and imaginary part /y/.
foreign import ccall "fexpr.h fexpr_set_re_im_d"
  fexpr_set_re_im_d :: Ptr CFexpr -> CDouble -> CDouble -> IO ()

-- | /fexpr_neg/ /res/ /a/ 
foreign import ccall "fexpr.h fexpr_neg"
  fexpr_neg :: Ptr CFexpr -> Ptr CFexpr -> IO ()
-- | /fexpr_add/ /res/ /a/ /b/ 
foreign import ccall "fexpr.h fexpr_add"
  fexpr_add :: Ptr CFexpr -> Ptr CFexpr -> Ptr CFexpr -> IO ()
-- | /fexpr_sub/ /res/ /a/ /b/ 
foreign import ccall "fexpr.h fexpr_sub"
  fexpr_sub :: Ptr CFexpr -> Ptr CFexpr -> Ptr CFexpr -> IO ()
-- | /fexpr_mul/ /res/ /a/ /b/ 
foreign import ccall "fexpr.h fexpr_mul"
  fexpr_mul :: Ptr CFexpr -> Ptr CFexpr -> Ptr CFexpr -> IO ()
-- | /fexpr_div/ /res/ /a/ /b/ 
foreign import ccall "fexpr.h fexpr_div"
  fexpr_div :: Ptr CFexpr -> Ptr CFexpr -> Ptr CFexpr -> IO ()
-- | /fexpr_pow/ /res/ /a/ /b/ 
--
-- Constructs an arithmetic expression with given arguments. No
-- simplifications whatsoever are performed.
foreign import ccall "fexpr.h fexpr_pow"
  fexpr_pow :: Ptr CFexpr -> Ptr CFexpr -> Ptr CFexpr -> IO ()

-- | /fexpr_is_arithmetic_operation/ /expr/ 
--
-- Returns whether /expr/ is of the form \(f(e_1,\ldots,e_n)\) where /f/ is
-- one of the arithmetic operators @Pos@, @Neg@, @Add@, @Sub@, @Mul@,
-- @Div@.
foreign import ccall "fexpr.h fexpr_is_arithmetic_operation"
  fexpr_is_arithmetic_operation :: Ptr CFexpr -> IO CInt

-- | /fexpr_arithmetic_nodes/ /nodes/ /expr/ 
--
-- Sets /nodes/ to a vector of subexpressions of /expr/ such that /expr/ is
-- an arithmetic expression with /nodes/ as leaves. More precisely, /expr/
-- will be constructed out of nested application the arithmetic operators
-- @Pos@, @Neg@, @Add@, @Sub@, @Mul@, @Div@ with integers and expressions
-- in /nodes/ as leaves. Powers @Pow@ with an atomic integer exponent are
-- also allowed. The nodes are output without repetition but are not
-- automatically sorted in a canonical order.
foreign import ccall "fexpr.h fexpr_arithmetic_nodes"
  fexpr_arithmetic_nodes :: Ptr CFexprVec -> Ptr CFexpr -> IO ()

-- | /fexpr_get_fmpz_mpoly_q/ /res/ /expr/ /vars/ /ctx/ 
--
-- Sets /res/ to the expression /expr/ as a formal rational function of the
-- subexpressions in /vars/. The vector /vars/ must have the same length as
-- the number of variables specified in /ctx/. To build /vars/
-- automatically for a given expression, @fexpr_arithmetic_nodes@ may be
-- used.
-- 
-- Returns 1 on success and 0 on failure. Failure can occur for the
-- following reasons:
-- 
-- -   A subexpression is encountered that cannot be interpreted as an
--     arithmetic operation and does not appear (exactly) in /vars/.
-- -   Overflow (too many terms or too large exponent).
-- -   Division by zero (a zero denominator is encountered).
-- 
-- It is important to note that this function views /expr/ as a formal
-- rational function with /vars/ as formal indeterminates. It does thus not
-- check for algebraic relations between /vars/ and can implicitly divide
-- by zero if /vars/ are not algebraically independent.
foreign import ccall "fexpr.h fexpr_get_fmpz_mpoly_q"
  fexpr_get_fmpz_mpoly_q :: Ptr CFmpzMPolyQ -> Ptr CFexpr -> Ptr CFexprVec -> Ptr CFmpzMPolyCtx -> IO CInt

-- | /fexpr_set_fmpz_mpoly/ /res/ /poly/ /vars/ /ctx/ 
foreign import ccall "fexpr.h fexpr_set_fmpz_mpoly"
  fexpr_set_fmpz_mpoly :: Ptr CFexpr -> Ptr CFmpzMPoly -> Ptr CFexprVec -> Ptr CFmpzMPolyCtx -> IO ()
-- | /fexpr_set_fmpz_mpoly_q/ /res/ /frac/ /vars/ /ctx/ 
--
-- Sets /res/ to an expression for the multivariate polynomial /poly/ (or
-- rational function /frac/), using the expressions in /vars/ as the
-- variables. The length of /vars/ must agree with the number of variables
-- in /ctx/. If /NULL/ is passed for /vars/, a default choice of symbols is
-- used.
foreign import ccall "fexpr.h fexpr_set_fmpz_mpoly_q"
  fexpr_set_fmpz_mpoly_q :: Ptr CFexpr -> Ptr CFmpzMPolyQ -> Ptr CFexprVec -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fexpr_expanded_normal_form/ /res/ /expr/ /flags/ 
--
-- Sets /res/ to /expr/ converted to expanded normal form viewed as a
-- formal rational function with its non-arithmetic subexpressions as
-- terminal nodes. This function first computes nodes with
-- @fexpr_arithmetic_nodes@, sorts the nodes, evaluates to a rational
-- function with @fexpr_get_fmpz_mpoly_q@, and then converts back to an
-- expression with @fexpr_set_fmpz_mpoly_q@. Optional /flags/ are reserved
-- for future use.
foreign import ccall "fexpr.h fexpr_expanded_normal_form"
  fexpr_expanded_normal_form :: Ptr CFexpr -> Ptr CFexpr -> CULong -> IO CInt

-- Vectors ---------------------------------------------------------------------

data FexprVec = FexprVec {-# UNPACK #-} !(ForeignPtr CFexprVec)
data CFexprVec = CFexprVec (Ptr Fexpr) CLong CLong

instance Storable CFexprVec where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fexpr_vec_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fexpr_vec_t}
  peek ptr = CFexprVec
    <$> #{peek fexpr_vec_struct, entries} ptr
    <*> #{peek fexpr_vec_struct, alloc  } ptr
    <*> #{peek fexpr_vec_struct, length } ptr
  poke ptr (CFexprVec entries alloc length) = do
    #{poke fexpr_vec_struct, entries } ptr entries
    #{poke fexpr_vec_struct, alloc   } ptr alloc
    #{poke fexpr_vec_struct, length  } ptr length

newFexprVec n = do
  p <- mallocForeignPtr
  withForeignPtr p $ \p -> do
    fexpr_vec_init p n
  addForeignPtrFinalizer p_fexpr_vec_clear p
  return $ FexprVec p

withFexprVec (FexprVec p) f = do
  withForeignPtr p $ \fp -> (FexprVec p,) <$> f fp

withNewFexprVec n f = do
  x <- newFexprVec n
  withFexprVec x f

-- | /fexpr_vec_init/ /vec/ /len/ 
--
-- Initializes /vec/ to a vector of length /len/. All entries are set to
-- the atomic integer 0.
foreign import ccall "fexpr.h fexpr_vec_init"
  fexpr_vec_init :: Ptr CFexprVec -> CLong -> IO ()

-- | /fexpr_vec_clear/ /vec/ 
--
-- Clears the vector /vec/.
foreign import ccall "fexpr.h fexpr_vec_clear"
  fexpr_vec_clear :: Ptr CFexprVec -> IO ()

foreign import ccall "fexpr.h &fexpr_vec_clear"
  p_fexpr_vec_clear :: FunPtr (Ptr CFexprVec -> IO ())

-- | /fexpr_vec_print/ /vec/ 
--
-- Prints /vec/ to standard output.
foreign import ccall "fexpr.h fexpr_vec_print"
  fexpr_vec_print :: Ptr CFexprVec -> IO ()

-- | /fexpr_vec_swap/ /x/ /y/ 
--
-- Swaps /x/ and /y/ efficiently.
foreign import ccall "fexpr.h fexpr_vec_swap"
  fexpr_vec_swap :: Ptr CFexprVec -> Ptr CFexprVec -> IO ()

-- | /fexpr_vec_fit_length/ /vec/ /len/ 
--
-- Ensures that /vec/ has space for /len/ entries.
foreign import ccall "fexpr.h fexpr_vec_fit_length"
  fexpr_vec_fit_length :: Ptr CFexprVec -> CLong -> IO ()

-- | /fexpr_vec_set/ /dest/ /src/ 
--
-- Sets /dest/ to a copy of /src/.
foreign import ccall "fexpr.h fexpr_vec_set"
  fexpr_vec_set :: Ptr CFexprVec -> Ptr CFexprVec -> IO ()

-- | /fexpr_vec_append/ /vec/ /expr/ 
--
-- Appends /expr/ to the end of the vector /vec/.
foreign import ccall "fexpr.h fexpr_vec_append"
  fexpr_vec_append :: Ptr CFexprVec -> Ptr CFexpr -> IO ()

-- | /fexpr_vec_insert_unique/ /vec/ /expr/ 
--
-- Inserts /expr/ without duplication into vec, returning its position. If
-- this expression already exists, /vec/ is unchanged. If this expression
-- does not exist in /vec/, it is appended.
foreign import ccall "fexpr.h fexpr_vec_insert_unique"
  fexpr_vec_insert_unique :: Ptr CFexprVec -> Ptr CFexpr -> IO CLong

-- | /fexpr_vec_set_length/ /vec/ /len/ 
--
-- Sets the length of /vec/ to /len/, truncating or zero-extending as
-- needed.
foreign import ccall "fexpr.h fexpr_vec_set_length"
  fexpr_vec_set_length :: Ptr CFexprVec -> CLong -> IO ()

-- | /_fexpr_vec_sort_fast/ /vec/ /len/ 
--
-- Sorts the /len/ entries in /vec/ using the comparison function
-- @fexpr_cmp_fast@.
foreign import ccall "fexpr.h _fexpr_vec_sort_fast"
  _fexpr_vec_sort_fast :: Ptr Fexpr -> CLong -> IO ()




