{-|
module      :  Data.Number.Flint.MPoly.FFI
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de
-}
module Data.Number.Flint.MPoly.FFI (
  -- * Support functions for multivariate polynomials
    MPolyCtx (..)
  , CMPolyCtx (..)
  , newMPolyCtx
  , withMPolyCtx
  -- * Context
  , mpoly_ctx_init
  , mpoly_ctx_clear
  , mpoly_ordering_randtest
  , mpoly_ctx_init_rand
  , mpoly_ordering_isdeg
  , mpoly_ordering_isrev
  , mpoly_ordering_print
  -- * Orderings
  , COrdering (..)
  , ord_lex
  , ord_deglex
  , ord_degrevlex
  -- * Monomial arithmetic
  , mpoly_monomial_add
  , mpoly_monomial_add_mp
  , mpoly_monomial_sub
  , mpoly_monomial_sub_mp
  , mpoly_monomial_overflows
  , mpoly_monomial_overflows_mp
  , mpoly_monomial_overflows1
  , mpoly_monomial_set
  , mpoly_monomial_swap
  , mpoly_monomial_mul_ui
  -- * Monomial comparison
  , mpoly_monomial_is_zero
  , mpoly_monomial_equal
  , mpoly_get_cmpmask
  , mpoly_monomial_lt
  , mpoly_monomial_gt
  , mpoly_monomial_cmp
  -- * Monomial divisibility
  , mpoly_monomial_divides
  , mpoly_monomial_divides_mp
  , mpoly_monomial_divides1
  , mpoly_monomial_divides_tight
  -- * Basic manipulation
  , mpoly_exp_bits_required_ui
  , mpoly_exp_bits_required_ffmpz
  , mpoly_exp_bits_required_pfmpz
  , mpoly_max_fields_ui_sp
  , mpoly_max_fields_fmpz
  , mpoly_max_degrees_tight
  , mpoly_monomial_exists
  , mpoly_search_monomials
  -- * Setting and getting monomials
  , mpoly_term_exp_fits_ui
  , mpoly_term_exp_fits_si
  , mpoly_get_monomial_ui
  , mpoly_get_monomial_ffmpz
  , mpoly_get_monomial_pfmpz
  , mpoly_set_monomial_ui
  , mpoly_set_monomial_ffmpz
  , mpoly_set_monomial_pfmpz
  -- * Packing and unpacking monomials
  , mpoly_pack_vec_ui
  , mpoly_pack_vec_fmpz
  , mpoly_unpack_vec_ui
  , mpoly_unpack_vec_fmpz
  , mpoly_repack_monomials
  , mpoly_pack_monomials_tight
  , mpoly_unpack_monomials_tight
  -- * Chunking
  , mpoly_main_variable_terms1
  -- * Chained heap functions
  , _mpoly_heap_insert
  , _mpoly_heap_insert1
  , _mpoly_heap_pop
  , _mpoly_heap_pop1
) where 

-- support functions for multivariate polynomials ------------------------------

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, castPtr)
import Foreign.Storable

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz

#include <flint/flint.h>
#include <flint/mpoly.h>

-- mpoly_ctx_t -----------------------------------------------------------------

data MPolyCtx = MPolyCtx {-# UNPACK #-} !(ForeignPtr CMPolyCtx)
data CMPolyCtx
  
instance Storable CMPolyCtx where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size mpoly_ctx_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment mpoly_ctx_t}
  peek = error "CMPolyCtx.peek is not defined."
  poke = error "CMPolyCtx.poke is not defined."

-- | Create a new `MPolyCtx` structure.
newMPolyCtx nvars ord = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> do
    mpoly_ctx_init x (fromIntegral nvars) ord
  addForeignPtrFinalizer p_mpoly_ctx_clear x
  return $ MPolyCtx x

-- | Use a new `MPolyCtx` structure.
withMPolyCtx (MPolyCtx ctx) f = do
  withForeignPtr ctx $ \pctx -> (MPolyCtx ctx,) <$> f pctx
  
-- ordering_t ------------------------------------------------------------------

newtype COrdering = COrdering {_Ordering :: CInt} deriving Eq

instance Storable COrdering where
  {-# INLINE sizeOf #-}
  sizeOf _ = sizeOf (undefined :: CInt)
  {-# INLINE alignment #-}
  alignment _ = alignment (undefined :: CInt)
  peek ptr = do
    v <- peek (castPtr ptr) :: IO CInt
    return $ COrdering v
  poke = undefined

ord_lex       = COrdering #const ORD_LEX
ord_deglex    = COrdering #const ORD_DEGLEX
ord_degrevlex = COrdering #const ORD_DEGREVLEX

-- mpoly_heap_s ----------------------------------------------------------------

data MPolyHeap = MPolyHeap {-# UNPACK #-} !(ForeignPtr CMPolyHeap)
type CMPolyHeap = Ptr ()

data MPolyHeap1 = MPolyHeap1 {-# UNPACK #-} !(ForeignPtr CMPolyHeap1)
type CMPolyHeap1 = Ptr ()

--------------------------------------------------------------------------------

-- | /mpoly_ctx_init/ /ctx/ /nvars/ /ord/ 
-- 
-- Initialize a context for specified number of variables and ordering.
foreign import ccall "mpoly.h mpoly_ctx_init"
  mpoly_ctx_init :: Ptr CMPolyCtx -> CLong -> COrdering -> IO ()

-- | /mpoly_ctx_clear/ /mctx/ 
-- 
-- Clean up any space used by a context object.
foreign import ccall "mpoly.h mpoly_ctx_clear"
  mpoly_ctx_clear :: Ptr CMPolyCtx -> IO ()

foreign import ccall "mpoly.h &mpoly_ctx_clear"
  p_mpoly_ctx_clear :: FunPtr (tr CMPolyCtx -> IO ())

-- | /mpoly_ordering_randtest/ /state/ 
-- 
-- Return a random ordering. The possibilities are @ORD_LEX@, @ORD_DEGLEX@
-- and @ORD_DEGREVLEX@.
foreign import ccall "mpoly.h mpoly_ordering_randtest"
  mpoly_ordering_randtest :: Ptr CFRandState -> IO (COrdering)

-- | /mpoly_ctx_init_rand/ /mctx/ /state/ /max_nvars/ 
-- 
-- Initialize a context with a random choice for the ordering.
foreign import ccall "mpoly.h mpoly_ctx_init_rand"
  mpoly_ctx_init_rand :: Ptr CMPolyCtx -> Ptr CFRandState -> CLong -> IO ()

-- | /mpoly_ordering_isdeg/ /ord/ 
-- 
-- Return 1 if the given ordering is a degree ordering (deglex or
-- degrevlex).
foreign import ccall "mpoly.h mpoly_ordering_isdeg"
  mpoly_ordering_isdeg :: COrdering -> IO CInt

-- | /mpoly_ordering_isrev/ /ord/ 
-- 
-- Return 1 if the given ordering is a reverse ordering (currently only
-- degrevlex).
foreign import ccall "mpoly.h mpoly_ordering_isrev"
  mpoly_ordering_isrev :: COrdering -> IO CInt

-- | /mpoly_ordering_print/ /ord/ 
-- 
-- Print a string (either \"lex\", \"deglex\" or \"degrevlex\") to standard
-- output, corresponding to the given ordering.
foreign import ccall "mpoly.h mpoly_ordering_print"
  mpoly_ordering_print :: COrdering -> IO ()

-- Monomial arithmetic ---------------------------------------------------------

-- | /mpoly_monomial_add/ /exp_ptr/ /exp2/ /exp3/ /N/ 
-- 
-- Set @(exp_ptr, N)@ to the sum of the monomials @(exp2, N)@ and
-- @(exp3, N)@, assuming @bits \<= FLINT_BITS@
foreign import ccall "mpoly.h mpoly_monomial_add"
  mpoly_monomial_add :: Ptr CULong -> Ptr CULong -> Ptr CULong -> CLong -> IO ()

-- | /mpoly_monomial_add_mp/ /exp_ptr/ /exp2/ /exp3/ /N/ 
-- 
-- Set @(exp_ptr, N)@ to the sum of the monomials @(exp2, N)@ and
-- @(exp3, N)@.
foreign import ccall "mpoly.h mpoly_monomial_add_mp"
  mpoly_monomial_add_mp :: Ptr CULong -> Ptr CULong -> Ptr CULong -> CLong -> IO ()

-- | /mpoly_monomial_sub/ /exp_ptr/ /exp2/ /exp3/ /N/ 
-- 
-- Set @(exp_ptr, N)@ to the difference of the monomials @(exp2, N)@ and
-- @(exp3, N)@, assuming @bits \<= FLINT_BITS@
foreign import ccall "mpoly.h mpoly_monomial_sub"
  mpoly_monomial_sub :: Ptr CULong -> Ptr CULong -> Ptr CULong -> CLong -> IO ()

-- | /mpoly_monomial_sub_mp/ /exp_ptr/ /exp2/ /exp3/ /N/ 
-- 
-- Set @(exp_ptr, N)@ to the difference of the monomials @(exp2, N)@ and
-- @(exp3, N)@.
foreign import ccall "mpoly.h mpoly_monomial_sub_mp"
  mpoly_monomial_sub_mp :: Ptr CULong -> Ptr CULong -> Ptr CULong -> CLong -> IO ()

-- | /mpoly_monomial_overflows/ /exp2/ /N/ /mask/ 
-- 
-- Return true if any of the fields of the given monomial @(exp2, N)@ has
-- overflowed (or is negative). The @mask@ is a word with the high bit of
-- each field set to 1. In other words, the function returns 1 if any word
-- of @exp2@ has any of the nonzero bits in @mask@ set. Assumes that
-- @bits \<= FLINT_BITS@.
foreign import ccall "mpoly.h mpoly_monomial_overflows"
  mpoly_monomial_overflows :: Ptr CULong -> CLong -> CULong -> IO CInt

-- | /mpoly_monomial_overflows_mp/ /exp_ptr/ /N/ /bits/ 
-- 
-- Return true if any of the fields of the given monomial @(exp_ptr, N)@
-- has overflowed. Assumes that @bits >= FLINT_BITS@.
foreign import ccall "mpoly.h mpoly_monomial_overflows_mp"
  mpoly_monomial_overflows_mp :: Ptr CULong -> CLong -> CFBitCnt -> IO CInt

-- | /mpoly_monomial_overflows1/ /exp/ /mask/ 
-- 
-- As per @mpoly_monomial_overflows@ with @N = 1@.
foreign import ccall "mpoly.h mpoly_monomial_overflows1"
  mpoly_monomial_overflows1 :: CULong -> CULong -> IO CInt

-- | /mpoly_monomial_set/ /exp2/ /exp3/ /N/ 
-- 
-- Set the monomial @(exp2, N)@ to @(exp3, N)@.
foreign import ccall "mpoly.h mpoly_monomial_set"
  mpoly_monomial_set :: Ptr CULong -> Ptr CULong -> CLong -> IO ()

-- | /mpoly_monomial_swap/ /exp2/ /exp3/ /N/ 
-- 
-- Swap the words in @(exp2, N)@ and @(exp3, N)@.
foreign import ccall "mpoly.h mpoly_monomial_swap"
  mpoly_monomial_swap :: Ptr CULong -> Ptr CULong -> CLong -> IO ()

-- | /mpoly_monomial_mul_ui/ /exp2/ /exp3/ /N/ /c/ 
-- 
-- Set the words of @(exp2, N)@ to the words of @(exp3, N)@ multiplied by
-- @c@.
foreign import ccall "mpoly.h mpoly_monomial_mul_ui"
  mpoly_monomial_mul_ui :: Ptr CULong -> Ptr CULong -> CLong -> CULong -> IO ()

-- Monomial comparison ---------------------------------------------------------

-- | /mpoly_monomial_is_zero/ /exp/ /N/ 
-- 
-- Return 1 if @(exp, N)@ is zero.
foreign import ccall "mpoly.h mpoly_monomial_is_zero"
  mpoly_monomial_is_zero :: Ptr CULong -> CLong -> IO CInt

-- | /mpoly_monomial_equal/ /exp2/ /exp3/ /N/ 
-- 
-- Return 1 if the monomials @(exp2, N)@ and @(exp3, N)@ are equal.
foreign import ccall "mpoly.h mpoly_monomial_equal"
  mpoly_monomial_equal :: Ptr CULong -> Ptr CULong -> CLong -> IO CInt

-- | /mpoly_get_cmpmask/ /cmpmask/ /N/ /bits/ /mctx/ 
-- 
-- Get the mask @(cmpmask, N)@ for comparisons. @bits@ should be set to the
-- number of bits in the exponents to be compared. Any function that
-- compares monomials should use this comparison mask.
foreign import ccall "mpoly.h mpoly_get_cmpmask"
  mpoly_get_cmpmask :: Ptr CULong -> CLong -> CLong -> Ptr CMPolyCtx -> IO ()

-- | /mpoly_monomial_lt/ /exp2/ /exp3/ /N/ /cmpmask/ 
-- 
-- Return 1 if @(exp2, N)@ is less than @(exp3, N)@.
foreign import ccall "mpoly.h mpoly_monomial_lt"
  mpoly_monomial_lt :: Ptr CULong -> Ptr CULong -> CLong -> Ptr CULong -> IO CInt

-- | /mpoly_monomial_gt/ /exp2/ /exp3/ /N/ /cmpmask/ 
-- 
-- Return 1 if @(exp2, N)@ is greater than @(exp3, N)@.
foreign import ccall "mpoly.h mpoly_monomial_gt"
  mpoly_monomial_gt :: Ptr CULong -> Ptr CULong -> CLong -> Ptr CULong -> IO CInt

-- | /mpoly_monomial_cmp/ /exp2/ /exp3/ /N/ /cmpmask/ 
-- 
-- Return \(1\) if @(exp2, N)@ is greater than, \(0\) if it is equal to and
-- \(-1\) if it is less than @(exp3, N)@.
foreign import ccall "mpoly.h mpoly_monomial_cmp"
  mpoly_monomial_cmp :: Ptr CULong -> Ptr CULong -> CLong -> Ptr CULong -> IO CInt

-- Monomial divisibility -------------------------------------------------------

-- | /mpoly_monomial_divides/ /exp_ptr/ /exp2/ /exp3/ /N/ /mask/ 
-- 
-- Return 1 if the monomial @(exp3, N)@ divides @(exp2, N)@. If so set
-- @(exp_ptr, N)@ to the quotient monomial. The @mask@ is a word with the
-- high bit of each bit field set to 1. Assumes that @bits \<= FLINT_BITS@.
foreign import ccall "mpoly.h mpoly_monomial_divides"
  mpoly_monomial_divides :: Ptr CULong -> Ptr CULong -> Ptr CULong -> CLong -> CULong -> IO CInt

-- | /mpoly_monomial_divides_mp/ /exp_ptr/ /exp2/ /exp3/ /N/ /bits/ 
-- 
-- Return 1 if the monomial @(exp3, N)@ divides @(exp2, N)@. If so set
-- @(exp_ptr, N)@ to the quotient monomial. Assumes that
-- @bits >= FLINT_BITS@.
foreign import ccall "mpoly.h mpoly_monomial_divides_mp"
  mpoly_monomial_divides_mp :: Ptr CULong -> Ptr CULong -> Ptr CULong -> CLong -> CFBitCnt -> IO CInt

-- | /mpoly_monomial_divides1/ /exp_ptr/ /exp2/ /exp3/ /mask/ 
-- 
-- As per @mpoly_monomial_divides@ with @N = 1@.
foreign import ccall "mpoly.h mpoly_monomial_divides1"
  mpoly_monomial_divides1 :: Ptr CULong -> CULong -> CULong -> CULong -> IO CInt

-- | /mpoly_monomial_divides_tight/ /e1/ /e2/ /prods/ /num/ 
-- 
-- Return 1 if the monomial @e2@ divides the monomial @e1@, where the
-- monomials are stored using factorial representation. The array
-- @(prods, num)@ should consist of \(1\), \(b_1, b_1\times b_2, \ldots\),
-- where the \(b_i\) are the bases of the factorial number representation.
foreign import ccall "mpoly.h mpoly_monomial_divides_tight"
  mpoly_monomial_divides_tight :: CLong -> CLong -> Ptr CLong -> CLong -> IO CInt

-- Basic manipulation ----------------------------------------------------------

-- | /mpoly_exp_bits_required_ui/ /user_exp/ /mctx/ 
-- 
-- Returns the number of bits required to store @user_exp@ in packed
-- format. The returned number of bits includes space for a zeroed signed
-- bit.
foreign import ccall "mpoly.h mpoly_exp_bits_required_ui"
  mpoly_exp_bits_required_ui :: Ptr CULong -> Ptr CMPolyCtx -> IO CFBitCnt

-- | /mpoly_exp_bits_required_ffmpz/ /user_exp/ /mctx/ 
-- 
-- Returns the number of bits required to store @user_exp@ in packed
-- format. The returned number of bits includes space for a zeroed signed
-- bit.
foreign import ccall "mpoly.h mpoly_exp_bits_required_ffmpz"
  mpoly_exp_bits_required_ffmpz :: Ptr CFmpz -> Ptr CMPolyCtx -> IO CFBitCnt

-- | /mpoly_exp_bits_required_pfmpz/ /user_exp/ /mctx/ 
-- 
-- Returns the number of bits required to store @user_exp@ in packed
-- format. The returned number of bits includes space for a zeroed signed
-- bit.
foreign import ccall "mpoly.h mpoly_exp_bits_required_pfmpz"
  mpoly_exp_bits_required_pfmpz :: Ptr (Ptr CFmpz) -> Ptr CMPolyCtx -> IO CFBitCnt

-- | /mpoly_max_fields_ui_sp/ /max_fields/ /poly_exps/ /len/ /bits/ /mctx/ 
-- 
-- Compute the field-wise maximum of packed exponents from @poly_exps@ of
-- length @len@ and unpack the result into @max_fields@. The maximums are
-- assumed to fit a ulong.
foreign import ccall "mpoly.h mpoly_max_fields_ui_sp"
  mpoly_max_fields_ui_sp :: Ptr CULong -> Ptr CULong -> CLong -> CLong -> Ptr CMPolyCtx -> IO ()

-- | /mpoly_max_fields_fmpz/ /max_fields/ /poly_exps/ /len/ /bits/ /mctx/ 
-- 
-- Compute the field-wise maximum of packed exponents from @poly_exps@ of
-- length @len@ and unpack the result into @max_fields@.
foreign import ccall "mpoly.h mpoly_max_fields_fmpz"
  mpoly_max_fields_fmpz :: Ptr CFmpz -> Ptr CULong -> CLong -> CLong -> Ptr CMPolyCtx -> IO ()

-- | /mpoly_max_degrees_tight/ /max_exp/ /exps/ /len/ /prods/ /num/ 
-- 
-- Return an array of @num@ integers corresponding to the maximum degrees
-- of the exponents in the array of exponent vectors @(exps, len)@,
-- assuming that the exponent are packed in a factorial representation. The
-- array @(prods, num)@ should consist of \(1\), \(b_1\),
-- \(b_1\times b_2, \ldots\), where the \(b_i\) are the bases of the
-- factorial number representation. The results are stored in the array
-- @max_exp@, with the entry corresponding to the most significant base of
-- the factorial representation first in the array.
foreign import ccall "mpoly.h mpoly_max_degrees_tight"
  mpoly_max_degrees_tight :: Ptr CLong -> Ptr CULong -> CLong -> Ptr CLong -> CLong -> IO ()

-- | /mpoly_monomial_exists/ /index/ /poly_exps/ /exp/ /len/ /N/ /cmpmask/ 
-- 
-- Returns true if the given exponent vector @exp@ exists in the array of
-- exponent vectors @(poly_exps, len)@, otherwise, returns false. If the
-- exponent vector is found, its index into the array of exponent vectors
-- is returned. Otherwise, @index@ is set to the index where this exponent
-- could be inserted to preserve the ordering. The index can be in the
-- range @[0, len]@.
foreign import ccall "mpoly.h mpoly_monomial_exists"
  mpoly_monomial_exists :: Ptr CLong -> Ptr CULong -> Ptr CULong -> CLong -> CLong -> Ptr CULong -> IO CInt

-- | /mpoly_search_monomials/ /e_ind/ /e/ /e_score/ /t1/ /t2/ /t3/ /lower/ /upper/ /a/ /a_len/ /b/ /b_len/ /N/ /cmpmask/ 
-- 
-- Given packed exponent vectors @a@ and @b@, compute a packed exponent @e@
-- such that the number of monomials in the cross product @a@ X @b@ that
-- are less than or equal to @e@ is between @lower@ and @upper@. This
-- number is stored in @e_store@. If no such monomial exists, one is chosen
-- so that the number of monomials is as close as possible. This function
-- assumes that @1@ is the smallest monomial and needs three arrays @t1@,
-- @t2@, and @t3@ of the size as @a@ for workspace. The parameter @e_ind@
-- is set to one of @t1@, @t2@, and @t3@ and gives the locations of the
-- monomials in @a@ X @b@.
foreign import ccall "mpoly.h mpoly_search_monomials"
  mpoly_search_monomials :: Ptr (Ptr CLong) -> Ptr CULong -> Ptr CLong -> Ptr CLong -> Ptr CLong -> Ptr CLong -> CLong -> CLong -> Ptr CULong -> CLong -> Ptr CULong -> CLong -> CLong -> Ptr CULong -> IO ()

-- Setting and getting monomials -----------------------------------------------

-- | /mpoly_term_exp_fits_ui/ /exps/ /bits/ /n/ /mctx/ 
-- 
-- Return whether every entry of the exponent vector of index \(n\) in
-- @exps@ fits into a @ulong@.
foreign import ccall "mpoly.h mpoly_term_exp_fits_ui"
  mpoly_term_exp_fits_ui :: Ptr CULong -> CLong -> CLong -> Ptr CMPolyCtx -> IO CInt

-- | /mpoly_term_exp_fits_si/ /exps/ /bits/ /n/ /mctx/ 
-- 
-- Return whether every entry of the exponent vector of index \(n\) in
-- @exps@ fits into a @slong@.
foreign import ccall "mpoly.h mpoly_term_exp_fits_si"
  mpoly_term_exp_fits_si :: Ptr CULong -> CLong -> CLong -> Ptr CMPolyCtx -> IO CInt

-- | /mpoly_get_monomial_ui/ /exps/ /poly_exps/ /bits/ /mctx/ 
-- 
-- Convert the packed exponent @poly_exps@ of bit count @bits@ to a
-- monomial from the user\'s perspective. The exponents are assumed to fit
-- a ulong.
foreign import ccall "mpoly.h mpoly_get_monomial_ui"
  mpoly_get_monomial_ui :: Ptr CULong -> Ptr CULong -> CLong -> Ptr CMPolyCtx -> IO ()

-- | /mpoly_get_monomial_ffmpz/ /exps/ /poly_exps/ /bits/ /mctx/ 
-- 
-- Convert the packed exponent @poly_exps@ of bit count @bits@ to a
-- monomial from the user\'s perspective.
foreign import ccall "mpoly.h mpoly_get_monomial_ffmpz"
  mpoly_get_monomial_ffmpz :: Ptr CFmpz -> Ptr CULong -> CFBitCnt -> Ptr CMPolyCtx -> IO ()

-- | /mpoly_get_monomial_pfmpz/ /exps/ /poly_exps/ /bits/ /mctx/ 
-- 
-- Convert the packed exponent @poly_exps@ of bit count @bits@ to a
-- monomial from the user\'s perspective.
foreign import ccall "mpoly.h mpoly_get_monomial_pfmpz"
  mpoly_get_monomial_pfmpz :: Ptr (Ptr CFmpz) -> Ptr CULong -> CFBitCnt -> Ptr CMPolyCtx -> IO ()

-- | /mpoly_set_monomial_ui/ /exp1/ /exp2/ /bits/ /mctx/ 
-- 
-- Convert the user monomial @exp2@ to packed format using @bits@.
foreign import ccall "mpoly.h mpoly_set_monomial_ui"
  mpoly_set_monomial_ui :: Ptr CULong -> Ptr CULong -> CLong -> Ptr CMPolyCtx -> IO ()

-- | /mpoly_set_monomial_ffmpz/ /exp1/ /exp2/ /bits/ /mctx/ 
-- 
-- Convert the user monomial @exp2@ to packed format using @bits@.
foreign import ccall "mpoly.h mpoly_set_monomial_ffmpz"
  mpoly_set_monomial_ffmpz :: Ptr CULong -> Ptr CFmpz -> CFBitCnt -> Ptr CMPolyCtx -> IO ()

-- | /mpoly_set_monomial_pfmpz/ /exp1/ /exp2/ /bits/ /mctx/ 
-- 
-- Convert the user monomial @exp2@ to packed format using @bits@.
foreign import ccall "mpoly.h mpoly_set_monomial_pfmpz"
  mpoly_set_monomial_pfmpz :: Ptr CULong -> Ptr (Ptr CFmpz) -> CFBitCnt -> Ptr CMPolyCtx -> IO ()

-- Packing and unpacking monomials ---------------------------------------------

-- | /mpoly_pack_vec_ui/ /exp1/ /exp2/ /bits/ /nfields/ /len/ 
-- 
-- Packs a vector @exp2@ into {exp1} using a bit count of @bits@. No
-- checking is done to ensure that the vector actually fits into @bits@
-- bits. The number of fields in each vector is @nfields@ and the total
-- number of vectors to unpack is @len@.
foreign import ccall "mpoly.h mpoly_pack_vec_ui"
  mpoly_pack_vec_ui :: Ptr CULong -> Ptr CULong -> CLong -> CLong -> CLong -> IO ()

-- | /mpoly_pack_vec_fmpz/ /exp1/ /exp2/ /bits/ /nfields/ /len/ 
-- 
-- Packs a vector @exp2@ into {exp1} using a bit count of @bits@. No
-- checking is done to ensure that the vector actually fits into @bits@
-- bits. The number of fields in each vector is @nfields@ and the total
-- number of vectors to unpack is @len@.
foreign import ccall "mpoly.h mpoly_pack_vec_fmpz"
  mpoly_pack_vec_fmpz :: Ptr CULong -> Ptr CFmpz -> CFBitCnt -> CLong -> CLong -> IO ()

-- | /mpoly_unpack_vec_ui/ /exp1/ /exp2/ /bits/ /nfields/ /len/ 
-- 
-- Unpacks vector @exp2@ of bit count @bits@ into @exp1@. The number of
-- fields in each vector is @nfields@ and the total number of vectors to
-- unpack is @len@.
foreign import ccall "mpoly.h mpoly_unpack_vec_ui"
  mpoly_unpack_vec_ui :: Ptr CULong -> Ptr CULong -> CLong -> CLong -> CLong -> IO ()

-- | /mpoly_unpack_vec_fmpz/ /exp1/ /exp2/ /bits/ /nfields/ /len/ 
-- 
-- Unpacks vector @exp2@ of bit count @bits@ into @exp1@. The number of
-- fields in each vector is @nfields@ and the total number of vectors to
-- unpack is @len@.
foreign import ccall "mpoly.h mpoly_unpack_vec_fmpz"
  mpoly_unpack_vec_fmpz :: Ptr CFmpz -> Ptr CULong -> CFBitCnt -> CLong -> CLong -> IO ()

-- | /mpoly_repack_monomials/ /exps1/ /bits1/ /exps2/ /bits2/ /len/ /mctx/ 
-- 
-- Convert an array of length @len@ of exponents @exps2@ packed using bits
-- @bits2@ into an array @exps1@ using bits @bits1@. No checking is done to
-- ensure that the result fits into bits @bits1@.
foreign import ccall "mpoly.h mpoly_repack_monomials"
  mpoly_repack_monomials :: Ptr CULong -> CLong -> Ptr CULong -> CLong -> CLong -> Ptr CMPolyCtx -> IO ()

-- | /mpoly_pack_monomials_tight/ /exp1/ /exp2/ /len/ /mults/ /num/ /extra/ /bits/ 
-- 
-- Given an array of possibly packed exponent vectors @exp2@ of length
-- @len@, where each field of each exponent vector is packed into the given
-- number of bits, return the corresponding array of monomial vectors
-- packed using a factorial numbering scheme. The \"bases\" for the
-- factorial numbering scheme are given as an array of integers @mults@,
-- the first entry of which corresponds to the field of least significance
-- in each input exponent vector. Obviously the maximum exponent to be
-- packed must be less than the corresponding base in @mults@.
-- 
-- The number of multipliers is given by @num@. The code only considers
-- least significant @num@ fields of each exponent vectors and ignores the
-- rest. The number of ignored fields should be passed in @extras@.
foreign import ccall "mpoly.h mpoly_pack_monomials_tight"
  mpoly_pack_monomials_tight :: Ptr CULong -> Ptr CULong -> CLong -> Ptr CLong -> CLong -> CLong -> CLong -> IO ()

-- | /mpoly_unpack_monomials_tight/ /e1/ /e2/ /len/ /mults/ /num/ /extra/ /bits/ 
-- 
-- Given an array of exponent vectors @e2@ of length @len@ packed using a
-- factorial numbering scheme, unpack the monomials into an array @e1@ of
-- exponent vectors in standard packed format, where each field has the
-- given number of bits. The \"bases\" for the factorial numbering scheme
-- are given as an array of integers @mults@, the first entry of which
-- corresponds to the field of least significance in each exponent vector.
-- 
-- The number of multipliers is given by @num@. The code only considers
-- least significant @num@ fields of each exponent vectors and ignores the
-- rest. The number of ignored fields should be passed in @extras@.
foreign import ccall "mpoly.h mpoly_unpack_monomials_tight"
  mpoly_unpack_monomials_tight :: Ptr CULong -> Ptr CULong -> CLong -> Ptr CLong -> CLong -> CLong -> CLong -> IO ()

-- Chunking --------------------------------------------------------------------

-- | /mpoly_main_variable_terms1/ /i1/ /n1/ /exp1/ /l1/ /len1/ /k/ /num/ /bits/ 
-- 
-- Given an array of exponent vectors @(exp1, len1)@, each exponent vector
-- taking one word of space, with each exponent being packed into the given
-- number of bits, compute @l1@ starting offsets @i1@ and lengths @n1@
-- (which may be zero) to break the exponents into chunks. Each chunk
-- consists of exponents have the same degree in the main variable. The
-- index of the main variable is given by \(k\). The variables are indexed
-- from the variable of least significance, starting from \(0\). The value
-- @l1@ should be the degree in the main variable, plus one.
foreign import ccall "mpoly.h mpoly_main_variable_terms1"
  mpoly_main_variable_terms1 :: Ptr CLong -> Ptr CLong -> Ptr CULong -> CLong -> CLong -> CLong -> CLong -> CLong -> IO ()

-- Chained heap functions ------------------------------------------------------

-- | /_mpoly_heap_insert/ /heap/ /exp/ /x/ /heap_len/ /N/ /cmpmask/ 
-- 
-- Given a heap, insert a new node \(x\) corresponding to the given
-- exponent into the heap. Heap elements are ordered by the exponent
-- @(exp, N)@, with the largest element at the head of the heap. A pointer
-- to the current heap length must be passed in via @heap_len@. This will
-- be updated by the function. Note that the index 0 position in the heap
-- is not used, so the length is always one greater than the number of
-- elements.
foreign import ccall "mpoly.h _mpoly_heap_insert"
  _mpoly_heap_insert :: Ptr CMPolyHeap -> Ptr CULong -> Ptr () -> Ptr CLong -> CLong -> Ptr CULong -> IO CInt

-- | /_mpoly_heap_insert1/ /heap/ /exp/ /x/ /heap_len/ /maskhi/ 
-- 
-- As per @_mpoly_heap_insert@ except that @N = 1@, and
-- @maskhi = cmpmask[0]@.
foreign import ccall "mpoly.h _mpoly_heap_insert1"
 _mpoly_heap_insert1 :: Ptr CMPolyHeap1 -> CULong -> Ptr () -> Ptr CLong -> CULong -> IO ()

-- | /_mpoly_heap_pop/ /heap/ /heap_len/ /N/ /maskhi/ /masklo/ 
-- 
-- Pop the head of the heap. It is cast to a @void *@. A pointer to the
-- current heap length must be passed in via @heap_len@. This will be
-- updated by the function. Note that the index 0 position in the heap is
-- not used, so the length is always one greater than the number of
-- elements. The @maskhi@ and @masklo@ values are zero except for degrevlex
-- ordering, where they are as per the monomial comparison operations
-- above.
foreign import ccall "mpoly.h _mpoly_heap_pop"
  _mpoly_heap_pop :: Ptr CMPolyHeap -> Ptr CLong -> CLong -> CULong -> CULong -> IO ()

-- | /_mpoly_heap_pop1/ /heap/ /heap_len/ /maskhi/ 
-- 
-- As per @_mpoly_heap_pop1@ except that @N = 1@, and
-- @maskhi = cmpmask[0]@.
foreign import ccall "mpoly.h _mpoly_heap_pop1"
  _mpoly_heap_pop1 :: Ptr CMPolyHeap1 -> Ptr CLong -> CULong -> IO ()

