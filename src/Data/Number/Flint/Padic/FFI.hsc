{-# language
    CApiFFI
  , FlexibleInstances
  , ForeignFunctionInterface
  , MultiParamTypeClasses
  , TupleSections
  , TypeFamilies
  , ScopedTypeVariables
  #-}

module Data.Number.Flint.Padic.FFI (
  -- * p-adic numbers
  -- * Introduction
  -- The @padic_t@ data type represents elements of \(\mathbf{Q}_p\) to
  -- precision \(N\), stored in the form \(x = p^v u\) with
  -- \(u, v \in \mathbf{Z}\). Arithmetic operations can be carried out with
  -- respect to a context containing the prime number \(p\) and various
  -- pieces of pre-computed data.
  --
  -- Independent of the context, we consider a \(p\)-adic number x = u p^v to
  -- be in canonical form whenever either p nmid u or \(u = v = 0\), and we
  -- say it is reduced if, in addition, for non-zero \(u\),
  -- \(u \in (0, p^{N-v})\).
  --
  -- We briefly describe the interface:
  --
  -- The functions in this module expect arguments of type @padic_t@, and
  -- each variable carries its own precision. The functions have an interface
  -- that is similar to the MPFR functions. In particular, they have the same
  -- semantics, specified as follows: Compute the requested operation exactly
  -- and then reduce the result to the precision of the output variable.
  -- * Data structures
  -- A \(p\)-adic number of type @padic_t@ comprises a unit \(u\), a
  -- valuation \(v\), and a precision \(N\). We provide the following macros
  -- to access these fields, so that code can be developed somewhat
  -- independently from the underlying data layout.
  --
  -- ** p-adic numbers
  --
  -- | A p-adic number of type Padic comprises \(a\) unit \(u\), a valuation
  -- \(v\), and a precision \(N\). Create with `newPadic`.
    Padic (..)
  --
  -- | Haskell wrapper for the Flint `padic_t` structure. 
  , CPadic (..)
  , newPadic
  , withPadic
  , withNewPadic
  -- ** p-adic context
  --
  -- | A context object for p p-adic arithmetic contains data
  -- pertinent to p-adic computations, but which we choose not to store
  -- with each element individually. Currently, this includes the prime
  -- number \(p\) , its double inverse in case of word-sized primes,
  -- precomputed powers of \(p\) in the range given by min and max, and the
  -- printing mode. Create with `newPadicCtx`.
  , PadicCtx (..)
  --
  -- | Haskell wrapper for the Flint `padic_ctx_t`.
  , CPadicCtx (..)
  , newPadicCtx
  , withPadicCtx
  , withNewPadicCtx
  -- 
  , padic_unit
  , padic_get_val
  , padic_get_prec
  --
  , padic_ctx_init
  , padic_ctx_clear
  , _padic_ctx_pow_ui
  -- * Memory management
  , padic_init
  , padic_init2
  , padic_clear
  , _padic_canonicalise
  , _padic_reduce
  , padic_reduce
  , PadicPrintMode (..)
  , padic_terse
  , padic_series
  , padic_val_unit
  -- * Randomisation
  , padic_randtest
  , padic_randtest_not_zero
  , padic_randtest_int
  -- * Assignments and conversions
  , padic_set
  , padic_set_si
  , padic_set_ui
  , padic_set_fmpz
  , padic_set_fmpq
  , padic_set_mpz
  , padic_set_mpq
  , padic_get_fmpz
  , padic_get_fmpq
  , padic_get_mpz
  , padic_get_mpq
  , padic_swap
  , padic_zero
  , padic_one
  -- * Comparison
  , padic_is_zero
  , padic_is_one
  , padic_equal
  -- * Arithmetic operations
  , _padic_lifts_exps
  , _padic_lifts_pows
  , padic_add
  , padic_sub
  , padic_neg
  , padic_mul
  , padic_shift
  , padic_div
  , _padic_inv_precompute
  , _padic_inv_clear
  , _padic_inv_precomp
  , _padic_inv
  , padic_inv
  , padic_sqrt
  , padic_pow_si
  -- * Exponential
  , _padic_exp_bound
  , _padic_exp_rectangular
  , padic_exp
  , padic_exp_rectangular
  , padic_exp_balanced
  -- * Logarithm
  , _padic_log_bound
  , _padic_log
  , padic_log
  , padic_log_rectangular
  , padic_log_satoh
  , padic_log_balanced
  -- * Special functions
  , _padic_teichmuller
  , padic_teichmuller
  , padic_val_fac_ui_2
  , padic_val_fac_ui
  , padic_val_fac
  -- * Input and output
  , padic_get_str
  , _padic_fprint
  , _padic_print
  , padic_print
  , padic_debug
) where 

-- p-adic numbers --------------------------------------------------------------

import Control.Monad

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr, castPtr, nullPtr )
import Foreign.Storable
import Foreign.Marshal ( free, peekArray )

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpq

#include <flint/flint.h>
#include <flint/padic.h>

-- padic_t ---------------------------------------------------------------------

data Padic = Padic {-# UNPACK #-} !(ForeignPtr CPadic)
data CPadic = CPadic (Ptr CFmpz) CLong CLong

instance Storable CPadic where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size padic_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment padic_t}
  peek ptr = return CPadic
    `ap` #{peek padic_struct, u} ptr
    `ap` #{peek padic_struct, v} ptr
    `ap` #{peek padic_struct, N} ptr
  poke ptr (CPadic u v n) = do
    #{poke padic_struct, u} ptr u
    #{poke padic_struct, v} ptr v
    #{poke padic_struct, N} ptr n
  
-- | Create a new p-adic.
newPadic = do
  p <- mallocForeignPtr
  withForeignPtr p padic_init
  addForeignPtrFinalizer p_padic_clear p
  return $ Padic p

-- | Use p-adic.
{-# INLINE withPadic #-}
withPadic (Padic p) f = do
  withForeignPtr p $ \fp -> (Padic p,) <$> f fp

-- | Apply `f` to new p-adic.
{-# INLINE withNewPadic #-}
withNewPadic f = do
  x <- newPadic
  withPadic x f

-- padic_inv_t -----------------------------------------------------------------

data PadicInv = PadicInv {-# UNPACK #-} !(ForeignPtr CPadicInv)
type CPadicInv = CFlint PadicInv

instance Storable CPadicInv where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size padic_inv_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment padic_inv_t}
  peek = error "CPadicInv.peek: Not defined"
  poke = error "CPadicInv.poke: Not defined"

newPadicInv x n = do
  p <- mallocForeignPtr
  withForeignPtr p $ \p ->
    withFmpz x $ \x -> _padic_inv_precompute p x n
  addForeignPtrFinalizer p_padic_inv_clear p
  return $ PadicInv p
   
{-# INLINE withPadicInv #-}
withPadicInv (PadicInv p) f =
  withForeignPtr p $ \ fp -> (PadicInv p,) <$> f fp

-- padic_ctx_t -----------------------------------------------------------------

data PadicCtx = PadicCtx {-# UNPACK #-} !(ForeignPtr CPadicCtx)
data CPadicCtx =
  CPadicCtx (Ptr CFmpz) CDouble (Ptr CFmpz) CLong CLong PadicPrintMode

instance Storable CPadicCtx where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size padic_ctx_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment padic_ctx_t}
  peek ptr = do
    p    <- return $ castPtr ptr
    pinv <- #{peek padic_ctx_struct, pinv} ptr
    pow  <- #{peek padic_ctx_struct, pow } ptr
    min  <- #{peek padic_ctx_struct, min } ptr
    max  <- #{peek padic_ctx_struct, max } ptr
    mode <- #{peek padic_ctx_struct, mode} ptr
    return $ CPadicCtx p pinv pow min max mode
  poke = undefined

-- | Create p-adic context with prime \(p\), precomputed powers \(p^{min}\)
-- to \(p^{max}\) and `PadicPrintMode` @mode@.
newPadicCtx p min max mode = do
  ctx <- mallocForeignPtr
  withForeignPtr ctx $ \ctx ->
    withFmpz p $ \p -> 
      padic_ctx_init ctx p min max mode
  addForeignPtrFinalizer p_padic_ctx_clear ctx
  return $ PadicCtx ctx

-- | Use p-adic context.
{-# INLINE withPadicCtx #-}
withPadicCtx (PadicCtx p) f = do
  withForeignPtr p $ \fp -> (PadicCtx p,) <$> f fp

-- | Use new p-adic ctx
withNewPadicCtx p min max mode f = do
  ctx <- newPadicCtx p min max mode
  withPadicCtx ctx $ \ctx -> do f ctx
    
-- | /padic_unit/ /op/ 
-- 
-- Returns the unit part of the \(p\)-adic number as a FLINT integer, which
-- can be used as an operand for the @fmpz@ functions.
padic_unit :: Ptr CPadic -> IO (Ptr CFmpz)
padic_unit x = return $ castPtr x
  
-- | /padic_get_val/ /op/ 
-- 
-- Returns the valuation part of the \(p\)-adic number.
padic_get_val :: Ptr CPadic -> IO CLong
padic_get_val x = do
  CPadic u v n <- peek x
  return v
  
-- | /padic_get_prec/ /op/ 
-- 
-- Returns the precision of the \(p\)-adic number.
padic_get_prec :: Ptr CPadic -> IO CLong
padic_get_prec x = do
  CPadic u v n <- peek x
  return n

-- Context ---------------------------------------------------------------------

-- A context object for \(p\)-adic arithmetic contains data pertinent to
-- p-adic computations, but which we choose not to store with each element
-- individually. Currently, this includes the prime number \(p\), its
-- @double@ inverse in case of word-sized primes, precomputed powers of
-- \(p\) in the range given by @min@ and @max@, and the printing mode.
--
-- | /padic_ctx_init/ /ctx/ /p/ /min/ /max/ /mode/ 
-- 
-- Initialises the context @ctx@ with the given data.
-- 
-- Assumes that \(p\) is a prime. This is not verified but the subsequent
-- behaviour is undefined if \(p\) is a composite number.
-- 
-- Assumes that @min@ and @max@ are non-negative and that @min@ is at most
-- @max@, raising an @abort@ signal otherwise.
-- 
-- Assumes that the printing mode is one of @PADIC_TERSE@, @PADIC_SERIES@,
-- or @PADIC_VAL_UNIT@. Using the example \(x = 7^{-1} 12\) in
-- \(\mathbf{Q}_7\), these behave as follows:
-- 
-- In @PADIC_TERSE@ mode, a \(p\)-adic number is printed in the same way as
-- a rational number, e.g. @12\/7@.
-- 
-- In @PADIC_SERIES@ mode, a \(p\)-adic number is printed digit by digit,
-- e.g. @5*7^-1 + 1@.
-- 
-- In @PADIC_VAL_UNIT@ mode, a \(p\)-adic number is printed showing the
-- valuation and unit parts separately, e.g. @12*7^-1@.
foreign import ccall "padic.h padic_ctx_init"
  padic_ctx_init :: Ptr CPadicCtx -> Ptr CFmpz -> CLong -> CLong -> PadicPrintMode -> IO ()

newtype PadicPrintMode = PadicPrintMode {_PadicPrintMode :: CInt} deriving Eq

instance Storable PadicPrintMode where
  {-# INLINE sizeOf #-}
  sizeOf _ = sizeOf (undefined :: CInt)
  {-# INLINE alignment #-}
  alignment _ = alignment (undefined :: CInt)
  peek ptr = do
    v <- peek (castPtr ptr) :: IO CInt
    return $ PadicPrintMode v
  poke = undefined

instance Show PadicPrintMode where
  show mode
    | mode == padic_terse    = "PADIC_TERSE"
    | mode == padic_series   = "PADIC_SERIES"
    | mode == padic_val_unit = "PADIC_VAL_UNIT"
    | otherwise = "unknown print mode"
  
padic_terse    = PadicPrintMode #const PADIC_TERSE
padic_series   = PadicPrintMode #const PADIC_SERIES
padic_val_unit = PadicPrintMode #const PADIC_VAL_UNIT

-- | /padic_ctx_clear/ /ctx/ 
-- 
-- Clears all memory that has been allocated as part of the context.
foreign import ccall "padic.h padic_ctx_clear"
  padic_ctx_clear :: Ptr CPadicCtx -> IO ()

foreign import ccall "padic.h &padic_ctx_clear"
  p_padic_ctx_clear :: FunPtr (Ptr CPadicCtx -> IO ())

-- | /_padic_ctx_pow_ui/ /rop/ /e/ /ctx/ 
-- 
-- Sets @rop@ to \(p^e\) as efficiently as possible, where @rop@ is
-- expected to be an uninitialised @fmpz_t@.
-- 
-- If the return value is non-zero, it is the responsibility of the caller
-- to clear the returned integer.
foreign import ccall "padic.h _padic_ctx_pow_ui"
  _padic_ctx_pow_ui :: Ptr CFmpz -> CULong -> Ptr CPadicCtx -> IO CInt

-- Memory management -----------------------------------------------------------

-- | /padic_init/ /rop/ 
-- 
-- Initialises the \(p\)-adic number with the precision set to
-- @PADIC_DEFAULT_PREC@, which is defined as \(20\).
foreign import ccall "padic.h padic_init"
  padic_init :: Ptr CPadic -> IO ()

-- | /padic_init2/ /rop/ /N/ 
-- 
-- Initialises the \(p\)-adic number @rop@ with precision \(N\).
foreign import ccall "padic.h padic_init2"
  padic_init2 :: Ptr CPadic -> CLong -> IO ()

-- | /padic_clear/ /rop/ 
-- 
-- Clears all memory used by the \(p\)-adic number @rop@.
foreign import ccall "padic.h padic_clear"
  padic_clear :: Ptr CPadic -> IO ()

foreign import ccall "padic.h &padic_clear"
  p_padic_clear :: FunPtr (Ptr CPadic -> IO ())

-- | /_padic_canonicalise/ /rop/ /ctx/ 
-- 
-- Brings the \(p\)-adic number @rop@ into canonical form.
-- 
-- That is to say, ensures that either \(u = v = 0\) or \(p \nmid u\).
-- There is no reduction modulo a power of \(p\).
foreign import ccall "padic.h _padic_canonicalise"
  _padic_canonicalise :: Ptr CPadic -> Ptr CPadicCtx -> IO ()

-- | /_padic_reduce/ /rop/ /ctx/ 
-- 
-- Given a \(p\)-adic number @rop@ in canonical form, reduces it modulo
-- \(p^N\).
foreign import ccall "padic.h _padic_reduce"
  _padic_reduce :: Ptr CPadic -> Ptr CPadicCtx -> IO ()

-- | /padic_reduce/ /rop/ /ctx/ 
-- 
-- Ensures that the \(p\)-adic number @rop@ is reduced.
foreign import ccall "padic.h padic_reduce"
  padic_reduce :: Ptr CPadic -> Ptr CPadicCtx -> IO ()

-- Randomisation ---------------------------------------------------------------

-- | /padic_randtest/ /rop/ /state/ /ctx/ 
-- 
-- Sets @rop@ to a random \(p\)-adic number modulo \(p^N\) with valuation
-- in the range \([- \lceil N/10\rceil, N)\),
-- \([N - \lceil -N/10\rceil, N)\), or \([-10, 0)\) as \(N\) is positive,
-- negative or zero, whenever @rop@ is non-zero.
foreign import ccall "padic.h padic_randtest"
  padic_randtest :: Ptr CPadic -> Ptr CFRandState -> Ptr CPadicCtx -> IO ()

-- | /padic_randtest_not_zero/ /rop/ /state/ /ctx/ 
-- 
-- Sets @rop@ to a random non-zero \(p\)-adic number modulo \(p^N\), where
-- the range of the valuation is as for the function @padic_randtest@.
foreign import ccall "padic.h padic_randtest_not_zero"
  padic_randtest_not_zero :: Ptr CPadic -> Ptr CFRandState -> Ptr CPadicCtx -> IO ()

-- | /padic_randtest_int/ /rop/ /state/ /ctx/ 
-- 
-- Sets @rop@ to a random \(p\)-adic integer modulo \(p^N\).
-- 
-- Note that whenever \(N \leq 0\), @rop@ is set to zero.
foreign import ccall "padic.h padic_randtest_int"
  padic_randtest_int :: Ptr CPadic -> Ptr CFRandState -> Ptr CPadicCtx -> IO ()

-- Assignments and conversions -------------------------------------------------

-- All assignment functions set the value of @rop@ from @op@, reduced to
-- the precision of @rop@.
--
-- | /padic_set/ /rop/ /op/ /ctx/ 
-- 
-- Sets @rop@ to the \(p\)-adic number @op@.
foreign import ccall "padic.h padic_set"
  padic_set :: Ptr CPadic -> Ptr CPadic -> Ptr CPadicCtx -> IO ()

-- | /padic_set_si/ /rop/ /op/ /ctx/ 
-- 
-- Sets the \(p\)-adic number @rop@ to the @slong@ integer @op@.
foreign import ccall "padic.h padic_set_si"
  padic_set_si :: Ptr CPadic -> CLong -> Ptr CPadicCtx -> IO ()

-- | /padic_set_ui/ /rop/ /op/ /ctx/ 
-- 
-- Sets the \(p\)-adic number @rop@ to the @ulong@ integer @op@.
foreign import ccall "padic.h padic_set_ui"
  padic_set_ui :: Ptr CPadic -> CULong -> Ptr CPadicCtx -> IO ()

-- | /padic_set_fmpz/ /rop/ /op/ /ctx/ 
-- 
-- Sets the \(p\)-adic number @rop@ to the integer @op@.
foreign import ccall "padic.h padic_set_fmpz"
  padic_set_fmpz :: Ptr CPadic -> Ptr CFmpz -> Ptr CPadicCtx -> IO ()

-- | /padic_set_fmpq/ /rop/ /op/ /ctx/ 
-- 
-- Sets @rop@ to the rational @op@.
foreign import ccall "padic.h padic_set_fmpq"
  padic_set_fmpq :: Ptr CPadic -> Ptr CFmpq -> Ptr CPadicCtx -> IO ()

-- | /padic_set_mpz/ /rop/ /op/ /ctx/ 
-- 
-- Sets the \(p\)-adic number @rop@ to the MPIR integer @op@.
foreign import ccall "padic.h padic_set_mpz"
  padic_set_mpz :: Ptr CPadic -> Ptr CMpz -> Ptr CPadicCtx -> IO ()

-- | /padic_set_mpq/ /rop/ /op/ /ctx/ 
-- 
-- Sets @rop@ to the MPIR rational @op@.
foreign import ccall "padic.h padic_set_mpq"
  padic_set_mpq :: Ptr CPadic -> Ptr CMpq -> Ptr CPadicCtx -> IO ()

-- | /padic_get_fmpz/ /rop/ /op/ /ctx/ 
-- 
-- Sets the integer @rop@ to the exact \(p\)-adic integer @op@.
-- 
-- If @op@ is not a \(p\)-adic integer, raises an @abort@ signal.
foreign import ccall "padic.h padic_get_fmpz"
  padic_get_fmpz :: Ptr CFmpz -> Ptr CPadic -> Ptr CPadicCtx -> IO ()

-- | /padic_get_fmpq/ /rop/ /op/ /ctx/ 
-- 
-- Sets the rational @rop@ to the \(p\)-adic number @op@.
foreign import ccall "padic.h padic_get_fmpq"
  padic_get_fmpq :: Ptr CFmpq -> Ptr CPadic -> Ptr CPadicCtx -> IO ()

-- | /padic_get_mpz/ /rop/ /op/ /ctx/ 
-- 
-- Sets the MPIR integer @rop@ to the \(p\)-adic integer @op@.
-- 
-- If @op@ is not a \(p\)-adic integer, raises an @abort@ signal.
foreign import ccall "padic.h padic_get_mpz"
  padic_get_mpz :: Ptr CMpz -> Ptr CPadic -> Ptr CPadicCtx -> IO ()

-- | /padic_get_mpq/ /rop/ /op/ /ctx/ 
-- 
-- Sets the MPIR rational @rop@ to the value of @op@.
foreign import ccall "padic.h padic_get_mpq"
  padic_get_mpq :: Ptr CMpq -> Ptr CPadic -> Ptr CPadicCtx -> IO ()

-- | /padic_swap/ /op1/ /op2/ 
-- 
-- Swaps the two \(p\)-adic numbers @op1@ and @op2@.
-- 
-- Note that this includes swapping the precisions. In particular, this
-- operation is not equivalent to swapping @op1@ and @op2@ using
-- @padic_set@ and an auxiliary variable whenever the precisions of the two
-- elements are different.
foreign import ccall "padic.h padic_swap"
  padic_swap :: Ptr CPadic -> Ptr CPadic -> IO ()

-- | /padic_zero/ /rop/ 
-- 
-- Sets the \(p\)-adic number @rop@ to zero.
foreign import ccall "padic.h padic_zero"
  padic_zero :: Ptr CPadic -> IO ()

-- | /padic_one/ /rop/ 
-- 
-- Sets the \(p\)-adic number @rop@ to one, reduced modulo the precision of
-- @rop@.
foreign import ccall "padic.h padic_one"
  padic_one :: Ptr CPadic -> IO ()

-- Comparison ------------------------------------------------------------------

-- | /padic_is_zero/ /op/ 
-- 
-- Returns whether @op@ is equal to zero.
foreign import ccall "padic.h padic_is_zero"
  padic_is_zero :: Ptr CPadic -> IO CInt

-- | /padic_is_one/ /op/ 
-- 
-- Returns whether @op@ is equal to one, that is, whether \(u = 1\) and
-- \(v = 0\).
foreign import ccall "padic.h padic_is_one"
  padic_is_one :: Ptr CPadic -> IO CInt

-- | /padic_equal/ /op1/ /op2/ 
-- 
-- Returns whether @op1@ and @op2@ are equal, that is, whether
-- \(u_1 = u_2\) and \(v_1 = v_2\).
foreign import ccall "padic.h padic_equal"
  padic_equal :: Ptr CPadic -> Ptr CPadic -> IO CInt

-- Arithmetic operations -------------------------------------------------------

-- | /_padic_lifts_exps/ /n/ /N/ 
-- 
-- Given a positive integer \(N\) define the sequence
-- \(a_0 = N, a_1 = \lceil a_0/2\rceil, \dotsc, a_{n-1} = \lceil a_{n-2}/2\rceil = 1\).
-- Then \(n = \lceil\log_2 N\rceil + 1\).
-- 
-- This function sets \(n\) and allocates and returns the array \(a\).
foreign import ccall "padic.h _padic_lifts_exps"
  _padic_lifts_exps :: Ptr CLong -> CLong -> IO (Ptr CLong)

-- | /_padic_lifts_pows/ /pow/ /a/ /n/ /p/ 
-- 
-- Given an array \(a\) as computed above, this function computes the
-- corresponding powers of \(p\), that is, @pow[i]@ is equal to
-- \(p^{a_i}\).
foreign import ccall "padic.h _padic_lifts_pows"
  _padic_lifts_pows :: Ptr CFmpz -> Ptr CLong -> CLong -> Ptr CFmpz -> IO ()

-- | /padic_add/ /rop/ /op1/ /op2/ /ctx/ 
-- 
-- Sets @rop@ to the sum of @op1@ and @op2@.
foreign import ccall "padic.h padic_add"
  padic_add :: Ptr CPadic -> Ptr CPadic -> Ptr CPadic -> Ptr CPadicCtx -> IO ()

-- | /padic_sub/ /rop/ /op1/ /op2/ /ctx/ 
-- 
-- Sets @rop@ to the difference of @op1@ and @op2@.
foreign import ccall "padic.h padic_sub"
  padic_sub :: Ptr CPadic -> Ptr CPadic -> Ptr CPadic -> Ptr CPadicCtx -> IO ()

-- | /padic_neg/ /rop/ /op/ /ctx/ 
-- 
-- Sets @rop@ to the additive inverse of @op@.
foreign import ccall "padic.h padic_neg"
  padic_neg :: Ptr CPadic -> Ptr CPadic -> Ptr CPadicCtx -> IO ()

-- | /padic_mul/ /rop/ /op1/ /op2/ /ctx/ 
-- 
-- Sets @rop@ to the product of @op1@ and @op2@.
foreign import ccall "padic.h padic_mul"
  padic_mul :: Ptr CPadic -> Ptr CPadic -> Ptr CPadic -> Ptr CPadicCtx -> IO ()

-- | /padic_shift/ /rop/ /op/ /v/ /ctx/ 
-- 
-- Sets @rop@ to the product of @op@ and \(p^v\).
foreign import ccall "padic.h padic_shift"
  padic_shift :: Ptr CPadic -> Ptr CPadic -> CLong -> Ptr CPadicCtx -> IO ()

-- | /padic_div/ /rop/ /op1/ /op2/ /ctx/ 
-- 
-- Sets @rop@ to the quotient of @op1@ and @op2@.
foreign import ccall "padic.h padic_div"
  padic_div :: Ptr CPadic -> Ptr CPadic -> Ptr CPadic -> Ptr CPadicCtx -> IO ()

-- | /_padic_inv_precompute/ /S/ /p/ /N/ 
-- 
-- Pre-computes some data and allocates temporary space for \(p\)-adic
-- inversion using Hensel lifting.
foreign import ccall "padic.h _padic_inv_precompute"
  _padic_inv_precompute :: Ptr CPadicInv -> Ptr CFmpz -> CLong -> IO ()

-- | /_padic_inv_clear/ /S/ 
-- 
-- Frees the memory used by \(S\).
foreign import ccall "padic.h _padic_inv_clear"
  _padic_inv_clear :: Ptr CPadicInv -> IO ()

foreign import ccall "padic.h &_padic_inv_clear"
  p_padic_inv_clear :: FunPtr (Ptr CPadicInv -> IO ())

-- | /_padic_inv_precomp/ /rop/ /op/ /S/ 
-- 
-- Sets @rop@ to the inverse of @op@ modulo \(p^N\), assuming that @op@ is
-- a unit and \(N \geq 1\).
-- 
-- In the current implementation, allows aliasing, but this might change in
-- future versions.
-- 
-- Uses some data \(S\) precomputed by calling the function
-- @_padic_inv_precompute@. Note that this object is not declared @const@
-- and in fact it carries a field providing temporary work space. This
-- allows repeated calls of this function to avoid repeated memory
-- allocations, as used e.g. by the function @padic_log@.
foreign import ccall "padic.h _padic_inv_precomp"
  _padic_inv_precomp :: Ptr CFmpz -> Ptr CFmpz -> Ptr CPadicInv -> IO ()

-- | /_padic_inv/ /rop/ /op/ /p/ /N/ 
-- 
-- Sets @rop@ to the inverse of @op@ modulo \(p^N\), assuming that @op@ is
-- a unit and \(N \geq 1\).
-- 
-- In the current implementation, allows aliasing, but this might change in
-- future versions.
foreign import ccall "padic.h _padic_inv"
  _padic_inv :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- | /padic_inv/ /rop/ /op/ /ctx/ 
-- 
-- Computes the inverse of @op@ modulo \(p^N\).
-- 
-- Suppose that @op@ is given as \(x = u p^v\). Raises an @abort@ signal if
-- \(v < -N\). Otherwise, computes the inverse of \(u\) modulo \(p^{N+v}\).
-- 
-- This function employs Hensel lifting of an inverse modulo \(p\).
foreign import ccall "padic.h padic_inv"
  padic_inv :: Ptr CPadic -> Ptr CPadic -> Ptr CPadicCtx -> IO ()

-- | /padic_sqrt/ /rop/ /op/ /ctx/ 
-- 
-- Returns whether @op@ is a \(p\)-adic square. If this is the case, sets
-- @rop@ to one of the square roots; otherwise, the value of @rop@ is
-- undefined.
-- 
-- We have the following theorem:
-- 
-- Let \(u \in \mathbf{Z}^{\times}\). Then \(u\) is a square if and only if
-- \(u \bmod p\) is a square in \(\mathbf{Z} / p \mathbf{Z}\), for
-- \(p > 2\), or if \(u \bmod 8\) is a square in
-- \(\mathbf{Z} / 8 \mathbf{Z}\), for \(p = 2\).
foreign import ccall "padic.h padic_sqrt"
  padic_sqrt :: Ptr CPadic -> Ptr CPadic -> Ptr CPadicCtx -> IO CInt

-- | /padic_pow_si/ /rop/ /op/ /e/ /ctx/ 
-- 
-- Sets @rop@ to @op@ raised to the power \(e\), which is defined as one
-- whenever \(e = 0\).
-- 
-- Assumes that some computations involving \(e\) and the valuation of @op@
-- do not overflow in the @slong@ range.
-- 
-- Note that if the input \(x = p^v u\) is defined modulo \(p^N\) then
-- \(x^e = p^{ev} u^e\) is defined modulo \(p^{N + (e - 1) v}\), which is a
-- precision loss in case \(v < 0\).
foreign import ccall "padic.h padic_pow_si"
  padic_pow_si :: Ptr CPadic -> Ptr CPadic -> CLong -> Ptr CPadicCtx -> IO ()

-- Exponential -----------------------------------------------------------------

-- | /_padic_exp_bound/ /v/ /N/ /p/ 
-- 
-- Returns an integer \(i\) such that for all \(j \geq i\) we have
-- \(\operatorname{ord}_p(x^j / j!) \geq N\), where
-- \(\operatorname{ord}_p(x) = v\).
-- 
-- When \(p\) is a word-sized prime, returns
-- \(\left\lceil \frac{(p-1)N - 1}{(p-1)v - 1}\right\rceil\). Otherwise,
-- returns \(\lceil N/v\rceil\).
-- 
-- Assumes that \(v < N\). Moreover, \(v\) has to be at least \(2\) or
-- \(1\), depending on whether \(p\) is \(2\) or odd.
foreign import ccall "padic.h _padic_exp_bound"
  _padic_exp_bound :: CLong -> CLong -> Ptr CFmpz -> IO CLong

-- | /_padic_exp_rectangular/ /rop/ /u/ /v/ /p/ /N/ 
-- 
-- Sets @rop@ to the \(p\)-exponential function evaluated at \(x = p^v u\),
-- reduced modulo \(p^N\).
-- 
-- Assumes that \(x \neq 0\), that \(\operatorname{ord}_p(x) < N\) and that
-- \(\exp(x)\) converges, that is, that \(\operatorname{ord}_p(x)\) is at
-- least \(2\) or \(1\) depending on whether the prime \(p\) is \(2\) or
-- odd.
-- 
-- Supports aliasing between @rop@ and \(u\).
foreign import ccall "padic.h _padic_exp_rectangular"
  _padic_exp_rectangular :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> IO ()

-- | /padic_exp/ /y/ /x/ /ctx/ 
-- 
-- Returns whether the \(p\)-adic exponential function converges at the
-- \(p\)-adic number \(x\), and if so sets \(y\) to its value.
-- 
-- The \(p\)-adic exponential function is defined by the usual series
-- 
-- \[`\]
-- \[\exp_p(x) = \sum_{i = 0}^{\infty} \frac{x^i}{i!}\]
-- 
-- but this only converges only when
-- \(\operatorname{ord}_p(x) > 1 / (p - 1)\). For elements
-- \(x \in \mathbf{Q}_p\), this means that
-- \(\operatorname{ord}_p(x) \geq 1\) when \(p \geq 3\) and
-- \(\operatorname{ord}_2(x) \geq 2\) when \(p = 2\).
foreign import ccall "padic.h padic_exp"
  padic_exp :: Ptr CPadic -> Ptr CPadic -> Ptr CPadicCtx -> IO CInt

-- | /padic_exp_rectangular/ /y/ /x/ /ctx/ 
-- 
-- Returns whether the \(p\)-adic exponential function converges at the
-- \(p\)-adic number \(x\), and if so sets \(y\) to its value.
-- 
-- Uses a rectangular splitting algorithm to evaluate the series expression
-- of \(\exp(x) \bmod{p^N}\).
foreign import ccall "padic.h padic_exp_rectangular"
  padic_exp_rectangular :: Ptr CPadic -> Ptr CPadic -> Ptr CPadicCtx -> IO CInt

-- | /padic_exp_balanced/ /y/ /x/ /ctx/ 
-- 
-- Returns whether the \(p\)-adic exponential function converges at the
-- \(p\)-adic number \(x\), and if so sets \(y\) to its value.
-- 
-- Uses a balanced approach, balancing the size of chunks of \(x\) with the
-- valuation and hence the rate of convergence, which results in a
-- quasi-linear algorithm in \(N\), for fixed \(p\).
foreign import ccall "padic.h padic_exp_balanced"
  padic_exp_balanced :: Ptr CPadic -> Ptr CPadic -> Ptr CPadicCtx -> IO CInt

-- Logarithm -------------------------------------------------------------------

-- | /_padic_log_bound/ /v/ /N/ /p/ 
-- 
-- Returns \(b\) such that for all \(i \geq b\) we have
-- 
-- \[`\]
-- \[i v - \operatorname{ord}_p(i) \geq N\]
-- 
-- where \(v \geq 1\).
-- 
-- Assumes that \(1 \leq v < N\) or \(2 \leq v < N\) when \(p\) is odd or
-- \(p = 2\), respectively, and also that \(N < 2^{f-2}\) where \(f\) is
-- @FLINT_BITS@.
foreign import ccall "padic.h _padic_log_bound"
  _padic_log_bound :: CLong -> CLong -> Ptr CFmpz -> IO CLong

-- | /_padic_log/ /z/ /y/ /v/ /p/ /N/ 
-- 
-- Computes
-- 
-- \[`\]
-- \[z = - \sum_{i = 1}^{\infty} \frac{y^i}{i} \pmod{p^N},\]
-- 
-- reduced modulo \(p^N\).
-- 
-- Note that this can be used to compute the \(p\)-adic logarithm via the
-- equation
-- 
-- \[`\]
-- \[\begin{aligned}
-- \log(x) & = \sum_{i=1}^{\infty} (-1)^{i-1} \frac{(x-1)^i}{i} \\
--         & = - \sum_{i=1}^{\infty} \frac{(1-x)^i}{i}.
-- \end{aligned}\]
-- 
-- Assumes that \(y = 1 - x\) is non-zero and that
-- \(v = \operatorname{ord}_p(y)\) is at least \(1\) when \(p\) is odd and
-- at least \(2\) when \(p = 2\) so that the series converges.
-- 
-- Assumes that \(v < N\), and hence in particular \(N \geq 2\).
-- 
-- Does not support aliasing between \(y\) and \(z\).
foreign import ccall "padic.h _padic_log"
  _padic_log :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> IO ()

-- | /padic_log/ /rop/ /op/ /ctx/ 
-- 
-- Returns whether the \(p\)-adic logarithm function converges at the
-- \(p\)-adic number @op@, and if so sets @rop@ to its value.
-- 
-- The \(p\)-adic logarithm function is defined by the usual series
-- 
-- \[`\]
-- \[\log_p(x) = \sum_{i=1}^{\infty} (-1)^{i-1} \frac{(x-1)^i}{i}\]
-- 
-- but this only converges when \(\operatorname{ord}_p(x - 1)\) is at least
-- \(2\) or \(1\) when \(p = 2\) or \(p > 2\), respectively.
foreign import ccall "padic.h padic_log"
  padic_log :: Ptr CPadic -> Ptr CPadic -> Ptr CPadicCtx -> IO CInt

-- | /padic_log_rectangular/ /rop/ /op/ /ctx/ 
-- 
-- Returns whether the \(p\)-adic logarithm function converges at the
-- \(p\)-adic number @op@, and if so sets @rop@ to its value.
-- 
-- Uses a rectangular splitting algorithm to evaluate the series expression
-- of \(\log(x) \bmod{p^N}\).
foreign import ccall "padic.h padic_log_rectangular"
  padic_log_rectangular :: Ptr CPadic -> Ptr CPadic -> Ptr CPadicCtx -> IO CInt

-- | /padic_log_satoh/ /rop/ /op/ /ctx/ 
-- 
-- Returns whether the \(p\)-adic logarithm function converges at the
-- \(p\)-adic number @op@, and if so sets @rop@ to its value.
-- 
-- Uses an algorithm based on a result of Satoh, Skjernaa and Taguchi that
-- \(\operatorname{ord}_p\bigl(a^{p^k} - 1\bigr) > k\), which implies that
-- 
-- \[`\]
-- \[\log(a) \equiv p^{-k} \Bigl( \log\bigl(a^{p^k}\bigr) \pmod{p^{N+k}} 
--                                                   \Bigr) \pmod{p^N}.\]
foreign import ccall "padic.h padic_log_satoh"
  padic_log_satoh :: Ptr CPadic -> Ptr CPadic -> Ptr CPadicCtx -> IO CInt

-- | /padic_log_balanced/ /rop/ /op/ /ctx/ 
-- 
-- Returns whether the \(p\)-adic logarithm function converges at the
-- \(p\)-adic number @op@, and if so sets @rop@ to its value.
foreign import ccall "padic.h padic_log_balanced"
  padic_log_balanced :: Ptr CPadic -> Ptr CPadic -> Ptr CPadicCtx -> IO CInt

-- Special functions -----------------------------------------------------------

-- | /_padic_teichmuller/ /rop/ /op/ /p/ /N/ 
-- 
-- Computes the Teichm\"uller lift of the \(p\)-adic unit @op@, assuming
-- that \(N \geq 1\).
-- 
-- Supports aliasing between @rop@ and @op@.
foreign import ccall "padic.h _padic_teichmuller"
  _padic_teichmuller :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- | /padic_teichmuller/ /rop/ /op/ /ctx/ 
-- 
-- Computes the Teichm\"uller lift of the \(p\)-adic unit @op@.
-- 
-- If @op@ is a \(p\)-adic integer divisible by \(p\), sets @rop@ to zero,
-- which satisfies \(t^p - t = 0\), although it is clearly not a
-- \((p-1)\)-st root of unity.
-- 
-- If @op@ has negative valuation, raises an @abort@ signal.
foreign import ccall "padic.h padic_teichmuller"
  padic_teichmuller :: Ptr CPadic -> Ptr CPadic -> Ptr CPadicCtx -> IO ()

-- | /padic_val_fac_ui_2/ /n/ 
-- 
-- Computes the \(2\)-adic valuation of \(n!\).
-- 
-- Note that since \(n\) fits into an @ulong@, so does
-- \(\operatorname{ord}_2(n!)\) since
-- \(\operatorname{ord}_2(n!) \leq (n - 1) / (p - 1) = n - 1\).
foreign import ccall "padic.h padic_val_fac_ui_2"
  padic_val_fac_ui_2 :: CULong -> IO CULong

-- | /padic_val_fac_ui/ /n/ /p/ 
-- 
-- Computes the \(p\)-adic valuation of \(n!\).
-- 
-- Note that since \(n\) fits into an @ulong@, so does
-- \(\operatorname{ord}_p(n!)\) since
-- \(\operatorname{ord}_p(n!) \leq (n - 1) / (p - 1)\).
foreign import ccall "padic.h padic_val_fac_ui"
  padic_val_fac_ui :: CULong -> Ptr CFmpz -> IO CULong

-- | /padic_val_fac/ /rop/ /op/ /p/ 
-- 
-- Sets @rop@ to the \(p\)-adic valuation of the factorial of @op@,
-- assuming that @op@ is non-negative.
foreign import ccall "padic.h padic_val_fac"
  padic_val_fac :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- Input and output ------------------------------------------------------------

-- | /padic_get_str/ /str/ /op/ /ctx/ 
-- 
-- Returns the string representation of the \(p\)-adic number @op@
-- according to the printing mode set in the context.
-- 
-- If @str@ is @NULL@ then a new block of memory is allocated and a pointer
-- to this is returned. Otherwise, it is assumed that the string @str@ is
-- large enough to hold the representation and it is also the return value.
foreign import ccall "padic.h padic_get_str"
  padic_get_str :: CString -> Ptr CPadic -> Ptr CPadicCtx -> IO CString

-- | /_padic_fprint/ /file/ /u/ /v/ /ctx/ 
-- 
-- Prints the string representation of the \(p\)-adic number @op@ to the
-- stream @file@.
-- 
-- In the current implementation, always returns \(1\).
foreign import ccall "padic.h _padic_fprint"
  _padic_fprint :: Ptr CFile -> Ptr CFmpz -> CLong -> Ptr CPadicCtx -> IO CInt

-- | /_padic_print/ /u/ /v/ /ctx/ 
-- 
-- Prints the string representation of the \(p\)-adic number @op@ to the
-- stream @stdout@.
-- 
-- In the current implementation, always returns \(1\).
foreign import ccall "padic.h _padic_print"
  _padic_print :: Ptr CFmpz -> CLong -> Ptr CPadicCtx -> IO CInt

-- | /padic_print/ /op/ /ctx/ 
-- 
-- Prints the string representation of the \(p\)-adic number @op@ to the
-- stream @stdout@.
-- 
-- In the current implementation, always returns \(1\).
padic_print :: Ptr CPadic -> Ptr CPadicCtx -> IO CInt
padic_print x ctx = printCStr (flip (padic_get_str nullPtr) ctx) x where

-- | /padic_debug/ /op/ 
-- 
-- Prints debug information about @op@ to the stream @stdout@, in the
-- format @\"(u v N)\"@.
foreign import ccall "padic.h padic_debug"
  padic_debug :: Ptr CPadic -> IO ()

