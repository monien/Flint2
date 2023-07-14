module Data.Number.Flint.Qadic.FFI (
  -- * Unramified extensions over p-adic numbers
  -- 
  -- ** q-adic numbers 
  -- | Data structures
  -- We represent an element of the
  -- extension \(\mathbb{Q}_q \cong \mathbb{Q}_p[X]\ /\ f(X)\)
  -- as a polynomial in \(\mathbb{Q}_p[X]\) of degree less than \(\deg(f)\).
  -- As such, @qadic_struct@ and @qadic_t@ are typedef\'ed as
  -- @padic_poly_struct@ and @padic_poly_t@.
    Qadic (..)
  , CQadic (..)
  , newQadic
  , withQadic
  , withNewQadic
  -- * q-adic context
  --
  -- | Context
  -- We represent an unramified extension of \(\mathbb{Q}_p\) 
  -- via \(\mathbb{Q}_q \cong \mathbb{Q}_p[X]\ /\ f(X)\), 
  -- where \(f \in \mathbb{Q}_p[X]\) is a monic, irreducible polynomial which we
  -- assume to actually be in \(\mathbb{Z}[X]\). The first field in the
  -- context structure is a \(p\)-adic context struct @pctx@, which contains
  -- data about the prime \(p\), precomputed powers, the printing mode etc.
  -- The polynomial \(f\) is represented as a sparse polynomial using two
  -- arrays \(j\) and \(a\) of length @len@,
  -- where \(f(X) = \sum_{i} a_{i} X^{j_{i}}\).
  -- We also assume that the array \(j\) is sorted in ascending
  -- order. We choose this data structure to improve reduction modulo \(f(X)\)
  -- in \(\mathbb{Q}_p[X]\), assuming a sparse polynomial \(f(X)\)
  -- is chosen. The field @var@ contains the name of a generator of the
  -- extension, which is used when printing the elements.
  , QadicCtx (..)
  , CQadicCtx (..)
  , newQadicCtx
  , newQadicCtxConway
  , withQadicCtx
  , withNewQadicCtx
  , withNewQadicCtxConway
  , qadic_ctx_init
  , qadic_ctx_init_conway
  , qadic_ctx_clear
  , qadic_ctx_degree
  , qadic_ctx_print
  -- * Memory management
  , qadic_init
  , qadic_init2
  , qadic_clear
  , _fmpz_poly_reduce
  , _fmpz_mod_poly_reduce
  , qadic_reduce
  -- * Properties
  , qadic_val
  , qadic_prec
  -- * Randomisation
  , qadic_randtest
  , qadic_randtest_not_zero
  , qadic_randtest_val
  , qadic_randtest_int
  -- * Assignments and conversions
  , qadic_set
  , qadic_zero
  , qadic_one
  , qadic_gen
  , qadic_set_ui
  , qadic_get_padic
  -- * Comparison
  , qadic_is_zero
  , qadic_is_one
  , qadic_equal
  -- * Basic arithmetic
  , qadic_add
  , qadic_sub
  , qadic_neg
  , qadic_mul
  , _qadic_inv
  , qadic_inv
  , _qadic_pow
  , qadic_pow
  -- * Square root
  , qadic_sqrt
  -- * Special functions
  , _qadic_exp_rectangular
  , qadic_exp_rectangular
  , _qadic_exp_balanced
  , qadic_exp_balanced
  , _qadic_exp
  , qadic_exp
  , _qadic_log_rectangular
  , qadic_log_rectangular
  , _qadic_log_balanced
  , qadic_log_balanced
  , _qadic_log
  , qadic_log
  , _qadic_frobenius_a
  , _qadic_frobenius
  , qadic_frobenius
  , _qadic_teichmuller
  , qadic_teichmuller
  , _qadic_trace
  , _qadic_norm
  , qadic_norm
  , qadic_norm_analytic
  , qadic_norm_resultant
  -- * Output
  , qadic_fprint_pretty
  , qadic_print_pretty
) where

-- unramified extensions over p-adic numbers -----------------------------------

import Control.Monad

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr, castPtr )
import Foreign.Storable
import Foreign.Marshal ( free )
import Foreign.Marshal.Array

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Vec
import Data.Number.Flint.Fmpq
import Data.Number.Flint.Padic
import Data.Number.Flint.Padic.Poly

#include <flint/flint.h>
#include <flint/qadic.h>

-- qadic_t --------------------------------------------------------------------

data Qadic = Qadic {-# UNPACK #-} !(ForeignPtr CQadic)
type CQadic = CPadicPoly

-- | Create new q-adic
newQadic = do
  x <- mallocForeignPtr
  withForeignPtr x qadic_init
  addForeignPtrFinalizer p_qadic_clear x
  return $ Qadic x

-- | Use q-adic
{-# INLINE withQadic #-}
withQadic (Qadic x) f = do
  withForeignPtr x $ \px -> f px >>= return . (Qadic x,)

-- | Apply `f` to new q-adic
{-# INLINE withNewQadic #-}
withNewQadic f = do
  x <- newQadic
  withQadic x f

-- qadic_ctx_t ----------------------------------------------------------------

data QadicCtx = QadicCtx {-# UNPACK #-} !(ForeignPtr CQadicCtx)
data CQadicCtx = CQadicCtx (Ptr CPadicCtx) (Ptr CFmpz) (Ptr CLong) CLong CString

instance Storable CQadicCtx where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size qadic_ctx_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment qadic_ctx_t}
  peek ptr = return CQadicCtx
    `ap` (return $ castPtr ptr)
    `ap` #{peek qadic_ctx_struct, a   } ptr
    `ap` #{peek qadic_ctx_struct, j   } ptr
    `ap` #{peek qadic_ctx_struct, len } ptr
    `ap` #{peek qadic_ctx_struct, var } ptr
  poke = undefined

{-# INLINE _newQadicCtx #-}
_newQadicCtx f p d min max var mode = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> do
    withFmpz p $ \p -> do
      withCString var $ \var -> do
        f x p d min max var mode
  addForeignPtrFinalizer p_qadic_ctx_clear x
  return $ QadicCtx x

-- | Create q-adic context with prime \(p\), extension \(d\),
-- precomputed powers \(p^{min}\) to \(p^{max}\) and `PadicPrintMode`
-- @mode@. Initialized with `qadic_ctx_init`.
newQadicCtx = _newQadicCtx qadic_ctx_init
-- | Create q-adic context with prime \(p\), extension \(d\),
-- precomputed powers \(p^{min}\) to \(p^{max}\) and `PadicPrintMode`
-- @mode@. Initialized with `qadic_ctx_init_conway`.
newQadicCtxConway = _newQadicCtx qadic_ctx_init_conway

-- | Use q-adic context
{-# INLINE withQadicCtx #-}
withQadicCtx (QadicCtx x) f = do
  withForeignPtr x $ \px -> f px >>= return . (QadicCtx x,)

_withNewQadicCtx initialize p d min max var mode f = do
  x <- initialize p d min max var mode
  withQadicCtx x f

withNewQadicCtx       = _withNewQadicCtx newQadicCtx
withNewQadicCtxConway = _withNewQadicCtx newQadicCtxConway

--------------------------------------------------------------------------------

-- | /qadic_ctx_init/ /ctx/ /p/ /d/ /min/ /max/ /var/ /mode/ 
-- 
-- Initialises the context @ctx@ with prime \(p\), extension degree \(d\),
-- variable name @var@ and printing mode @mode@. The defining polynomial is
-- chosen as a Conway polynomial if possible and otherwise as a random
-- sparse polynomial.
-- 
-- Stores powers of \(p\) with exponents between @min@ (inclusive) and
-- @max@ exclusive. Assumes that @min@ is at most @max@.
-- 
-- Assumes that \(p\) is a prime.
-- 
-- Assumes that the string @var@ is a null-terminated string of length at
-- least one.
-- 
-- Assumes that the printing mode is one of @PADIC_TERSE@, @PADIC_SERIES@,
-- or @PADIC_VAL_UNIT@.
-- 
-- This function also carries out some relevant precomputation for
-- arithmetic in \(\mathbb{Q}_p / (p^N)\) such as powers of \(p\) close to
-- \(p^N\).
foreign import ccall "qadic.h qadic_ctx_init"
  qadic_ctx_init :: Ptr CQadicCtx -> Ptr CFmpz -> CLong -> CLong -> CLong -> CString -> PadicPrintMode -> IO ()

-- | /qadic_ctx_init_conway/ /ctx/ /p/ /d/ /min/ /max/ /var/ /mode/ 
-- 
-- Initialises the context @ctx@ with prime \(p\), extension degree \(d\),
-- variable name @var@ and printing mode @mode@. The defining polynomial is
-- chosen as a Conway polynomial, hence has restrictions on the prime and
-- the degree.
-- 
-- Stores powers of \(p\) with exponents between @min@ (inclusive) and
-- @max@ exclusive. Assumes that @min@ is at most @max@.
-- 
-- Assumes that \(p\) is a prime.
-- 
-- Assumes that the string @var@ is a null-terminated string of length at
-- least one.
-- 
-- Assumes that the printing mode is one of @PADIC_TERSE@, @PADIC_SERIES@,
-- or @PADIC_VAL_UNIT@.
-- 
-- This function also carries out some relevant precomputation for
-- arithmetic in \(\mathbb{Q}_p / (p^N)\) such as powers of \(p\) close to
-- \(p^N\).
foreign import ccall "qadic.h qadic_ctx_init_conway"
  qadic_ctx_init_conway :: Ptr CQadicCtx -> Ptr CFmpz -> CLong -> CLong -> CLong -> CString -> PadicPrintMode -> IO ()

-- | /qadic_ctx_clear/ /ctx/ 
-- 
-- Clears all memory that has been allocated as part of the context.
foreign import ccall "qadic.h qadic_ctx_clear"
  qadic_ctx_clear :: Ptr CQadicCtx -> IO ()

foreign import ccall "qadic.h &qadic_ctx_clear"
  p_qadic_ctx_clear :: FunPtr (Ptr CQadicCtx -> IO ())

-- | /qadic_ctx_degree/ /ctx/ 
-- 
-- Returns the extension degree.
foreign import ccall "qadic.h qadic_ctx_degree"
  qadic_ctx_degree :: Ptr CQadicCtx -> IO CLong

-- | /qadic_ctx_print/ /ctx/ 
-- 
-- Prints the data from the given context.
qadic_ctx_print ctx = do
  CQadicCtx pctx a j len var <- peek ctx
  CPadicCtx p _ _ _ _ mode <- peek pctx
  putStr "p    = "
  fmpz_print p
  putStr "\n"
  d <- peek (j `advancePtr` (fromIntegral len - 1))
  putStrLn $ "d    = " ++ show d
  putStr "f(X) = "
  fmpz_print a
  forM_ [1 .. fromIntegral len - 1] $ \k -> do
    i <- peek (j `advancePtr` k)
    flag1 <- fmpz_is_zero (a `advancePtr` k)
    case flag1 of 
      1 -> return ()
      _ -> do
        putStr " + " 
        flag <- fmpz_is_one (a `advancePtr` k)
        case flag of 
          1 -> return ()
          _ -> do
            fmpz_print (a `advancePtr` k)
            putStr "*"
        putStr "X"
        when ( i /= 1 ) $ putStr $ "^" ++ show i

-- Memory management -----------------------------------------------------------

-- | /qadic_init/ /rop/ 
-- 
-- Initialises the element @rop@, setting its value to \(0\).
foreign import ccall "qadic.h qadic_init"
  qadic_init :: Ptr CQadic -> IO ()

-- | /qadic_init2/ /rop/ /prec/ 
-- 
-- Initialises the element @rop@ with the given output precision, setting
-- the value to \(0\).
foreign import ccall "qadic.h qadic_init2"
  qadic_init2 :: Ptr CQadic -> CLong -> IO ()

-- | /qadic_clear/ /rop/ 
-- 
-- Clears the element @rop@.
foreign import ccall "qadic.h qadic_clear"
  qadic_clear :: Ptr CQadic -> IO ()

foreign import ccall "qadic.h &qadic_clear"
  p_qadic_clear :: FunPtr (Ptr CQadic -> IO ())

-- | /_fmpz_poly_reduce/ /R/ /lenR/ /a/ /j/ /len/ 
-- 
-- Reduces a polynomial @(R, lenR)@ modulo a sparse monic
-- polynomial \(f(X) = \sum_{i} a_{i} X^{j_{i}}\) of degree at least \(2\).
-- 
-- Assumes that the array \(j\) of positive length @len@ is sorted in
-- ascending order.
-- 
-- Allows zero-padding in @(R, lenR)@.
foreign import ccall "qadic.h _fmpz_poly_reduce"
  _fmpz_poly_reduce :: Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CLong -> CLong -> IO ()

-- | /_fmpz_mod_poly_reduce/ /R/ /lenR/ /a/ /j/ /len/ /p/ 
-- 
-- Reduces a polynomial @(R, lenR)@ modulo a sparse monic
-- polynomial \(f(X) = \sum_{i} a_{i} X^{j_{i}}\) of degree at least \(2\) in
-- \(\mathbb{Z}/(p)\), where \(p\) is typically a prime power.
-- 
-- Assumes that the array \(j\) of positive length @len@ is sorted in
-- ascending order.
-- 
-- Allows zero-padding in @(R, lenR)@.
foreign import ccall "qadic.h _fmpz_mod_poly_reduce"
  _fmpz_mod_poly_reduce :: Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CLong -> CLong -> Ptr CFmpz -> IO ()

-- | /qadic_reduce/ /rop/ /ctx/ 
-- 
-- Reduces @rop@ modulo \(f(X)\) and \(p^N\).
foreign import ccall "qadic.h qadic_reduce"
  qadic_reduce :: Ptr CQadic -> Ptr CQadicCtx -> IO ()

-- Properties ------------------------------------------------------------------

-- | /qadic_val/ /op/ 
-- 
-- Returns the valuation of @op@.
foreign import ccall "qadic.h qadic_val"
  qadic_val :: Ptr CQadic -> IO CLong

-- | /qadic_prec/ /op/ 
-- 
-- Returns the precision of @op@.
foreign import ccall "qadic.h qadic_prec"
  qadic_prec :: Ptr CQadic -> IO CLong

-- Randomisation ---------------------------------------------------------------

-- | /qadic_randtest/ /rop/ /state/ /ctx/ 
-- 
-- Generates a random element of \(\mathbb{Q}_q\).
foreign import ccall "qadic.h qadic_randtest"
  qadic_randtest :: Ptr CQadic -> Ptr CFRandState -> Ptr CQadicCtx -> IO ()

-- | /qadic_randtest_not_zero/ /rop/ /state/ /ctx/ 
-- 
-- Generates a random non-zero element of \(\mathbb{Q}_q\).
foreign import ccall "qadic.h qadic_randtest_not_zero"
  qadic_randtest_not_zero :: Ptr CQadic -> Ptr CFRandState -> Ptr CQadicCtx -> IO ()

-- | /qadic_randtest_val/ /rop/ /state/ /v/ /ctx/ 
-- 
-- Generates a random element of \(\mathbb{Q}_q\) with prescribed valuation
-- @val@.
-- 
-- Note that if \(v \geq N\) then the element is necessarily zero.
foreign import ccall "qadic.h qadic_randtest_val"
  qadic_randtest_val :: Ptr CQadic -> Ptr CFRandState -> CLong -> Ptr CQadicCtx -> IO ()

-- | /qadic_randtest_int/ /rop/ /state/ /ctx/ 
-- 
-- Generates a random element of \(\mathbb{Q}_q\) with non-negative
-- valuation.
foreign import ccall "qadic.h qadic_randtest_int"
  qadic_randtest_int :: Ptr CQadic -> Ptr CFRandState -> Ptr CQadicCtx -> IO ()

-- Assignments and conversions -------------------------------------------------

-- | /qadic_set/ /rop/ /op/ 
-- 
-- Sets @rop@ to @op@.
foreign import ccall "qadic.h qadic_set"
  qadic_set :: Ptr CQadic -> Ptr CQadic -> IO ()

-- | /qadic_zero/ /rop/ 
-- 
-- Sets @rop@ to zero.
foreign import ccall "qadic.h qadic_zero"
  qadic_zero :: Ptr CQadic -> IO ()

-- | /qadic_one/ /rop/ /ctx/ 
-- 
-- Sets @rop@ to one, reduced in the given context.
-- 
-- Note that if the precision \(N\) is non-positive then @rop@ is actually
-- set to zero.
foreign import ccall "qadic.h qadic_one"
  qadic_one :: Ptr CQadic -> Ptr CQadicCtx -> IO ()

-- | /qadic_gen/ /rop/ /ctx/ 
-- 
-- Sets @rop@ to the generator \(X\) for the extension when \(N > 0\), and
-- zero otherwise. If the extension degree is one, raises an abort signal.
foreign import ccall "qadic.h qadic_gen"
  qadic_gen :: Ptr CQadic -> Ptr CQadicCtx -> IO ()

-- | /qadic_set_ui/ /rop/ /op/ /ctx/ 
-- 
-- Sets @rop@ to the integer @op@, reduced in the context.
foreign import ccall "qadic.h qadic_set_ui"
  qadic_set_ui :: Ptr CQadic -> CULong -> Ptr CQadicCtx -> IO ()

-- | /qadic_get_padic/ /rop/ /op/ /ctx/ 
-- 
-- If the element @op@ lies in \(\mathbb{Q}_p\), sets @rop@ to its value
-- and returns \(1\); otherwise, returns \(0\).
foreign import ccall "qadic.h qadic_get_padic"
  qadic_get_padic :: Ptr CPadic -> Ptr CQadic -> Ptr CQadicCtx -> IO CInt

-- Comparison ------------------------------------------------------------------

-- | /qadic_is_zero/ /op/ 
-- 
-- Returns whether @op@ is equal to zero.
foreign import ccall "qadic.h qadic_is_zero"
  qadic_is_zero :: Ptr CQadic -> IO CInt

-- | /qadic_is_one/ /op/ /ctx/ 
-- 
-- Returns whether @op@ is equal to one in the given context.
foreign import ccall "qadic.h qadic_is_one"
  qadic_is_one :: Ptr CQadic -> Ptr CQadicCtx -> IO CInt

-- | /qadic_equal/ /op1/ /op2/ 
-- 
-- Returns whether @op1@ and @op2@ are equal.
foreign import ccall "qadic.h qadic_equal"
  qadic_equal :: Ptr CQadic -> Ptr CQadic -> IO CInt

-- Basic arithmetic ------------------------------------------------------------

-- | /qadic_add/ /rop/ /op1/ /op2/ /ctx/ 
-- 
-- Sets @rop@ to the sum of @op1@ and @op2@.
-- 
-- Assumes that both @op1@ and @op2@ are reduced in the given context and
-- ensures that @rop@ is, too.
foreign import ccall "qadic.h qadic_add"
  qadic_add :: Ptr CQadic -> Ptr CQadic -> Ptr CQadic -> Ptr CQadicCtx -> IO ()

-- | /qadic_sub/ /rop/ /op1/ /op2/ /ctx/ 
-- 
-- Sets @rop@ to the difference of @op1@ and @op2@.
-- 
-- Assumes that both @op1@ and @op2@ are reduced in the given context and
-- ensures that @rop@ is, too.
foreign import ccall "qadic.h qadic_sub"
  qadic_sub :: Ptr CQadic -> Ptr CQadic -> Ptr CQadic -> Ptr CQadicCtx -> IO ()

-- | /qadic_neg/ /rop/ /op/ /ctx/ 
-- 
-- Sets @rop@ to the negative of @op@.
-- 
-- Assumes that @op@ is reduced in the given context and ensures that @rop@
-- is, too.
foreign import ccall "qadic.h qadic_neg"
  qadic_neg :: Ptr CQadic -> Ptr CQadic -> Ptr CQadicCtx -> IO ()

-- | /qadic_mul/ /rop/ /op1/ /op2/ /ctx/ 
-- 
-- Sets @rop@ to the product of @op1@ and @op2@, reducing the output in the
-- given context.
foreign import ccall "qadic.h qadic_mul"
  qadic_mul :: Ptr CQadic -> Ptr CQadic -> Ptr CQadic -> Ptr CQadicCtx -> IO ()

-- | /_qadic_inv/ /rop/ /op/ /len/ /a/ /j/ /lena/ /p/ /N/ 
-- 
-- Sets @(rop, d)@ to the inverse of @(op, len)@ modulo \(f(X)\) given by
-- @(a,j,lena)@ and \(p^N\).
-- 
-- Assumes that @(op,len)@ has valuation \(0\), that is, that it represents
-- a \(p\)-adic unit.
-- 
-- Assumes that @len@ is at most \(d\).
-- 
-- Does not support aliasing.
foreign import ccall "qadic.h _qadic_inv"
  _qadic_inv :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CLong -> CLong -> Ptr CFmpz -> CLong -> IO ()

-- | /qadic_inv/ /rop/ /op/ /ctx/ 
-- 
-- Sets @rop@ to the inverse of @op@, reduced in the given context.
foreign import ccall "qadic.h qadic_inv"
  qadic_inv :: Ptr CQadic -> Ptr CQadic -> Ptr CQadicCtx -> IO ()

-- | /_qadic_pow/ /rop/ /op/ /len/ /e/ /a/ /j/ /lena/ /p/ 
-- 
-- Sets @(rop, 2*d-1)@ to @(op,len)@ raised to the power \(e\), reduced
-- modulo \(f(X)\) given by @(a, j, lena)@ and \(p\), which is expected to
-- be a prime power.
-- 
-- Assumes that \(e \geq 0\) and that @len@ is positive and at most \(d\).
-- 
-- Although we require that @rop@ provides space for \(2d - 1\)
-- coefficients, the output will be reduces modulo \(f(X)\), which is a
-- polynomial of degree \(d\).
-- 
-- Does not support aliasing.
foreign import ccall "qadic.h _qadic_pow"
  _qadic_pow :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpz -> Ptr CLong -> CLong -> Ptr CFmpz -> IO ()

-- | /qadic_pow/ /rop/ /op/ /e/ /ctx/ 
-- 
-- Sets @rop@ the @op@ raised to the power \(e\).
-- 
-- Currently assumes that \(e \geq 0\).
-- 
-- Note that for any input @op@, @rop@ is set to one in the given context
-- whenever \(e = 0\).
foreign import ccall "qadic.h qadic_pow"
  qadic_pow :: Ptr CQadic -> Ptr CQadic -> Ptr CFmpz -> Ptr CQadicCtx -> IO ()

-- Square root -----------------------------------------------------------------

-- | /qadic_sqrt/ /rop/ /op/ /ctx/ 
-- 
-- Return @1@ if the input is a square (to input precision). If so, set
-- @rop@ to a square root (truncated to output precision).
foreign import ccall "qadic.h qadic_sqrt"
  qadic_sqrt :: Ptr CQadic -> Ptr CQadic -> Ptr CQadicCtx -> IO CInt

-- Special functions -----------------------------------------------------------

-- | /_qadic_exp_rectangular/ /rop/ /op/ /v/ /len/ /a/ /j/ /lena/ /p/ /N/ /pN/ 
-- 
-- Sets @(rop, 2*d - 1)@ to the exponential of @(op, v, len)@ reduced
-- modulo \(p^N\), assuming that the series converges.
-- 
-- Assumes that @(op, v, len)@ is non-zero.
-- 
-- Does not support aliasing.
foreign import ccall "qadic.h _qadic_exp_rectangular"
  _qadic_exp_rectangular :: Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> Ptr CFmpz -> Ptr CLong -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /qadic_exp_rectangular/ /rop/ /op/ /ctx/ 
-- 
-- Returns whether the exponential series converges at @op@ and sets @rop@
-- to its value reduced modulo in the given context.
foreign import ccall "qadic.h qadic_exp_rectangular"
  qadic_exp_rectangular :: Ptr CQadic -> Ptr CQadic -> Ptr CQadicCtx -> IO CInt

-- | /_qadic_exp_balanced/ /rop/ /x/ /v/ /len/ /a/ /j/ /lena/ /p/ /N/ /pN/ 
-- 
-- Sets @(rop, d)@ to the exponential of @(op, v, len)@ reduced modulo
-- \(p^N\), assuming that the series converges.
-- 
-- Assumes that @len@ is in \([1,d)\) but supports zero padding, including
-- the special case when @(op, len)@ is zero.
-- 
-- Supports aliasing between @rop@ and @op@.
foreign import ccall "qadic.h _qadic_exp_balanced"
  _qadic_exp_balanced :: Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> Ptr CFmpz -> Ptr CLong -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /qadic_exp_balanced/ /rop/ /op/ /ctx/ 
-- 
-- Returns whether the exponential series converges at @op@ and sets @rop@
-- to its value reduced modulo in the given context.
foreign import ccall "qadic.h qadic_exp_balanced"
  qadic_exp_balanced :: Ptr CQadic -> Ptr CQadic -> Ptr CQadicCtx -> IO CInt

-- | /_qadic_exp/ /rop/ /op/ /v/ /len/ /a/ /j/ /lena/ /p/ /N/ 
-- 
-- Sets @(rop, 2*d - 1)@ to the exponential of @(op, v, len)@ reduced
-- modulo \(p^N\), assuming that the series converges.
-- 
-- Assumes that @(op, v, len)@ is non-zero.
-- 
-- Does not support aliasing.
foreign import ccall "qadic.h _qadic_exp"
  _qadic_exp :: Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> Ptr CFmpz -> Ptr CLong -> CLong -> Ptr CFmpz -> CLong -> IO ()

-- | /qadic_exp/ /rop/ /op/ /ctx/ 
-- 
-- Returns whether the exponential series converges at @op@ and sets @rop@
-- to its value reduced modulo in the given context.
-- 
-- The exponential series converges if the valuation of @op@ is at least
-- \(2\) or \(1\) when \(p\) is even or odd, respectively.
foreign import ccall "qadic.h qadic_exp"
  qadic_exp :: Ptr CQadic -> Ptr CQadic -> Ptr CQadicCtx -> IO CInt

-- | /_qadic_log_rectangular/ /z/ /y/ /v/ /len/ /a/ /j/ /lena/ /p/ /N/ /pN/ 
-- 
-- Computes
-- 
-- \[`\]
-- \[z = - \sum_{i = 1}^{\infty} \frac{y^i}{i} \pmod{p^N}.\]
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
-- Assumes that \(y\) is reduced modulo \(p^N\).
-- 
-- Assumes that \(v < N\), and in particular \(N \geq 2\).
-- 
-- Supports aliasing between \(y\) and \(z\).
foreign import ccall "qadic.h _qadic_log_rectangular"
  _qadic_log_rectangular :: Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> Ptr CFmpz -> Ptr CLong -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /qadic_log_rectangular/ /rop/ /op/ /ctx/ 
-- 
-- Returns whether the \(p\)-adic logarithm function converges at @op@, and
-- if so sets @rop@ to its value.
foreign import ccall "qadic.h qadic_log_rectangular"
  qadic_log_rectangular :: Ptr CQadic -> Ptr CQadic -> Ptr CPadicCtx -> IO CInt

-- | /_qadic_log_balanced/ /z/ /y/ /len/ /a/ /j/ /lena/ /p/ /N/ /pN/ 
-- 
-- Computes \((z, d)\) as
-- 
-- \[`\]
-- \[z = - \sum_{i = 1}^{\infty} \frac{y^i}{i} \pmod{p^N}.\]
-- 
-- Assumes that \(v = \operatorname{ord}_p(y)\) is at least \(1\) when
-- \(p\) is odd and at least \(2\) when \(p = 2\) so that the series
-- converges.
-- 
-- Supports aliasing between \(z\) and \(y\).
foreign import ccall "qadic.h _qadic_log_balanced"
  _qadic_log_balanced :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CLong -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /qadic_log_balanced/ /rop/ /op/ /ctx/ 
-- 
-- Returns whether the \(p\)-adic logarithm function converges at @op@, and
-- if so sets @rop@ to its value.
foreign import ccall "qadic.h qadic_log_balanced"
  qadic_log_balanced :: Ptr CQadic -> Ptr CQadic -> Ptr CQadicCtx -> IO CInt

-- | /_qadic_log/ /z/ /y/ /v/ /len/ /a/ /j/ /lena/ /p/ /N/ /pN/ 
-- 
-- Computes \((z, d)\) as
-- 
-- \[`\]
-- \[z = - \sum_{i = 1}^{\infty} \frac{y^i}{i} \pmod{p^N}.\]
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
-- Assumes that \((y, d)\) is reduced modulo \(p^N\).
-- 
-- Assumes that \(v < N\), and hence in particular \(N \geq 2\).
-- 
-- Supports aliasing between \(z\) and \(y\).
foreign import ccall "qadic.h _qadic_log"
  _qadic_log :: Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> Ptr CFmpz -> Ptr CLong -> CLong -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /qadic_log/ /rop/ /op/ /ctx/ 
-- 
-- Returns whether the \(p\)-adic logarithm function converges at @op@, and
-- if so sets @rop@ to its value.
-- 
-- The \(p\)-adic logarithm function is defined by the usual series
-- 
-- \[`\]
-- \[\log_p(x) = \sum_{i=1}^{\infty} (-1)^{i-1} \frac{(x-1)^i}{i}\]
-- 
-- but this only converges when \(\operatorname{ord}_p(x)\) is at least
-- \(2\) or \(1\) when \(p = 2\) or \(p > 2\), respectively.
foreign import ccall "qadic.h qadic_log"
  qadic_log :: Ptr CQadic -> Ptr CQadic -> Ptr CQadicCtx -> IO CInt

-- | /_qadic_frobenius_a/ /rop/ /e/ /a/ /j/ /lena/ /p/ /N/ 
-- 
-- Computes \(\sigma^e(X) \bmod{p^N}\) where \(X\) is such that
-- \(\mathbb{Q}_q \cong \mathbb{Q}_p[X]/(f(X))\).
-- 
-- Assumes that the precision \(N\) is at least \(2\) and that the
-- extension is non-trivial, i.e.\(d \geq 2\).
-- 
-- Assumes that \(0 < e < d\).
-- 
-- Sets @(rop, 2*d-1)@, although the actual length of the output will be at
-- most \(d\).
foreign import ccall "qadic.h _qadic_frobenius_a"
  _qadic_frobenius_a :: Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CLong -> CLong -> Ptr CFmpz -> CLong -> IO ()

-- | /_qadic_frobenius/ /rop/ /op/ /len/ /e/ /a/ /j/ /lena/ /p/ /N/ 
-- 
-- Sets @(rop, 2*d-1)@ to \(\Sigma\) evaluated at @(op, len)@.
-- 
-- Assumes that @len@ is positive but at most \(d\).
-- 
-- Assumes that \(0 < e < d\).
-- 
-- Does not support aliasing.
foreign import ccall "qadic.h _qadic_frobenius"
  _qadic_frobenius :: Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> Ptr CFmpz -> Ptr CLong -> CLong -> Ptr CFmpz -> CLong -> IO ()

-- | /qadic_frobenius/ /rop/ /op/ /e/ /ctx/ 
-- 
-- Evaluates the homomorphism \(\Sigma^e\) at @op@.
-- 
-- Recall that \(\mathbb{Q}_q / \mathbb{Q}_p\) is Galois with Galois group
-- \(\langle \Sigma \rangle \cong \langle \sigma \rangle\), which is also
-- isomorphic to \(\mathbb{Z}/d\mathbb{Z}\), where
-- \(\sigma \in \operatorname{Gal}(\mathbb{F}_q/\mathbb{F}_p)\) is the
-- Frobenius element \(\sigma \colon x \mapsto x^p\) and \(\Sigma\) is its
-- lift to \(\operatorname{Gal}(\mathbb{Q}_q/\mathbb{Q}_p)\).
-- 
-- This functionality is implemented as @GaloisImage()@ in Magma.
foreign import ccall "qadic.h qadic_frobenius"
  qadic_frobenius :: Ptr CQadic -> Ptr CQadic -> CLong -> Ptr CQadicCtx -> IO ()

-- | /_qadic_teichmuller/ /rop/ /op/ /len/ /a/ /j/ /lena/ /p/ /N/ 
-- 
-- Sets @(rop, d)@ to the Teichm\"uller lift of @(op, len)@ modulo \(p^N\).
-- 
-- Does not support aliasing.
foreign import ccall "qadic.h _qadic_teichmuller"
  _qadic_teichmuller :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CLong -> CLong -> Ptr CFmpz -> CLong -> IO ()

-- | /qadic_teichmuller/ /rop/ /op/ /ctx/ 
-- 
-- Sets @rop@ to the Teichm\"uller lift of @op@ to the precision given in
-- the context.
-- 
-- For a unit @op@, this is the unique \((q-1)`th root of unity 
-- which is congruent to \)op modulo :math:\`p.
-- 
-- Sets @rop@ to zero if @op@ is zero in the given context.
-- 
-- Raises an exception if the valuation of @op@ is negative.
foreign import ccall "qadic.h qadic_teichmuller"
  qadic_teichmuller :: Ptr CQadic -> Ptr CQadic -> Ptr CQadicCtx -> IO ()

-- | /_qadic_trace/ /rop/ /op/ /len/ /a/ /j/ /lena/ /pN/ 
-- 
-- Sets @rop@ to the trace of @op@.
-- 
-- For an element \(a \in \mathbb{Q}_q\), multiplication by \(a\) defines a
-- \(\mathbb{Q}_p\)-linear map on \(\mathbb{Q}_q\). We define the trace of
-- \(a\) as the trace of this map. Equivalently, if \(\Sigma\) generates
-- \(\operatorname{Gal}(\mathbb{Q}_q / \mathbb{Q}_p)\) then the trace of
-- \(a\) is equal to \(\sum_{i=0}^{d-1} \Sigma^i (a)\).
foreign import ccall "qadic.h _qadic_trace"
  _qadic_trace :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CLong -> CLong -> Ptr CFmpz -> IO ()

-- | /_qadic_norm/ /rop/ /op/ /len/ /a/ /j/ /lena/ /p/ /N/ 
-- 
-- Sets @rop@ to the norm of the element @(op,len)@ in \(\mathbb{Z}_q\) to
-- precision \(N\), where @len@ is at least one.
-- 
-- The result will be reduced modulo \(p^N\).
-- 
-- Note that whenever @(op,len)@ is a unit, so is its norm. Thus, the
-- output @rop@ of this function will typically not have to be
-- canonicalised or reduced by the caller.
foreign import ccall "qadic.h _qadic_norm"
  _qadic_norm :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CLong -> CLong -> Ptr CFmpz -> CLong -> IO ()

-- | /qadic_norm/ /rop/ /op/ /ctx/ 
-- 
-- Computes the norm of @op@ to the given precision.
-- 
-- Algorithm selection is automatic depending on the input.
foreign import ccall "qadic.h qadic_norm"
  qadic_norm :: Ptr CPadic -> Ptr CQadic -> Ptr CQadicCtx -> IO ()

-- | /qadic_norm_analytic/ /rop/ /op/ /ctx/ 
-- 
-- Whenever @op@ has valuation greater than \((p-1)^{-1}\), this routine
-- computes its norm @rop@ via
-- 
-- \[`\]
-- \[\operatorname{Norm} (x) = \exp \Bigl( \bigl( \operatorname{Trace} \log (x) \bigr) \Bigr).\]
-- 
-- In the special case that @op@ lies in \(\mathbb{Q}_p\), returns its norm
-- as \(\operatorname{Norm}(x) = x^d\), where \(d\) is the extension
-- degree.
-- 
-- Otherwise, raises an @abort@ signal.
-- 
-- The complexity of this implementation is quasi-linear in \(d\) and
-- \(N\), and polynomial in \(\log p\).
foreign import ccall "qadic.h qadic_norm_analytic"
  qadic_norm_analytic :: Ptr CPadic -> Ptr CQadic -> Ptr CQadicCtx -> IO ()

-- | /qadic_norm_resultant/ /rop/ /op/ /ctx/ 
-- 
-- Sets @rop@ to the norm of @op@, using the formula
-- 
-- \[`\]
-- \[\operatorname{Norm}(x) = \ell(f)^{-\deg(a)} \operatorname{Res}(f(X), a(X)),\]
-- 
-- where \(\mathbb{Q}_q \cong \mathbb{Q}_p[X] / (f(X))\), \(\ell(f)\) is
-- the leading coefficient of \(f(X)\), and \(a(X) \in \mathbb{Q}_p[X]\)
-- denotes the same polynomial as \(x\).
-- 
-- The complexity of the current implementation is given
-- by \(\mathcal{O}(d^4 M(N \log p))\), where \(M(n)\) denotes the complexity
-- of multiplying to \(n\)-bit integers.
foreign import ccall "qadic.h qadic_norm_resultant"
  qadic_norm_resultant :: Ptr CPadic -> Ptr CQadic -> Ptr CQadicCtx -> IO ()

-- Output ----------------------------------------------------------------------

-- | /qadic_fprint_pretty/ /file/ /op/ /ctx/ 
-- 
-- Prints a pretty representation of @op@ to @file@.
-- 
-- In the current implementation, always returns \(1\). The return code is
-- part of the function\'s signature to allow for a later implementation to
-- return the number of characters printed or a non-positive error code.
foreign import ccall "qadic.h qadic_fprint_pretty"
  qadic_fprint_pretty :: Ptr CFile -> Ptr CQadic -> Ptr CQadicCtx -> IO CInt

-- | /qadic_print_pretty/ /op/ /ctx/ 
-- 
-- Prints a pretty representation of @op@ to @stdout@.
-- 
-- In the current implementation, always returns \(1\). The return code is
-- part of the function\'s signature to allow for a later implementation to
-- return the number of characters printed or a non-positive error code.
qadic_print_pretty x ctx = printCStr (flip qadic_get_str_pretty ctx) x

-- | /qadic_get_str__pretty/ /op/ /ctx/
--
-- Returns a pretty representation of @op@ in a C string.
foreign import ccall "qadic_get_str_pretty"
  qadic_get_str_pretty :: Ptr CQadic -> Ptr CQadicCtx -> IO CString


