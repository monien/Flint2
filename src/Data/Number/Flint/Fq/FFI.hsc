module Data.Number.Flint.Fq.FFI (
  -- * Finite fields
  -- ** Finite field element
  --
  -- | The type `Fq` represents an element of the finite field \(\mathbb F_q\).
    Fq (..)
  , CFq (..)
  , newFq
  , withFq
  , withNewFq
  -- * Finite field context
  , FqCtx (..)
  , CFqCtx (..)
  , newFqCtx
  , withFqCtx
  , withNewFqCtx
  , newFqCtxConway
  , withNewFqCtxConway
  , newFqCtxModulus
  , withNewFqCtxModulus
  -- * Context Management
  , fq_ctx_init
  , _fq_ctx_init_conway
  , fq_ctx_init_conway
  , fq_ctx_init_modulus
  , fq_ctx_clear
  , fq_ctx_modulus
  , fq_ctx_degree
  , fq_ctx_prime
  , fq_ctx_order
  , fq_ctx_fprint
  , fq_ctx_print
  , fq_ctx_randtest
  , fq_ctx_randtest_reducible
  -- * Memory management
  , fq_init
  , fq_init2
  , fq_clear
  , _fq_sparse_reduce
  , _fq_dense_reduce
  , _fq_reduce
  , fq_reduce
  -- * Basic arithmetic
  , fq_add
  , fq_sub
  , fq_sub_one
  , fq_neg
  , fq_mul
  , fq_mul_fmpz
  , fq_mul_si
  , fq_mul_ui
  , fq_sqr
  , fq_div
  , _fq_inv
  , fq_inv
  , fq_gcdinv
  , _fq_pow
  , fq_pow
  , fq_pow_ui
  -- * Roots
  , fq_sqrt
  , fq_pth_root
  , fq_is_square
  -- * Output
  , fq_fprint_pretty
  , fq_print_pretty
  , fq_fprint
  , fq_print
  , fq_get_str
  , fq_get_str_pretty
  -- * Randomisation
  , fq_randtest
  , fq_randtest_not_zero
  , fq_randtest_dense
  , fq_rand
  , fq_rand_not_zero
  -- * Assignments and conversions
  , fq_set
  , fq_set_si
  , fq_set_ui
  , fq_set_fmpz
  , fq_swap
  , fq_zero
  , fq_one
  , fq_gen
  , fq_get_fmpz
  , fq_get_fmpz_poly
  , fq_get_fmpz_mod_poly
  , fq_set_fmpz_poly
  , fq_set_fmpz_mod_poly
  , fq_get_fmpz_mod_mat
  , fq_set_fmpz_mod_mat
  -- * Comparison
  , fq_is_zero
  , fq_is_one
  , fq_equal
  , fq_is_invertible
  , fq_is_invertible_f
  -- * Special functions
  , _fq_trace
  , fq_trace
  , _fq_norm
  , fq_norm
  , _fq_frobenius
  , fq_frobenius
  , fq_multiplicative_order
  , fq_is_primitive
  -- * Bit packing
  , fq_bit_pack
  , fq_bit_unpack
) where 

-- finite fields ---------------------------------------------------------------

import Foreign.C.String
import Foreign.C.Types
import qualified Foreign.Concurrent
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr )
import Foreign.Storable
import Foreign.Marshal ( free )

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Poly
import Data.Number.Flint.Fmpz.Mod
import Data.Number.Flint.Fmpz.Mod.Poly
import Data.Number.Flint.Fmpz.Mod.Mat
import Data.Number.Flint.Fmpq

#include <flint/flint.h>
#include <flint/fq.h>

-- fq_t ------------------------------------------------------------------------

data Fq = Fq {-# UNPACK #-} !(ForeignPtr CFq)
type CFq = CFmpzPoly

-- | Create a new `Fq` with context `ctx`.
newFq :: FqCtx -> IO Fq
newFq ctx@(FqCtx pctx) = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> do
    withFqCtx ctx $ \ctx -> do
      fq_init x ctx
      addForeignPtrFinalizerEnv p_fq_clear x pctx
  return $ Fq x

-- | Use `Fq`.
{-# INLINE withFq #-}
withFq (Fq p) f = do
  withForeignPtr p $ \fp -> f fp >>= return . (Fq p,)

-- | Use a new `Fq`.
{-# INLINE withNewFq #-}
withNewFq ctx f = do
  x <- newFq ctx
  withFq x f

-- fq_ctx_t --------------------------------------------------------------------

-- | Context of the finite field (opaque pointer)
data FqCtx = FqCtx {-# UNPACK #-} !(ForeignPtr CFqCtx)
type CFqCtx = CFlint FqCtx

instance Storable CFqCtx where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fq_ctx_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fq_ctx_t}
  peek = undefined
  poke = undefined

-- | Create a new `Fq` context using `fq_ctx_init`.
newFqCtx p d var = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x ->
    withFmpz p $ \p ->
      withCString var $ \var ->
        fq_ctx_init x p d var
  addForeignPtrFinalizer p_fq_ctx_clear x
  return $ FqCtx x

-- | Use the `FqCtx`.
{-# INLINE withFqCtx #-}
withFqCtx (FqCtx p) f = do
  withForeignPtr p $ \fp -> f fp >>= return . (FqCtx p,)

-- | Apply function to new `FqCtx`.
-- parameters as in `newFqCtx`.
withNewFqCtx p d var f = do
  ctx <- newFqCtx p d var
  withFqCtx ctx f
  
-- | Create a new `Fq` context using `fq_ctx_init_conway`.
newFqCtxConway p d var = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x ->
    withFmpz p $ \p ->
      withCString var $ \var ->
        fq_ctx_init_conway x p d var
  addForeignPtrFinalizer p_fq_ctx_clear x
  return $ FqCtx x

-- | Apply function to new `Fq` initialized with `fq_ctx_init_conway`.
withNewFqCtxConway p d var f = do
  ctx <- newFqCtxConway p d var
  withFqCtx ctx f
 
-- | Create a new `Fq` context using `fq_ctx_init_modulus`.
newFqCtxModulus modulus mod_ctx var = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x ->
    withFmpzModPoly modulus $ \modulus ->
      withFmpzModCtx mod_ctx $ \mod_ctx ->  
        withCString var $ \var ->
          fq_ctx_init_modulus x modulus mod_ctx var
  addForeignPtrFinalizer p_fq_ctx_clear x
  return $ FqCtx x

-- | Create a new `Fq` initialized using `fq_ctx_init_modulus`.
withNewFqCtxModulus modulus mod_ctx var f = do
  ctx <- newFqCtxModulus modulus mod_ctx var
  withFqCtx ctx f
 
-- Context Management ----------------------------------------------------------

-- | /fq_ctx_init/ /ctx/ /p/ /d/ /var/ 
-- 
-- Initialises the context for prime \(p\) and extension degree \(d\), with
-- name @var@ for the generator. By default, it will try use a Conway
-- polynomial; if one is not available, a random irreducible polynomial
-- will be used.
-- 
-- Assumes that \(p\) is a prime.
-- 
-- Assumes that the string @var@ is a null-terminated string of length at
-- least one.
foreign import ccall "fq.h fq_ctx_init"
  fq_ctx_init :: Ptr CFqCtx -> Ptr CFmpz -> CLong -> CString -> IO ()

-- | /_fq_ctx_init_conway/ /ctx/ /p/ /d/ /var/ 
-- 
-- Attempts to initialise the context for prime \(p\) and extension degree
-- \(d\), with name @var@ for the generator using a Conway polynomial for
-- the modulus.
-- 
-- Returns \(1\) if the Conway polynomial is in the database for the given
-- size and the initialization is successful; otherwise, returns \(0\).
-- 
-- Assumes that \(p\) is a prime.
-- 
-- Assumes that the string @var@ is a null-terminated string of length at
-- least one.
foreign import ccall "fq.h _fq_ctx_init_conway"
  _fq_ctx_init_conway :: Ptr CFqCtx -> Ptr CFmpz -> CLong -> CString -> IO CInt

-- | /fq_ctx_init_conway/ /ctx/ /p/ /d/ /var/ 
-- 
-- Initialises the context for prime \(p\) and extension degree \(d\), with
-- name @var@ for the generator using a Conway polynomial for the modulus.
-- 
-- Assumes that \(p\) is a prime.
-- 
-- Assumes that the string @var@ is a null-terminated string of length at
-- least one.
foreign import ccall "fq.h fq_ctx_init_conway"
  fq_ctx_init_conway :: Ptr CFqCtx -> Ptr CFmpz -> CLong -> CString -> IO ()

-- | /fq_ctx_init_modulus/ /ctx/ /modulus/ /ctxp/ /var/ 
-- 
-- Initialises the context for given @modulus@ with name @var@ for the
-- generator.
-- 
-- Assumes that @modulus@ is an irreducible polynomial over the finite
-- field \(\mathbf{F}_{p}\) in @ctxp@.
-- 
-- Assumes that the string @var@ is a null-terminated string of length at
-- least one.
foreign import ccall "fq.h fq_ctx_init_modulus"
  fq_ctx_init_modulus :: Ptr CFqCtx -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> CString -> IO ()

-- | /fq_ctx_clear/ /ctx/ 
-- 
-- Clears all memory that has been allocated as part of the context.
foreign import ccall "fq.h fq_ctx_clear"
  fq_ctx_clear :: Ptr CFqCtx -> IO ()

foreign import ccall "fq.h &fq_ctx_clear"
  p_fq_ctx_clear :: FunPtr (Ptr CFqCtx -> IO ())

-- | /fq_ctx_modulus/ /ctx/ 
-- 
-- Returns a pointer to the modulus in the context.
foreign import ccall "fq.h fq_ctx_modulus"
  fq_ctx_modulus :: Ptr CFqCtx -> IO (Ptr CFmpzModPoly)

-- | /fq_ctx_degree/ /ctx/ 
-- 
-- Returns the degree of the field extension
-- \([\mathbf{F}_{q} : \mathbf{F}_{p}]\), which is equal to \(\log_{p} q\).
foreign import ccall "fq.h fq_ctx_degree"
  fq_ctx_degree :: Ptr CFqCtx -> IO CLong

-- | /fq_ctx_prime/ /ctx/ 
-- 
-- Returns a pointer to the prime \(p\) in the context.
foreign import ccall "fq.h fq_ctx_prime"
  fq_ctx_prime :: Ptr CFqCtx -> IO (Ptr CFmpz)

-- | /fq_ctx_order/ /f/ /ctx/ 
-- 
-- Sets \(f\) to be the size of the finite field.
foreign import ccall "fq.h fq_ctx_order"
  fq_ctx_order :: Ptr CFmpz -> Ptr CFqCtx -> IO ()

-- | /fq_ctx_fprint/ /file/ /ctx/ 
-- 
-- Prints the context information to @file@. Returns 1 for a success and a
-- negative number for an error.
foreign import ccall "fq.h fq_ctx_fprint"
  fq_ctx_fprint :: Ptr CFile -> Ptr CFqCtx -> IO CInt

-- | /fq_ctx_print/ /ctx/ 
-- 
-- Prints the context information to @stdout@.
foreign import ccall "fq.h fq_ctx_print"
  fq_ctx_print :: Ptr CFqCtx -> IO ()

-- | /fq_ctx_randtest/ /ctx/ 
-- 
-- Initializes @ctx@ to a random finite field. Assumes that @fq_ctx_init@
-- has not been called on @ctx@ already.
foreign import ccall "fq.h fq_ctx_randtest"
  fq_ctx_randtest :: Ptr CFqCtx -> IO ()

-- | /fq_ctx_randtest_reducible/ /ctx/ 
-- 
-- Initializes @ctx@ to a random extension of a prime field. The modulus
-- may or may not be irreducible. Assumes that @fq_ctx_init@ has not been
-- called on @ctx@ already.
foreign import ccall "fq.h fq_ctx_randtest_reducible"
  fq_ctx_randtest_reducible :: Ptr CFqCtx -> IO ()

-- Memory management -----------------------------------------------------------

-- | /fq_init/ /rop/ /ctx/ 
-- 
-- Initialises the element @rop@, setting its value to \(0\).
foreign import ccall "fq.h fq_init"
  fq_init :: Ptr CFq -> Ptr CFqCtx -> IO ()

-- | /fq_init2/ /rop/ /ctx/ 
-- 
-- Initialises @poly@ with at least enough space for it to be an element of
-- @ctx@ and sets it to \(0\).
foreign import ccall "fq.h fq_init2"
  fq_init2 :: Ptr CFq -> Ptr CFqCtx -> IO ()

-- | /fq_clear/ /rop/ /ctx/ 
-- 
-- Clears the element @rop@.
foreign import ccall "fq.h fq_clear"
  fq_clear :: Ptr CFq -> Ptr CFqCtx -> IO ()

foreign import ccall "fq.h &fq_clear"
  p_fq_clear :: FunPtr (Ptr CFq -> Ptr CFqCtx -> IO ())

-- | /_fq_sparse_reduce/ /R/ /lenR/ /ctx/ 
-- 
-- Reduces @(R, lenR)@ modulo the polynomial \(f\) given by the modulus of
-- @ctx@.
foreign import ccall "fq.h _fq_sparse_reduce"
  _fq_sparse_reduce :: Ptr CFmpz -> CLong -> Ptr CFqCtx -> IO ()

-- | /_fq_dense_reduce/ /R/ /lenR/ /ctx/ 
-- 
-- Reduces @(R, lenR)@ modulo the polynomial \(f\) given by the modulus of
-- @ctx@ using Newton division.
foreign import ccall "fq.h _fq_dense_reduce"
  _fq_dense_reduce :: Ptr CFmpz -> CLong -> Ptr CFqCtx -> IO ()

-- | /_fq_reduce/ /r/ /lenR/ /ctx/ 
-- 
-- Reduces @(R, lenR)@ modulo the polynomial \(f\) given by the modulus of
-- @ctx@. Does either sparse or dense reduction based on
-- @ctx->sparse_modulus@.
foreign import ccall "fq.h _fq_reduce"
  _fq_reduce :: Ptr CFmpz -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_reduce/ /rop/ /ctx/ 
-- 
-- Reduces the polynomial @rop@ as an element of
-- \(\mathbf{F}_p[X] / (f(X))\).
foreign import ccall "fq.h fq_reduce"
  fq_reduce :: Ptr CFq -> Ptr CFqCtx -> IO ()

-- Basic arithmetic ------------------------------------------------------------

-- | /fq_add/ /rop/ /op1/ /op2/ /ctx/ 
-- 
-- Sets @rop@ to the sum of @op1@ and @op2@.
foreign import ccall "fq.h fq_add"
  fq_add :: Ptr CFq -> Ptr CFq -> Ptr CFq -> Ptr CFqCtx -> IO ()

-- | /fq_sub/ /rop/ /op1/ /op2/ /ctx/ 
-- 
-- Sets @rop@ to the difference of @op1@ and @op2@.
foreign import ccall "fq.h fq_sub"
  fq_sub :: Ptr CFq -> Ptr CFq -> Ptr CFq -> Ptr CFqCtx -> IO ()

-- | /fq_sub_one/ /rop/ /op1/ /ctx/ 
-- 
-- Sets @rop@ to the difference of @op1@ and \(1\).
foreign import ccall "fq.h fq_sub_one"
  fq_sub_one :: Ptr CFq -> Ptr CFq -> Ptr CFqCtx -> IO ()

-- | /fq_neg/ /rop/ /op/ /ctx/ 
-- 
-- Sets @rop@ to the negative of @op@.
foreign import ccall "fq.h fq_neg"
  fq_neg :: Ptr CFq -> Ptr CFq -> Ptr CFqCtx -> IO ()

-- | /fq_mul/ /rop/ /op1/ /op2/ /ctx/ 
-- 
-- Sets @rop@ to the product of @op1@ and @op2@, reducing the output in the
-- given context.
foreign import ccall "fq.h fq_mul"
  fq_mul :: Ptr CFq -> Ptr CFq -> Ptr CFq -> Ptr CFqCtx -> IO ()

-- | /fq_mul_fmpz/ /rop/ /op/ /x/ /ctx/ 
-- 
-- Sets @rop@ to the product of @op@ and \(x\), reducing the output in the
-- given context.
foreign import ccall "fq.h fq_mul_fmpz"
  fq_mul_fmpz :: Ptr CFq -> Ptr CFq -> Ptr CFmpz -> Ptr CFqCtx -> IO ()

-- | /fq_mul_si/ /rop/ /op/ /x/ /ctx/ 
-- 
-- Sets @rop@ to the product of @op@ and \(x\), reducing the output in the
-- given context.
foreign import ccall "fq.h fq_mul_si"
  fq_mul_si :: Ptr CFq -> Ptr CFq -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_mul_ui/ /rop/ /op/ /x/ /ctx/ 
-- 
-- Sets @rop@ to the product of @op@ and \(x\), reducing the output in the
-- given context.
foreign import ccall "fq.h fq_mul_ui"
  fq_mul_ui :: Ptr CFq -> Ptr CFq -> CULong -> Ptr CFqCtx -> IO ()

-- | /fq_sqr/ /rop/ /op/ /ctx/ 
-- 
-- Sets @rop@ to the square of @op@, reducing the output in the given
-- context.
foreign import ccall "fq.h fq_sqr"
  fq_sqr :: Ptr CFq -> Ptr CFq -> Ptr CFqCtx -> IO ()

-- | /fq_div/ /rop/ /op1/ /op2/ /ctx/ 
-- 
-- Sets @rop@ to the quotient of @op1@ and @op2@, reducing the output in
-- the given context.
foreign import ccall "fq.h fq_div"
  fq_div :: Ptr CFq -> Ptr CFq -> Ptr CFq -> Ptr CFqCtx -> IO ()

-- | /_fq_inv/ /rop/ /op/ /len/ /ctx/ 
-- 
-- Sets @(rop, d)@ to the inverse of the non-zero element @(op, len)@.
foreign import ccall "fq.h _fq_inv"
  _fq_inv :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_inv/ /rop/ /op/ /ctx/ 
-- 
-- Sets @rop@ to the inverse of the non-zero element @op@.
foreign import ccall "fq.h fq_inv"
  fq_inv :: Ptr CFq -> Ptr CFq -> Ptr CFqCtx -> IO ()

-- | /fq_gcdinv/ /f/ /inv/ /op/ /ctx/ 
-- 
-- Sets @inv@ to be the inverse of @op@ modulo the modulus of @ctx@. If
-- @op@ is not invertible, then @f@ is set to a factor of the modulus;
-- otherwise, it is set to one.
foreign import ccall "fq.h fq_gcdinv"
  fq_gcdinv :: Ptr CFq -> Ptr CFq -> Ptr CFq -> Ptr CFqCtx -> IO ()

-- | /_fq_pow/ /rop/ /op/ /len/ /e/ /ctx/ 
-- 
-- Sets @(rop, 2*d-1)@ to @(op,len)@ raised to the power \(e\), reduced
-- modulo \(f(X)\), the modulus of @ctx@.
-- 
-- Assumes that \(e \geq 0\) and that @len@ is positive and at most \(d\).
-- 
-- Although we require that @rop@ provides space for \(2d - 1\)
-- coefficients, the output will be reduced modulo \(f(X)\), which is a
-- polynomial of degree \(d\).
-- 
-- Does not support aliasing.
foreign import ccall "fq.h _fq_pow"
  _fq_pow :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFqCtx -> IO ()

-- | /fq_pow/ /rop/ /op/ /e/ /ctx/ 
-- 
-- Sets @rop@ the @op@ raised to the power \(e\).
-- 
-- Currently assumes that \(e \geq 0\).
-- 
-- Note that for any input @op@, @rop@ is set to \(1\) whenever \(e = 0\).
foreign import ccall "fq.h fq_pow"
  fq_pow :: Ptr CFq -> Ptr CFq -> Ptr CFmpz -> Ptr CFqCtx -> IO ()

-- | /fq_pow_ui/ /rop/ /op/ /e/ /ctx/ 
-- 
-- Sets @rop@ the @op@ raised to the power \(e\).
-- 
-- Currently assumes that \(e \geq 0\).
-- 
-- Note that for any input @op@, @rop@ is set to \(1\) whenever \(e = 0\).
foreign import ccall "fq.h fq_pow_ui"
  fq_pow_ui :: Ptr CFq -> Ptr CFq -> CULong -> Ptr CFqCtx -> IO ()

-- Roots -----------------------------------------------------------------------

-- | /fq_sqrt/ /rop/ /op1/ /ctx/ 
-- 
-- Sets @rop@ to the square root of @op1@ if it is a square, and return
-- \(1\), otherwise return \(0\).
foreign import ccall "fq.h fq_sqrt"
  fq_sqrt :: Ptr CFq -> Ptr CFq -> Ptr CFqCtx -> IO CInt

-- | /fq_pth_root/ /rop/ /op1/ /ctx/ 
-- 
-- Sets @rop@ to a \(p^{th}\) root root of @op1@. Currently, this computes
-- the root by raising @op1@ to \(p^{d-1}\) where \(d\) is the degree of
-- the extension.
foreign import ccall "fq.h fq_pth_root"
  fq_pth_root :: Ptr CFq -> Ptr CFq -> Ptr CFqCtx -> IO ()

-- | /fq_is_square/ /op/ /ctx/ 
-- 
-- Return @1@ if @op@ is a square.
foreign import ccall "fq.h fq_is_square"
  fq_is_square :: Ptr CFq -> Ptr CFqCtx -> IO CInt

-- Output ----------------------------------------------------------------------

-- | /fq_fprint_pretty/ /file/ /op/ /ctx/ 
-- 
-- Prints a pretty representation of @op@ to @file@.
-- 
-- In the current implementation, always returns \(1\). The return code is
-- part of the function\'s signature to allow for a later implementation to
-- return the number of characters printed or a non-positive error code.
foreign import ccall "fq.h fq_fprint_pretty"
  fq_fprint_pretty :: Ptr CFile -> Ptr CFq -> Ptr CFqCtx -> IO CInt

-- | /fq_print_pretty/ /op/ /ctx/ 
-- 
-- Prints a pretty representation of @op@ to @stdout@.
-- 
-- In the current implementation, always returns \(1\). The return code is
-- part of the function\'s signature to allow for a later implementation to
-- return the number of characters printed or a non-positive error code.
fq_print_pretty :: Ptr CFq -> Ptr CFqCtx -> IO CInt
fq_print_pretty x ctx = printCStr (flip fq_get_str_pretty ctx) x
 
-- | /fq_fprint/ /file/ /op/ /ctx/ 
-- 
-- Prints a representation of @op@ to @file@.
-- 
-- For further details on the representation used, see
-- @fmpz_mod_poly_fprint@.
foreign import ccall "fq.h fq_fprint"
  fq_fprint :: Ptr CFile -> Ptr CFq -> Ptr CFqCtx -> IO ()

-- | /fq_print/ /op/ /ctx/ 
-- 
-- Prints a representation of @op@ to @stdout@.
-- 
-- For further details on the representation used, see
-- @fmpz_mod_poly_print@.
fq_print :: Ptr CFq -> Ptr CFqCtx -> IO CInt
fq_print x ctx = printCStr (flip fq_get_str ctx) x
  
-- | /fq_get_str/ /op/ /ctx/ 
-- 
-- Returns the plain FLINT string representation of the element @op@.
foreign import ccall "fq.h fq_get_str"
  fq_get_str :: Ptr CFq -> Ptr CFqCtx -> IO CString

-- | /fq_get_str_pretty/ /op/ /ctx/ 
-- 
-- Returns a pretty representation of the element @op@ using the
-- null-terminated string @x@ as the variable name.
foreign import ccall "fq.h fq_get_str_pretty"
  fq_get_str_pretty :: Ptr CFq -> Ptr CFqCtx -> IO CString

-- Randomisation ---------------------------------------------------------------

-- | /fq_randtest/ /rop/ /state/ /ctx/ 
-- 
-- Generates a random element of \(\mathbf{F}_q\).
foreign import ccall "fq.h fq_randtest"
  fq_randtest :: Ptr CFq -> Ptr CFRandState -> Ptr CFqCtx -> IO ()

-- | /fq_randtest_not_zero/ /rop/ /state/ /ctx/ 
-- 
-- Generates a random non-zero element of \(\mathbf{F}_q\).
foreign import ccall "fq.h fq_randtest_not_zero"
  fq_randtest_not_zero :: Ptr CFq -> Ptr CFRandState -> Ptr CFqCtx -> IO ()

-- | /fq_randtest_dense/ /rop/ /state/ /ctx/ 
-- 
-- Generates a random element of \(\mathbf{F}_q\) which has an underlying
-- polynomial with dense coefficients.
foreign import ccall "fq.h fq_randtest_dense"
  fq_randtest_dense :: Ptr CFq -> Ptr CFRandState -> Ptr CFqCtx -> IO ()

-- | /fq_rand/ /rop/ /state/ /ctx/ 
-- 
-- Generates a high quality random element of \(\mathbf{F}_q\).
foreign import ccall "fq.h fq_rand"
  fq_rand :: Ptr CFq -> Ptr CFRandState -> Ptr CFqCtx -> IO ()

-- | /fq_rand_not_zero/ /rop/ /state/ /ctx/ 
-- 
-- Generates a high quality non-zero random element of \(\mathbf{F}_q\).
foreign import ccall "fq.h fq_rand_not_zero"
  fq_rand_not_zero :: Ptr CFq -> Ptr CFRandState -> Ptr CFqCtx -> IO ()

-- Assignments and conversions -------------------------------------------------

-- | /fq_set/ /rop/ /op/ /ctx/ 
-- 
-- Sets @rop@ to @op@.
foreign import ccall "fq.h fq_set"
  fq_set :: Ptr CFq -> Ptr CFq -> Ptr CFqCtx -> IO ()

-- | /fq_set_si/ /rop/ /x/ /ctx/ 
-- 
-- Sets @rop@ to @x@, considered as an element of \(\mathbf{F}_p\).
foreign import ccall "fq.h fq_set_si"
  fq_set_si :: Ptr CFq -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_set_ui/ /rop/ /x/ /ctx/ 
-- 
-- Sets @rop@ to @x@, considered as an element of \(\mathbf{F}_p\).
foreign import ccall "fq.h fq_set_ui"
  fq_set_ui :: Ptr CFq -> CULong -> Ptr CFqCtx -> IO ()

-- | /fq_set_fmpz/ /rop/ /x/ /ctx/ 
-- 
-- Sets @rop@ to @x@, considered as an element of \(\mathbf{F}_p\).
foreign import ccall "fq.h fq_set_fmpz"
  fq_set_fmpz :: Ptr CFq -> Ptr CFmpz -> Ptr CFqCtx -> IO ()

-- | /fq_swap/ /op1/ /op2/ /ctx/ 
-- 
-- Swaps the two elements @op1@ and @op2@.
foreign import ccall "fq.h fq_swap"
  fq_swap :: Ptr CFq -> Ptr CFq -> Ptr CFqCtx -> IO ()

-- | /fq_zero/ /rop/ /ctx/ 
-- 
-- Sets @rop@ to zero.
foreign import ccall "fq.h fq_zero"
  fq_zero :: Ptr CFq -> Ptr CFqCtx -> IO ()

-- | /fq_one/ /rop/ /ctx/ 
-- 
-- Sets @rop@ to one, reduced in the given context.
foreign import ccall "fq.h fq_one"
  fq_one :: Ptr CFq -> Ptr CFqCtx -> IO ()

-- | /fq_gen/ /rop/ /ctx/ 
-- 
-- Sets @rop@ to a generator for the finite field. There is no guarantee
-- this is a multiplicative generator of the finite field.
foreign import ccall "fq.h fq_gen"
  fq_gen :: Ptr CFq -> Ptr CFqCtx -> IO ()

-- | /fq_get_fmpz/ /rop/ /op/ /ctx/ 
-- 
-- If @op@ has a lift to the integers, return \(1\) and set @rop@ to the
-- lift in \([0,p)\). Otherwise, return \(0\) and leave \(rop\) undefined.
foreign import ccall "fq.h fq_get_fmpz"
  fq_get_fmpz :: Ptr CFmpz -> Ptr CFq -> Ptr CFqCtx -> IO CInt

foreign import ccall "fq.h fq_get_fmpz_poly"
  fq_get_fmpz_poly :: Ptr CFmpzPoly -> Ptr CFq -> Ptr CFqCtx -> IO ()

-- | /fq_get_fmpz_mod_poly/ /a/ /b/ /ctx/ 
-- 
-- Set @a@ to a representative of @b@ in @ctx@. The representatives are
-- taken in \((\mathbb{Z}/p\mathbb{Z})[x]/h(x)\) where \(h(x)\) is the
-- defining polynomial in @ctx@.
foreign import ccall "fq.h fq_get_fmpz_mod_poly"
  fq_get_fmpz_mod_poly :: Ptr CFmpzModPoly -> Ptr CFq -> Ptr CFqCtx -> IO ()

foreign import ccall "fq.h fq_set_fmpz_poly"
  fq_set_fmpz_poly :: Ptr CFq -> Ptr CFmpzPoly -> Ptr CFqCtx -> IO ()

-- | /fq_set_fmpz_mod_poly/ /a/ /b/ /ctx/ 
-- 
-- Set @a@ to the element in @ctx@ with representative @b@. The
-- representatives are taken in \((\mathbb{Z}/p\mathbb{Z})[x]/h(x)\) where
-- \(h(x)\) is the defining polynomial in @ctx@.
foreign import ccall "fq.h fq_set_fmpz_mod_poly"
  fq_set_fmpz_mod_poly :: Ptr CFq -> Ptr CFmpzModPoly -> Ptr CFqCtx -> IO ()

-- | /fq_get_fmpz_mod_mat/ /col/ /a/ /ctx/ 
-- 
-- Convert @a@ to a column vector of length @degree(ctx)@.
foreign import ccall "fq.h fq_get_fmpz_mod_mat"
  fq_get_fmpz_mod_mat :: Ptr CFmpzModMat -> Ptr CFq -> Ptr CFqCtx -> IO ()

-- | /fq_set_fmpz_mod_mat/ /a/ /col/ /ctx/ 
-- 
-- Convert a column vector @col@ of length @degree(ctx)@ to an element of
-- @ctx@.
foreign import ccall "fq.h fq_set_fmpz_mod_mat"
  fq_set_fmpz_mod_mat :: Ptr CFq -> Ptr CFmpzModMat -> Ptr CFqCtx -> IO ()

-- Comparison ------------------------------------------------------------------

-- | /fq_is_zero/ /op/ /ctx/ 
-- 
-- Returns whether @op@ is equal to zero.
foreign import ccall "fq.h fq_is_zero"
  fq_is_zero :: Ptr CFq -> Ptr CFqCtx -> IO CInt

-- | /fq_is_one/ /op/ /ctx/ 
-- 
-- Returns whether @op@ is equal to one.
foreign import ccall "fq.h fq_is_one"
  fq_is_one :: Ptr CFq -> Ptr CFqCtx -> IO CInt

-- | /fq_equal/ /op1/ /op2/ /ctx/ 
-- 
-- Returns whether @op1@ and @op2@ are equal.
foreign import ccall "fq.h fq_equal"
  fq_equal :: Ptr CFq -> Ptr CFq -> Ptr CFqCtx -> IO CInt

-- | /fq_is_invertible/ /op/ /ctx/ 
-- 
-- Returns whether @op@ is an invertible element.
foreign import ccall "fq.h fq_is_invertible"
  fq_is_invertible :: Ptr CFq -> Ptr CFqCtx -> IO CInt

-- | /fq_is_invertible_f/ /f/ /op/ /ctx/ 
-- 
-- Returns whether @op@ is an invertible element. If it is not, then @f@ is
-- set of a factor of the modulus.
foreign import ccall "fq.h fq_is_invertible_f"
  fq_is_invertible_f :: Ptr CFq -> Ptr CFq -> Ptr CFqCtx -> IO CInt

-- Special functions -----------------------------------------------------------

-- | /_fq_trace/ /rop/ /op/ /len/ /ctx/ 
-- 
-- Sets @rop@ to the trace of the non-zero element @(op, len)@ in
-- \(\mathbf{F}_{q}\).
foreign import ccall "fq.h _fq_trace"
  _fq_trace :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_trace/ /rop/ /op/ /ctx/ 
-- 
-- Sets @rop@ to the trace of @op@.
-- 
-- For an element \(a \in \mathbf{F}_q\), multiplication by \(a\) defines a
-- \(\mathbf{F}_p\)-linear map on \(\mathbf{F}_q\). We define the trace of
-- \(a\) as the trace of this map. Equivalently, if \(\Sigma\) generates
-- \(\operatorname{Gal}(\mathbf{F}_q / \mathbf{F}_p)\) then the trace of
-- \(a\) is equal to \(\sum_{i=0}^{d-1} \Sigma^i (a)\), where \(d =
-- \log_{p} q\).
foreign import ccall "fq.h fq_trace"
  fq_trace :: Ptr CFmpz -> Ptr CFq -> Ptr CFqCtx -> IO ()

-- | /_fq_norm/ /rop/ /op/ /len/ /ctx/ 
-- 
-- Sets @rop@ to the norm of the non-zero element @(op, len)@ in
-- \(\mathbf{F}_{q}\).
foreign import ccall "fq.h _fq_norm"
  _fq_norm :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_norm/ /rop/ /op/ /ctx/ 
-- 
-- Computes the norm of @op@.
-- 
-- For an element \(a \in \mathbf{F}_q\), multiplication by \(a\) defines a
-- \(\mathbf{F}_p\)-linear map on \(\mathbf{F}_q\). We define the norm of
-- \(a\) as the determinant of this map. Equivalently, if \(\Sigma\)
-- generates \(\operatorname{Gal}(\mathbf{F}_q / \mathbf{F}_p)\) then the
-- trace of \(a\) is equal to \(\prod_{i=0}^{d-1} \Sigma^i (a)\), where
-- \(d = \text{dim}_{\mathbf{F}_p}(\mathbf{F}_q)\).
-- 
-- Algorithm selection is automatic depending on the input.
foreign import ccall "fq.h fq_norm"
  fq_norm :: Ptr CFmpz -> Ptr CFq -> Ptr CFqCtx -> IO ()

-- | /_fq_frobenius/ /rop/ /op/ /len/ /e/ /ctx/ 
-- 
-- Sets @(rop, 2d-1)@ to the image of @(op, len)@ under the Frobenius
-- operator raised to the e-th power, assuming that neither @op@ nor @e@
-- are zero.
foreign import ccall "fq.h _fq_frobenius"
  _fq_frobenius :: Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_frobenius/ /rop/ /op/ /e/ /ctx/ 
-- 
-- Evaluates the homomorphism \(\Sigma^e\) at @op@.
-- 
-- Recall that \(\mathbf{F}_q / \mathbf{F}_p\) is Galois with Galois group
-- \(\langle \sigma \rangle\), which is also isomorphic to
-- \(\mathbf{Z}/d\mathbf{Z}\), where
-- \(\sigma \in \operatorname{Gal}(\mathbf{F}_q/\mathbf{F}_p)\) is the
-- Frobenius element \(\sigma \colon x \mapsto x^p\).
foreign import ccall "fq.h fq_frobenius"
  fq_frobenius :: Ptr CFq -> Ptr CFq -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_multiplicative_order/ /ord/ /op/ /ctx/ 
-- 
-- Computes the order of @op@ as an element of the multiplicative group of
-- @ctx@.
-- 
-- Returns 0 if @op@ is 0, otherwise it returns 1 if @op@ is a generator of
-- the multiplicative group, and -1 if it is not.
-- 
-- This function can also be used to check primitivity of a generator of a
-- finite field whose defining polynomial is not primitive.
foreign import ccall "fq.h fq_multiplicative_order"
  fq_multiplicative_order :: Ptr CFmpz -> Ptr CFq -> Ptr CFqCtx -> IO CInt

-- | /fq_is_primitive/ /op/ /ctx/ 
-- 
-- Returns whether @op@ is primitive, i.e., whether it is a generator of
-- the multiplicative group of @ctx@.
foreign import ccall "fq.h fq_is_primitive"
  fq_is_primitive :: Ptr CFq -> Ptr CFqCtx -> IO CInt

-- Bit packing -----------------------------------------------------------------

-- | /fq_bit_pack/ /f/ /op/ /bit_size/ /ctx/ 
-- 
-- Packs @op@ into bitfields of size @bit_size@, writing the result to @f@.
foreign import ccall "fq.h fq_bit_pack"
  fq_bit_pack :: Ptr CFmpz -> Ptr CFq -> CFBitCnt -> Ptr CFqCtx -> IO ()

-- | /fq_bit_unpack/ /rop/ /f/ /bit_size/ /ctx/ 
-- 
-- Unpacks into @rop@ the element with coefficients packed into fields of
-- size @bit_size@ as represented by the integer @f@.
foreign import ccall "fq.h fq_bit_unpack"
  fq_bit_unpack :: Ptr CFq -> Ptr CFmpz -> CFBitCnt -> Ptr CFqCtx -> IO ()

