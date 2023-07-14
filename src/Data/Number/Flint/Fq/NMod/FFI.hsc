module Data.Number.Flint.Fq.NMod.FFI (
  -- * Finite fields (word-size characteristic)
    FqNMod (..)
  , CFqNMod (..)
  , newFqNMod
  , withFqNMod
  -- * Context
  , FqNModCtx (..)
  , CFqNModCtx (..)
  , newFqNModCtx
  , newFqNModCtxConway
  , newFqNModCtxModulus
  , withFqNModCtx
  -- * Context Management
  , fq_nmod_ctx_init
  , _fq_nmod_ctx_init_conway
  , fq_nmod_ctx_init_conway
  , fq_nmod_ctx_init_modulus
  , fq_nmod_ctx_clear
  , fq_nmod_ctx_modulus
  , fq_nmod_ctx_degree
  -- , fq_nmod_ctx_prime
  , fq_nmod_ctx_order
  , fq_nmod_ctx_fprint
  , fq_nmod_ctx_print
  , fq_nmod_ctx_randtest
  , fq_nmod_ctx_randtest_reducible
  -- * Memory management
  , fq_nmod_init
  , fq_nmod_init2
  , fq_nmod_clear
  , _fq_nmod_sparse_reduce
  , _fq_nmod_dense_reduce
  , _fq_nmod_reduce
  , fq_nmod_reduce
  -- * Basic arithmetic
  , fq_nmod_add
  , fq_nmod_sub
  , fq_nmod_sub_one
  , fq_nmod_neg
  , fq_nmod_mul
  , fq_nmod_mul_fmpz
  , fq_nmod_mul_si
  , fq_nmod_mul_ui
  , fq_nmod_sqr
  , _fq_nmod_inv
  , fq_nmod_inv
  , fq_nmod_gcdinv
  , _fq_nmod_pow
  , fq_nmod_pow
  , fq_nmod_pow_ui
  -- * Roots
  , fq_nmod_sqrt
  , fq_nmod_pth_root
  , fq_nmod_is_square
  -- * Output
  , fq_nmod_fprint_pretty
  , fq_nmod_print_pretty
  , fq_nmod_fprint
  , fq_nmod_print
  , fq_nmod_get_str
  , fq_nmod_get_str_pretty
  -- * Randomisation
  , fq_nmod_randtest
  , fq_nmod_randtest_not_zero
  , fq_nmod_randtest_dense
  , fq_nmod_rand
  , fq_nmod_rand_not_zero
  -- * Assignments and conversions
  , fq_nmod_set
  , fq_nmod_set_si
  , fq_nmod_set_ui
  , fq_nmod_set_fmpz
  , fq_nmod_swap
  , fq_nmod_zero
  , fq_nmod_one
  , fq_nmod_gen
  , fq_nmod_get_fmpz
  , fq_nmod_get_nmod_poly
  , fq_nmod_set_nmod_poly
  , fq_nmod_get_nmod_mat
  , fq_nmod_set_nmod_mat
  -- * Comparison
  , fq_nmod_is_zero
  , fq_nmod_is_one
  , fq_nmod_equal
  , fq_nmod_is_invertible
  , fq_nmod_is_invertible_f
  , fq_nmod_cmp
  -- * Special functions
  , _fq_nmod_trace
  , fq_nmod_trace
  , _fq_nmod_norm
  , fq_nmod_norm
  , _fq_nmod_frobenius
  , fq_nmod_frobenius
  , fq_nmod_multiplicative_order
  , fq_nmod_is_primitive
  -- * Bit packing
  , fq_nmod_bit_pack
  , fq_nmod_bit_unpack
) where

-- Finite fields (word-size characteristic) ------------------------------------

import Foreign.C.String
import Foreign.C.Types
import qualified Foreign.Concurrent
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr, castPtr )
import Foreign.Storable
import Foreign.Marshal ( free )

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.NMod
import Data.Number.Flint.NMod.Types

#include <flint/flint.h>

#include <flint/fq_nmod.h>

-- fq_nmod_t -------------------------------------------------------------------

data FqNMod = FqNMod {-# UNPACK #-} !(ForeignPtr CFqNMod)
type CFqNMod = CFlint FqNMod

instance Storable CFqNMod where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fq_nmod_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fq_nmod_t}
  peek = undefined
  poke = undefined

newFqNMod ctx@(FqNModCtx ftx) = do
  x <- mallocForeignPtr
  withForeignPtr x$ \x -> do
    withFqNModCtx ctx $ \ctx -> do
      fq_nmod_init x ctx
    addForeignPtrFinalizerEnv p_fq_nmod_clear x ftx
  return $ FqNMod x

{-# INLINE withFqNMod #-}
withFqNMod (FqNMod x) f = do
  withForeignPtr x $ \px -> f px >>= return . (FqNMod x,)

-- fq_nmod_ctx_t ---------------------------------------------------------------

data FqNModCtx = FqNModCtx {-# UNPACK #-} !(ForeignPtr CFqNModCtx)
data CFqNModCtx = CFqNModCtx (Ptr CFmpz) (Ptr CNMod) CInt CInt (Ptr CMpLimb) (Ptr CLong) (Ptr CLong) (Ptr CNModPoly) (Ptr CNModPoly) CString 

instance Storable CFqNModCtx where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fq_nmod_ctx_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fq_nmod_ctx_t}
  peek ptr = CFqNModCtx
    <$> (return $ castPtr ptr)
    <*> #{peek fq_nmod_ctx_struct, mod           } ptr
    <*> #{peek fq_nmod_ctx_struct, sparse_modulus} ptr
    <*> #{peek fq_nmod_ctx_struct, is_conway     } ptr
    <*> #{peek fq_nmod_ctx_struct, a             } ptr
    <*> #{peek fq_nmod_ctx_struct, j             } ptr
    <*> #{peek fq_nmod_ctx_struct, len           } ptr
    <*> #{peek fq_nmod_ctx_struct, modulus       } ptr
    <*> #{peek fq_nmod_ctx_struct, inv           } ptr
    <*> #{peek fq_nmod_ctx_struct, var           } ptr
  poke = undefined

newFqNModCtx p d var = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x ->
    withFmpz p $ \p -> 
      withCString var $ \var -> 
        fq_nmod_ctx_init x p d var
  addForeignPtrFinalizer p_fq_nmod_ctx_clear x
  return $ FqNModCtx x

newFqNModCtxConway p d var = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x ->
    withFmpz p $ \p -> 
      withCString var $ \var -> 
        fq_nmod_ctx_init_conway x p d var
  addForeignPtrFinalizer p_fq_nmod_ctx_clear x
  return $ FqNModCtx x

newFqNModCtxModulus modulus var = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x ->
    withCString var $ \var ->
      fq_nmod_ctx_init_modulus x modulus var 
  addForeignPtrFinalizer p_fq_nmod_ctx_clear x
  return $ FqNModCtx x
  
{-# INLINE withFqNModCtx #-}
withFqNModCtx (FqNModCtx x) f = do
  withForeignPtr x $ \px -> f px >>= return . (FqNModCtx x,)

-- Context Management ----------------------------------------------------------

-- | /fq_nmod_ctx_init/ /ctx/ /p/ /d/ /var/ 
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
foreign import ccall "fq_nmod.h fq_nmod_ctx_init"
  fq_nmod_ctx_init :: Ptr CFqNModCtx -> Ptr CFmpz -> CLong -> CString -> IO ()

-- | /_fq_nmod_ctx_init_conway/ /ctx/ /p/ /d/ /var/ 
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
foreign import ccall "fq_nmod.h _fq_nmod_ctx_init_conway"
  _fq_nmod_ctx_init_conway :: Ptr CFqNModCtx -> Ptr CFmpz -> CLong -> CString -> IO CInt

-- | /fq_nmod_ctx_init_conway/ /ctx/ /p/ /d/ /var/ 
--
-- Initialises the context for prime \(p\) and extension degree \(d\), with
-- name @var@ for the generator using a Conway polynomial for the modulus.
-- 
-- Assumes that \(p\) is a prime.
-- 
-- Assumes that the string @var@ is a null-terminated string of length at
-- least one.
foreign import ccall "fq_nmod.h fq_nmod_ctx_init_conway"
  fq_nmod_ctx_init_conway :: Ptr CFqNModCtx -> Ptr CFmpz -> CLong -> CString -> IO ()

-- | /fq_nmod_ctx_init_modulus/ /ctx/ /modulus/ /var/ 
--
-- Initialises the context for given @modulus@ with name @var@ for the
-- generator.
-- 
-- Assumes that @modulus@ is an irreducible polynomial over
-- \(\mathbf{F}_{p}\).
-- 
-- Assumes that the string @var@ is a null-terminated string of length at
-- least one.
foreign import ccall "fq_nmod.h fq_nmod_ctx_init_modulus"
  fq_nmod_ctx_init_modulus :: Ptr CFqNModCtx -> Ptr CNModPoly -> CString -> IO ()

-- | /fq_nmod_ctx_clear/ /ctx/ 
--
-- Clears all memory that has been allocated as part of the context.
foreign import ccall "fq_nmod.h fq_nmod_ctx_clear"
  fq_nmod_ctx_clear :: Ptr CFqNModCtx -> IO ()

foreign import ccall "fq_nmod.h &fq_nmod_ctx_clear"
  p_fq_nmod_ctx_clear :: FunPtr (Ptr CFqNModCtx -> IO ())

-- | /fq_nmod_ctx_modulus/ /ctx/ 
--
-- Returns a pointer to the modulus in the context.
foreign import ccall "fq_nmod.h fq_nmod_ctx_modulus"
  fq_nmod_ctx_modulus :: Ptr CFqNModCtx -> IO (Ptr (Ptr CNModPoly))

-- | /fq_nmod_ctx_degree/ /ctx/ 
--
-- Returns the degree of the field extension
-- \([\mathbf{F}_{q} : \mathbf{F}_{p}]\), which is equal to \(\log_{p} q\).
foreign import ccall "fq_nmod.h fq_nmod_ctx_degree"
  fq_nmod_ctx_degree :: Ptr CFqNModCtx -> IO CLong

-- | /fq_nmod_ctx_prime/ /ctx/ 
--
-- Returns a pointer to the prime \(p\) in the context.
-- foreign import ccall "fq_nmod.h fq_nmod_ctx_prime"
fq_nmod_ctx_prime :: Ptr CFqNModCtx -> IO (Ptr CFmpz)
fq_nmod_ctx_prime ctx = do
  CFqNModCtx p _ _ _ _ _ _ _ _ _ <- peek ctx
  return p
  
-- | /fq_nmod_ctx_order/ /f/ /ctx/ 
--
-- Sets \(f\) to be the size of the finite field.
foreign import ccall "fq_nmod.h fq_nmod_ctx_order"
  fq_nmod_ctx_order :: Ptr CFmpz -> Ptr CFqNModCtx -> IO ()

-- Input and Output ------------------------------------------------------------

-- | /fq_nmod_ctx_get_str/ /ctx/ 
--
-- Return a string representation of the context information. 
foreign import ccall "fq_nmod.h fq_nmod_ctx_get_str"
  fq_nmod_ctx_get_str :: Ptr CFqNModCtx -> IO CString
  
-- | /fq_nmod_ctx_fprint/ /file/ /ctx/ 
--
-- Prints the context information to @file@. Returns 1 for a success and a
-- negative number for an error.
foreign import ccall "fq_nmod.h fq_nmod_ctx_fprint"
  fq_nmod_ctx_fprint :: Ptr CFile -> Ptr CFqNModCtx -> IO CInt

-- | /fq_nmod_ctx_print/ /ctx/ 
--
-- Prints the context information to @stdout@.
fq_nmod_ctx_print :: Ptr CFqNModCtx -> IO ()
fq_nmod_ctx_print ctx = do
  printCStr fq_nmod_ctx_get_str ctx
  return ()

-- | /fq_nmod_ctx_randtest/ /ctx/ 
--
-- Initializes @ctx@ to a random finite field. Assumes that
-- @fq_nmod_ctx_init@ has not been called on @ctx@ already.
foreign import ccall "fq_nmod.h fq_nmod_ctx_randtest"
  fq_nmod_ctx_randtest :: Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_ctx_randtest_reducible/ /ctx/ 
--
-- Initializes @ctx@ to a random extension of a word-sized prime field. The
-- modulus may or may not be irreducible. Assumes that @fq_nmod_ctx_init@
-- has not been called on @ctx@ already.
foreign import ccall "fq_nmod.h fq_nmod_ctx_randtest_reducible"
  fq_nmod_ctx_randtest_reducible :: Ptr CFqNModCtx -> IO ()

-- Memory management -----------------------------------------------------------

-- | /fq_nmod_init/ /rop/ /ctx/ 
--
-- Initialises the element @rop@, setting its value to \(0\). Currently,
-- the behaviour is identical to @fq_nmod_init2@, as it also ensures @rop@
-- has enough space for it to be an element of @ctx@, this may change in
-- the future.
foreign import ccall "fq_nmod.h fq_nmod_init"
  fq_nmod_init :: Ptr CFqNMod -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_init2/ /rop/ /ctx/ 
--
-- Initialises @rop@ with at least enough space for it to be an element of
-- @ctx@ and sets it to \(0\).
foreign import ccall "fq_nmod.h fq_nmod_init2"
  fq_nmod_init2 :: Ptr CFqNMod -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_clear/ /rop/ /ctx/ 
--
-- Clears the element @rop@.
foreign import ccall "fq_nmod.h fq_nmod_clear"
  fq_nmod_clear :: Ptr CFqNMod -> Ptr CFqNModCtx -> IO ()

foreign import ccall "fq_nmod.h &fq_nmod_clear"
  p_fq_nmod_clear :: FunPtr (Ptr CFqNMod -> Ptr CFqNModCtx -> IO ())

-- | /_fq_nmod_sparse_reduce/ /R/ /lenR/ /ctx/ 
--
-- Reduces @(R, lenR)@ modulo the polynomial \(f\) given by the modulus of
-- @ctx@.
foreign import ccall "fq_nmod.h _fq_nmod_sparse_reduce"
  _fq_nmod_sparse_reduce :: Ptr CMp -> CLong -> Ptr CFqNModCtx -> IO ()

-- | /_fq_nmod_dense_reduce/ /R/ /lenR/ /ctx/ 
--
-- Reduces @(R, lenR)@ modulo the polynomial \(f\) given by the modulus of
-- @ctx@ using Newton division.
foreign import ccall "fq_nmod.h _fq_nmod_dense_reduce"
  _fq_nmod_dense_reduce :: Ptr CMp -> CLong -> Ptr CFqNModCtx -> IO ()

-- | /_fq_nmod_reduce/ /r/ /lenR/ /ctx/ 
--
-- Reduces @(R, lenR)@ modulo the polynomial \(f\) given by the modulus of
-- @ctx@. Does either sparse or dense reduction based on
-- @ctx->sparse_modulus@.
foreign import ccall "fq_nmod.h _fq_nmod_reduce"
  _fq_nmod_reduce :: Ptr CMp -> CLong -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_reduce/ /rop/ /ctx/ 
--
-- Reduces the polynomial @rop@ as an element of
-- \(\mathbf{F}_p[X] / (f(X))\).
foreign import ccall "fq_nmod.h fq_nmod_reduce"
  fq_nmod_reduce :: Ptr CFqNMod -> Ptr CFqNModCtx -> IO ()

-- Basic arithmetic ------------------------------------------------------------

-- | /fq_nmod_add/ /rop/ /op1/ /op2/ /ctx/ 
--
-- Sets @rop@ to the sum of @op1@ and @op2@.
foreign import ccall "fq_nmod.h fq_nmod_add"
  fq_nmod_add :: Ptr CFqNMod -> Ptr CFqNMod -> Ptr CFqNMod -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_sub/ /rop/ /op1/ /op2/ /ctx/ 
--
-- Sets @rop@ to the difference of @op1@ and @op2@.
foreign import ccall "fq_nmod.h fq_nmod_sub"
  fq_nmod_sub :: Ptr CFqNMod -> Ptr CFqNMod -> Ptr CFqNMod -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_sub_one/ /rop/ /op1/ /ctx/ 
--
-- Sets @rop@ to the difference of @op1@ and \(1\).
foreign import ccall "fq_nmod.h fq_nmod_sub_one"
  fq_nmod_sub_one :: Ptr CFqNMod -> Ptr CFqNMod -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_neg/ /rop/ /op/ /ctx/ 
--
-- Sets @rop@ to the negative of @op@.
foreign import ccall "fq_nmod.h fq_nmod_neg"
  fq_nmod_neg :: Ptr CFqNMod -> Ptr CFqNMod -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_mul/ /rop/ /op1/ /op2/ /ctx/ 
--
-- Sets @rop@ to the product of @op1@ and @op2@, reducing the output in the
-- given context.
foreign import ccall "fq_nmod.h fq_nmod_mul"
  fq_nmod_mul :: Ptr CFqNMod -> Ptr CFqNMod -> Ptr CFqNMod -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_mul_fmpz/ /rop/ /op/ /x/ /ctx/ 
--
-- Sets @rop@ to the product of @op@ and \(x\), reducing the output in the
-- given context.
foreign import ccall "fq_nmod.h fq_nmod_mul_fmpz"
  fq_nmod_mul_fmpz :: Ptr CFqNMod -> Ptr CFqNMod -> Ptr CFmpz -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_mul_si/ /rop/ /op/ /x/ /ctx/ 
--
-- Sets @rop@ to the product of @op@ and \(x\), reducing the output in the
-- given context.
foreign import ccall "fq_nmod.h fq_nmod_mul_si"
  fq_nmod_mul_si :: Ptr CFqNMod -> Ptr CFqNMod -> CLong -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_mul_ui/ /rop/ /op/ /x/ /ctx/ 
--
-- Sets @rop@ to the product of @op@ and \(x\), reducing the output in the
-- given context.
foreign import ccall "fq_nmod.h fq_nmod_mul_ui"
  fq_nmod_mul_ui :: Ptr CFqNMod -> Ptr CFqNMod -> CULong -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_sqr/ /rop/ /op/ /ctx/ 
--
-- Sets @rop@ to the square of @op@, reducing the output in the given
-- context.
foreign import ccall "fq_nmod.h fq_nmod_sqr"
  fq_nmod_sqr :: Ptr CFqNMod -> Ptr CFqNMod -> Ptr CFqNModCtx -> IO ()

-- | /_fq_nmod_inv/ /rop/ /op/ /len/ /ctx/ 
--
-- Sets @(rop, d)@ to the inverse of the non-zero element @(op, len)@.
foreign import ccall "fq_nmod.h _fq_nmod_inv"
  _fq_nmod_inv :: Ptr (Ptr CMp) -> Ptr (Ptr CMp) -> CLong -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_inv/ /rop/ /op/ /ctx/ 
--
-- Sets @rop@ to the inverse of the non-zero element @op@.
foreign import ccall "fq_nmod.h fq_nmod_inv"
  fq_nmod_inv :: Ptr CFqNMod -> Ptr CFqNMod -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_gcdinv/ /f/ /inv/ /op/ /ctx/ 
--
-- Sets @inv@ to be the inverse of @op@ modulo the modulus of @ctx@. If
-- @op@ is not invertible, then @f@ is set to a factor of the modulus;
-- otherwise, it is set to one.
foreign import ccall "fq_nmod.h fq_nmod_gcdinv"
  fq_nmod_gcdinv :: Ptr CFqNMod -> Ptr CFqNMod -> Ptr CFqNMod -> Ptr CFqNModCtx -> IO ()

-- | /_fq_nmod_pow/ /rop/ /op/ /len/ /e/ /ctx/ 
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
foreign import ccall "fq_nmod.h _fq_nmod_pow"
  _fq_nmod_pow :: Ptr (Ptr CMp) -> Ptr (Ptr CMp) -> CLong -> Ptr CFmpz -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_pow/ /rop/ /op/ /e/ /ctx/ 
--
-- Sets @rop@ to @op@ raised to the power \(e\).
-- 
-- Currently assumes that \(e \geq 0\).
-- 
-- Note that for any input @op@, @rop@ is set to \(1\) whenever \(e = 0\).
foreign import ccall "fq_nmod.h fq_nmod_pow"
  fq_nmod_pow :: Ptr CFqNMod -> Ptr CFqNMod -> Ptr CFmpz -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_pow_ui/ /rop/ /op/ /e/ /ctx/ 
--
-- Sets @rop@ to @op@ raised to the power \(e\).
-- 
-- Currently assumes that \(e \geq 0\).
-- 
-- Note that for any input @op@, @rop@ is set to \(1\) whenever \(e = 0\).
foreign import ccall "fq_nmod.h fq_nmod_pow_ui"
  fq_nmod_pow_ui :: Ptr CFqNMod -> Ptr CFqNMod -> CULong -> Ptr CFqNModCtx -> IO ()

-- Roots -----------------------------------------------------------------------

-- | /fq_nmod_sqrt/ /rop/ /op1/ /ctx/ 
--
-- Sets @rop@ to the square root of @op1@ if it is a square, and return
-- \(1\), otherwise return \(0\).
foreign import ccall "fq_nmod.h fq_nmod_sqrt"
  fq_nmod_sqrt :: Ptr CFqNMod -> Ptr CFqNMod -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_pth_root/ /rop/ /op1/ /ctx/ 
--
-- Sets @rop@ to a \(p^{\textrm{th}}\) root of @op1@. Currently, this
-- computes the root by raising @op1@ to \(p^{d-1}\) where \(d\) is the
-- degree of the extension.
foreign import ccall "fq_nmod.h fq_nmod_pth_root"
  fq_nmod_pth_root :: Ptr CFqNMod -> Ptr CFqNMod -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_is_square/ /op/ /ctx/ 
--
-- Return @1@ if @op@ is a square.
foreign import ccall "fq_nmod.h fq_nmod_is_square"
  fq_nmod_is_square :: Ptr CFqNMod -> Ptr CFqNModCtx -> IO CInt

-- Output ----------------------------------------------------------------------

-- | /fq_nmod_fprint_pretty/ /file/ /op/ /ctx/ 
--
-- Prints a pretty representation of @op@ to @file@.
-- 
-- In case of success, returns a positive value. In case of failure,
-- returns a non-positive value.
foreign import ccall "fq_nmod.h fq_nmod_fprint_pretty"
  fq_nmod_fprint_pretty :: Ptr CFile -> Ptr CFqNMod -> Ptr CFqNModCtx -> IO CInt

-- | /fq_nmod_print_pretty/ /op/ /ctx/ 
--
-- Prints a pretty representation of @op@ to @stdout@.
-- 
-- In case of success, returns a positive value. In case of failure,
-- returns a non-positive value.
fq_nmod_print_pretty :: Ptr CFqNMod -> Ptr CFqNModCtx -> IO CInt
fq_nmod_print_pretty op ctx = do
  printCStr (`fq_nmod_get_str_pretty` ctx) op

-- | /fq_nmod_fprint/ /file/ /op/ /ctx/ 
--
-- Prints a representation of @op@ to @file@.
-- 
-- For further details on the representation used, see
-- @nmod_poly_fprint()@.
foreign import ccall "fq_nmod.h fq_nmod_fprint"
  fq_nmod_fprint :: Ptr CFile -> Ptr CFqNMod -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_print/ /op/ /ctx/ 
--
-- Prints a representation of @op@ to @stdout@.
-- 
-- For further details on the representation used, see @nmod_poly_print()@.
fq_nmod_print :: Ptr CFqNMod -> Ptr CFqNModCtx -> IO ()
fq_nmod_print op ctx = do
  printCStr (`fq_nmod_get_str` ctx) op
  return ()

-- | /fq_nmod_get_str/ /op/ /ctx/ 
--
-- Returns the plain FLINT string representation of the element @op@.
foreign import ccall "fq_nmod.h fq_nmod_get_str"
  fq_nmod_get_str :: Ptr CFqNMod -> Ptr CFqNModCtx -> IO CString

-- | /fq_nmod_get_str_pretty/ /op/ /ctx/ 
--
-- Returns a pretty representation of the element @op@ using the
-- null-terminated string @x@ as the variable name.
foreign import ccall "fq_nmod.h fq_nmod_get_str_pretty"
  fq_nmod_get_str_pretty :: Ptr CFqNMod -> Ptr CFqNModCtx -> IO CString

-- Randomisation ---------------------------------------------------------------

-- | /fq_nmod_randtest/ /rop/ /state/ /ctx/ 
--
-- Generates a random element of \(\mathbf{F}_q\).
foreign import ccall "fq_nmod.h fq_nmod_randtest"
  fq_nmod_randtest :: Ptr CFqNMod -> Ptr CFRandState -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_randtest_not_zero/ /rop/ /state/ /ctx/ 
--
-- Generates a random non-zero element of \(\mathbf{F}_q\).
foreign import ccall "fq_nmod.h fq_nmod_randtest_not_zero"
  fq_nmod_randtest_not_zero :: Ptr CFqNMod -> Ptr CFRandState -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_randtest_dense/ /rop/ /state/ /ctx/ 
--
-- Generates a random element of \(\mathbf{F}_q\) which has an underlying
-- polynomial with dense coefficients.
foreign import ccall "fq_nmod.h fq_nmod_randtest_dense"
  fq_nmod_randtest_dense :: Ptr CFqNMod -> Ptr CFRandState -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_rand/ /rop/ /state/ /ctx/ 
--
-- Generates a high quality random element of \(\mathbf{F}_q\).
foreign import ccall "fq_nmod.h fq_nmod_rand"
  fq_nmod_rand :: Ptr CFqNMod -> Ptr CFRandState -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_rand_not_zero/ /rop/ /state/ /ctx/ 
--
-- Generates a high quality non-zero random element of \(\mathbf{F}_q\).
foreign import ccall "fq_nmod.h fq_nmod_rand_not_zero"
  fq_nmod_rand_not_zero :: Ptr CFqNMod -> Ptr CFRandState -> Ptr CFqNModCtx -> IO ()

-- Assignments and conversions -------------------------------------------------

-- | /fq_nmod_set/ /rop/ /op/ /ctx/ 
--
-- Sets @rop@ to @op@.
foreign import ccall "fq_nmod.h fq_nmod_set"
  fq_nmod_set :: Ptr CFqNMod -> Ptr CFqNMod -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_set_si/ /rop/ /x/ /ctx/ 
--
-- Sets @rop@ to @x@, considered as an element of \(\mathbf{F}_p\).
foreign import ccall "fq_nmod.h fq_nmod_set_si"
  fq_nmod_set_si :: Ptr CFqNMod -> CLong -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_set_ui/ /rop/ /x/ /ctx/ 
--
-- Sets @rop@ to @x@, considered as an element of \(\mathbf{F}_p\).
foreign import ccall "fq_nmod.h fq_nmod_set_ui"
  fq_nmod_set_ui :: Ptr CFqNMod -> CULong -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_set_fmpz/ /rop/ /x/ /ctx/ 
--
-- Sets @rop@ to @x@, considered as an element of \(\mathbf{F}_p\).
foreign import ccall "fq_nmod.h fq_nmod_set_fmpz"
  fq_nmod_set_fmpz :: Ptr CFqNMod -> Ptr CFmpz -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_swap/ /op1/ /op2/ /ctx/ 
--
-- Swaps the two elements @op1@ and @op2@.
foreign import ccall "fq_nmod.h fq_nmod_swap"
  fq_nmod_swap :: Ptr CFqNMod -> Ptr CFqNMod -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_zero/ /rop/ /ctx/ 
--
-- Sets @rop@ to zero.
foreign import ccall "fq_nmod.h fq_nmod_zero"
  fq_nmod_zero :: Ptr CFqNMod -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_one/ /rop/ /ctx/ 
--
-- Sets @rop@ to one, reduced in the given context.
foreign import ccall "fq_nmod.h fq_nmod_one"
  fq_nmod_one :: Ptr CFqNMod -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_gen/ /rop/ /ctx/ 
--
-- Sets @rop@ to a generator for the finite field. There is no guarantee
-- this is a multiplicative generator of the finite field.
foreign import ccall "fq_nmod.h fq_nmod_gen"
  fq_nmod_gen :: Ptr CFqNMod -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_get_fmpz/ /rop/ /op/ /ctx/ 
--
-- If @op@ has a lift to the integers, return \(1\) and set @rop@ to the
-- lift in \([0,p)\). Otherwise, return \(0\) and leave \(rop\) undefined.
foreign import ccall "fq_nmod.h fq_nmod_get_fmpz"
  fq_nmod_get_fmpz :: Ptr CFmpz -> Ptr CFqNMod -> Ptr CFqNModCtx -> IO CInt

-- | /fq_nmod_get_nmod_poly/ /a/ /b/ /ctx/ 
--
-- Set @a@ to a representative of @b@ in @ctx@. The representatives are
-- taken in \((\mathbb{Z}/p\mathbb{Z})[x]/h(x)\) where \(h(x)\) is the
-- defining polynomial in @ctx@.
foreign import ccall "fq_nmod.h fq_nmod_get_nmod_poly"
  fq_nmod_get_nmod_poly :: Ptr CNModPoly -> Ptr CFqNMod -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_set_nmod_poly/ /a/ /b/ /ctx/ 
--
-- Set @a@ to the element in @ctx@ with representative @b@. The
-- representatives are taken in \((\mathbb{Z}/p\mathbb{Z})[x]/h(x)\) where
-- \(h(x)\) is the defining polynomial in @ctx@.
foreign import ccall "fq_nmod.h fq_nmod_set_nmod_poly"
  fq_nmod_set_nmod_poly :: Ptr CFqNMod -> Ptr CNModPoly -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_get_nmod_mat/ /col/ /a/ /ctx/ 
--
-- Convert @a@ to a column vector of length @degree(ctx)@.
foreign import ccall "fq_nmod.h fq_nmod_get_nmod_mat"
  fq_nmod_get_nmod_mat :: Ptr CNModMat -> Ptr CFqNMod -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_set_nmod_mat/ /a/ /col/ /ctx/ 
--
-- Convert a column vector @col@ of length @degree(ctx)@ to an element of
-- @ctx@.
foreign import ccall "fq_nmod.h fq_nmod_set_nmod_mat"
  fq_nmod_set_nmod_mat :: Ptr CFqNMod -> Ptr CNModMat -> Ptr CFqNModCtx -> IO ()

-- Comparison ------------------------------------------------------------------

-- | /fq_nmod_is_zero/ /op/ /ctx/ 
--
-- Returns whether @op@ is equal to zero.
foreign import ccall "fq_nmod.h fq_nmod_is_zero"
  fq_nmod_is_zero :: Ptr CFqNMod -> Ptr CFqNModCtx -> IO CInt

-- | /fq_nmod_is_one/ /op/ /ctx/ 
--
-- Returns whether @op@ is equal to one.
foreign import ccall "fq_nmod.h fq_nmod_is_one"
  fq_nmod_is_one :: Ptr CFqNMod -> Ptr CFqNModCtx -> IO CInt

-- | /fq_nmod_equal/ /op1/ /op2/ /ctx/ 
--
-- Returns whether @op1@ and @op2@ are equal.
foreign import ccall "fq_nmod.h fq_nmod_equal"
  fq_nmod_equal :: Ptr CFqNMod -> Ptr CFqNMod -> Ptr CFqNModCtx -> IO CInt

-- | /fq_nmod_is_invertible/ /op/ /ctx/ 
--
-- Returns whether @op@ is an invertible element.
foreign import ccall "fq_nmod.h fq_nmod_is_invertible"
  fq_nmod_is_invertible :: Ptr CFqNMod -> Ptr CFqNModCtx -> IO CInt

-- | /fq_nmod_is_invertible_f/ /f/ /op/ /ctx/ 
--
-- Returns whether @op@ is an invertible element. If it is not, then @f@ is
-- set to a factor of the modulus.
foreign import ccall "fq_nmod.h fq_nmod_is_invertible_f"
  fq_nmod_is_invertible_f :: Ptr CFqNMod -> Ptr CFqNMod -> Ptr CFqNModCtx -> IO CInt

-- | /fq_nmod_cmp/ /a/ /b/ /ctx/ 
--
-- Return @1@ (resp. @-1@, or @0@) if @a@ is after (resp. before, same as)
-- @b@ in some arbitrary but fixed total ordering of the elements.
foreign import ccall "fq_nmod.h fq_nmod_cmp"
  fq_nmod_cmp :: Ptr CFqNMod -> Ptr CFqNMod -> Ptr CFqNModCtx -> IO CInt

-- Special functions -----------------------------------------------------------

-- | /_fq_nmod_trace/ /rop/ /op/ /len/ /ctx/ 
--
-- Sets @rop@ to the trace of the non-zero element @(op, len)@ in
-- \(\mathbf{F}_{q}\).
foreign import ccall "fq_nmod.h _fq_nmod_trace"
  _fq_nmod_trace :: Ptr CFmpz -> Ptr (Ptr CMp) -> CLong -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_trace/ /rop/ /op/ /ctx/ 
--
-- Sets @rop@ to the trace of @op@.
-- 
-- For an element \(a \in \mathbf{F}_q\), multiplication by \(a\) defines a
-- \(\mathbf{F}_p\)-linear map on \(\mathbf{F}_q\). We define the trace of
-- \(a\) as the trace of this map. Equivalently, if \(\Sigma\) generates
-- \(\operatorname{Gal}(\mathbf{F}_q / \mathbf{F}_p)\) then the trace of
-- \(a\) is equal to \(\sum_{i=0}^{d-1} \Sigma^i (a)\), where \(d =
-- \log_{p} q\).
foreign import ccall "fq_nmod.h fq_nmod_trace"
  fq_nmod_trace :: Ptr CFmpz -> Ptr CFqNMod -> Ptr CFqNModCtx -> IO ()

-- | /_fq_nmod_norm/ /rop/ /op/ /len/ /ctx/ 
--
-- Sets @rop@ to the norm of the non-zero element @(op, len)@ in
-- \(\mathbf{F}_{q}\).
foreign import ccall "fq_nmod.h _fq_nmod_norm"
  _fq_nmod_norm :: Ptr CFmpz -> Ptr (Ptr CMp) -> CLong -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_norm/ /rop/ /op/ /ctx/ 
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
foreign import ccall "fq_nmod.h fq_nmod_norm"
  fq_nmod_norm :: Ptr CFmpz -> Ptr CFqNMod -> Ptr CFqNModCtx -> IO ()

-- | /_fq_nmod_frobenius/ /rop/ /op/ /len/ /e/ /ctx/ 
--
-- Sets @(rop, 2d-1)@ to the image of @(op, len)@ under the Frobenius
-- operator raised to the e-th power, assuming that neither @op@ nor @e@
-- are zero.
foreign import ccall "fq_nmod.h _fq_nmod_frobenius"
  _fq_nmod_frobenius :: Ptr (Ptr CMp) -> Ptr (Ptr CMp) -> CLong -> CLong -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_frobenius/ /rop/ /op/ /e/ /ctx/ 
--
-- Evaluates the homomorphism \(\Sigma^e\) at @op@.
-- 
-- Recall that \(\mathbf{F}_q / \mathbf{F}_p\) is Galois with Galois group
-- \(\langle \sigma \rangle\), which is also isomorphic to
-- \(\mathbf{Z}/d\mathbf{Z}\), where
-- \(\sigma \in \operatorname{Gal}(\mathbf{F}_q/\mathbf{F}_p)\) is the
-- Frobenius element \(\sigma \colon x \mapsto x^p\).
foreign import ccall "fq_nmod.h fq_nmod_frobenius"
  fq_nmod_frobenius :: Ptr CFqNMod -> Ptr CFqNMod -> CLong -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_multiplicative_order/ /ord/ /op/ /ctx/ 
--
-- Computes the order of @op@ as an element of the multiplicative group of
-- @ctx@.
-- 
-- Returns 0 if @op@ is 0, otherwise it returns 1 if @op@ is a generator of
-- the multiplicative group, and -1 if it is not.
-- 
-- This function can also be used to check primitivity of a generator of a
-- finite field whose defining polynomial is not primitive.
foreign import ccall "fq_nmod.h fq_nmod_multiplicative_order"
  fq_nmod_multiplicative_order :: Ptr CFmpz -> Ptr CFqNMod -> Ptr CFqNModCtx -> IO CInt

-- | /fq_nmod_is_primitive/ /op/ /ctx/ 
--
-- Returns whether @op@ is primitive, i.e., whether it is a generator of
-- the multiplicative group of @ctx@.
foreign import ccall "fq_nmod.h fq_nmod_is_primitive"
  fq_nmod_is_primitive :: Ptr CFqNMod -> Ptr CFqNModCtx -> IO CInt

-- Bit packing -----------------------------------------------------------------

-- | /fq_nmod_bit_pack/ /f/ /op/ /bit_size/ /ctx/ 
--
-- Packs @op@ into bitfields of size @bit_size@, writing the result to @f@.
foreign import ccall "fq_nmod.h fq_nmod_bit_pack"
  fq_nmod_bit_pack :: Ptr CFmpz -> Ptr CFqNMod -> CFBitCnt -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_bit_unpack/ /rop/ /f/ /bit_size/ /ctx/ 
--
-- Unpacks into @rop@ the element with coefficients packed into fields of
-- size @bit_size@ as represented by the integer @f@.
foreign import ccall "fq_nmod.h fq_nmod_bit_unpack"
  fq_nmod_bit_unpack :: Ptr CFqNMod -> Ptr CFmpz -> CFBitCnt -> Ptr CFqNModCtx -> IO ()

