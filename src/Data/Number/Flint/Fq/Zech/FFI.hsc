{-# language
    CApiFFI
  , FlexibleInstances
  , ForeignFunctionInterface
  , MultiParamTypeClasses
  , TupleSections
  , TypeFamilies
  #-}

module Data.Number.Flint.Fq.Zech.FFI (
  -- * Finite fields (Zech logarithm representation)
    FqZech (..)
  , CFqZech (..)
  , newFqZech
  , withFqZech
  -- * Context
  , FqZechCtx (..)
  , CFqZechCtx (..)
  -- ** create new context
  , newFqZechCtx
  , newFqZechCtxConway
  , newFqZechCtxRandom
  , newFqZechCtxModulus
  , newFqZechCtxModulusCheck
  , newFqZechCtxFqNModCtx
  , newFqZechCtxFqNModCtxCheck
  -- * work with context
  , withFqZechCtx
  -- * Context Management
  , fq_zech_ctx_init
  , _fq_zech_ctx_init_conway
  , fq_zech_ctx_init_conway
  , fq_zech_ctx_init_random
  , fq_zech_ctx_init_modulus
  , fq_zech_ctx_init_modulus_check
  , fq_zech_ctx_init_fq_nmod_ctx
  , fq_zech_ctx_init_fq_nmod_ctx_check
  , fq_zech_ctx_clear
  , fq_zech_ctx_modulus
  , fq_zech_ctx_degree
  --, fq_zech_ctx_prime
  , fq_zech_ctx_order
  , fq_zech_ctx_order_ui
  , fq_zech_ctx_fprint
  , fq_zech_ctx_print
  , fq_zech_ctx_randtest
  , fq_zech_ctx_randtest_reducible
  -- * Memory management
  , fq_zech_init
  , fq_zech_init2
  , fq_zech_clear
  --, _fq_zech_sparse_reduce
  --, _fq_zech_dense_reduce
  --, _fq_zech_reduce
  , fq_zech_reduce
  -- * Basic arithmetic
  , fq_zech_add
  , fq_zech_sub
  , fq_zech_sub_one
  , fq_zech_neg
  , fq_zech_mul
  , fq_zech_mul_fmpz
  , fq_zech_mul_si
  , fq_zech_mul_ui
  , fq_zech_sqr
  , fq_zech_div
  --, _fq_zech_inv
  , fq_zech_inv
  , fq_zech_gcdinv
  --, _fq_zech_pow
  , fq_zech_pow
  , fq_zech_pow_ui
  -- * Roots
  , fq_zech_sqrt
  , fq_zech_pth_root
  , fq_zech_is_square
  -- * Output
  , fq_zech_fprint_pretty
  , fq_zech_print_pretty
  , fq_zech_fprint
  , fq_zech_print
  , fq_zech_get_str
  , fq_zech_get_str_pretty
  -- * Randomisation
  , fq_zech_randtest
  , fq_zech_randtest_not_zero
  --, fq_zech_randtest_dense
  , fq_zech_rand
  , fq_zech_rand_not_zero
  -- * Assignments and conversions
  , fq_zech_set
  , fq_zech_set_si
  , fq_zech_set_ui
  , fq_zech_set_fmpz
  , fq_zech_swap
  , fq_zech_zero
  , fq_zech_one
  , fq_zech_gen
  , fq_zech_get_fmpz
  , fq_zech_get_fq_nmod
  , fq_zech_set_fq_nmod
  , fq_zech_get_nmod_poly
  , fq_zech_set_nmod_poly
  , fq_zech_get_nmod_mat
  , fq_zech_set_nmod_mat
  -- * Comparison
  , fq_zech_is_zero
  , fq_zech_is_one
  , fq_zech_equal
  , fq_zech_is_invertible
  , fq_zech_is_invertible_f
  -- * Special functions
  , fq_zech_trace
  , fq_zech_norm
  , fq_zech_frobenius
  , fq_zech_multiplicative_order
  -- , fq_zech_is_primitive
  -- * Bit packing
  , fq_zech_bit_pack
  , fq_zech_bit_unpack
) where

-- Finite fields (Zech logarithm representation) -------------------------------

-- finite fields (Zech logarithm representation) -------------------------------

import Foreign.C.String
import Foreign.C.Types

import Foreign.Ptr ( Ptr, FunPtr, plusPtr )
import Foreign.ForeignPtr
import Foreign.Storable
import Foreign.Marshal ( free )

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.NMod.Poly
import Data.Number.Flint.NMod.Mat
import Data.Number.Flint.Fq
import Data.Number.Flint.Fq.NMod
import Data.Number.Flint.Fq.NMod.Mat

#include <flint/flint.h>
#include <flint/fq_zech.h>

-- fq_zech_t -------------------------------------------------------------------

data FqZech = FqZech {-# UNPACK #-} !(ForeignPtr CFqZech)
type CFqZech = CFlint FqZech

instance Storable CFqZech where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fq_zech_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fq_zech_t}
  peek = undefined
  poke = undefined

newFqZech ctx@(FqZechCtx ftx) = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> do
    withFqZechCtx ctx $ \ctx -> do
      fq_zech_init x ctx
    addForeignPtrFinalizerEnv p_fq_zech_clear x ftx
  return $ FqZech x

{-# INLINE withFqZech #-}
withFqZech (FqZech x) f = do
  withForeignPtr x $ \px -> f px >>= return . (FqZech x,)

-- fq_zech_ctx_t ---------------------------------------------------------------

data FqZechCtx = FqZechCtx {-# UNPACK #-} !(ForeignPtr CFqZechCtx)
type CFqZechCtx = CFlint FqZechCtx

instance Storable CFqZechCtx where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fq_zech_ctx_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fq_zech_ctx_t}
  peek = undefined
  poke = undefined

_newFqZechCtx f p d var = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x ->
    withFmpz p $ \p -> 
      withCString var $ \var -> do
        f x p d var
  addForeignPtrFinalizer p_fq_zech_ctx_clear x
  return $ FqZechCtx x

newFqZechCtx       = _newFqZechCtx fq_zech_ctx_init
newFqZechCtxConway = _newFqZechCtx fq_zech_ctx_init_conway
newFqZechCtxRandom = _newFqZechCtx fq_zech_ctx_init_random

newFqZechCtxModulus f modulus var = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x ->
    withNModPoly modulus $ \modulus -> 
      withCString var $ \var -> 
        fq_zech_ctx_init_modulus x modulus var
  addForeignPtrFinalizer p_fq_zech_ctx_clear x
  return $ FqZechCtx x

newFqZechCtxModulusCheck f modulus var = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x ->
    withNModPoly modulus $ \modulus -> 
      withCString var $ \var -> 
        fq_zech_ctx_init_modulus_check x modulus var
  addForeignPtrFinalizer p_fq_zech_ctx_clear x
  return $ FqZechCtx x

newFqZechCtxFqNModCtx f ctxn = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x ->
    withFqNModCtx ctxn $ \ctxn -> 
      fq_zech_ctx_init_fq_nmod_ctx x ctxn
  addForeignPtrFinalizer p_fq_zech_ctx_clear x
  return $ FqZechCtx x

newFqZechCtxFqNModCtxCheck f ctxn = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x ->
    withFqNModCtx ctxn $ \ctxn -> 
      fq_zech_ctx_init_fq_nmod_ctx_check x ctxn
  addForeignPtrFinalizer p_fq_zech_ctx_clear x
  return $ FqZechCtx x

newFqZechCtxFqCtxModulusCheck f ctxn = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x ->
    withFqNModCtx ctxn $ \ctxn -> 
      fq_zech_ctx_init_fq_nmod_ctx_check x ctxn
  addForeignPtrFinalizer p_fq_zech_ctx_clear x
  return $ FqZechCtx x

{-# INLINE withFqZechCtx #-}
withFqZechCtx (FqZechCtx x) f = do
  withForeignPtr x $ \px -> f px >>= return . (FqZechCtx x,)

-- Context Management ----------------------------------------------------------

-- | /fq_zech_ctx_init/ /ctx/ /p/ /d/ /var/ 
--
-- Initialises the context for prime \(p\) and extension degree \(d\), with
-- name @var@ for the generator. By default, it will try use a Conway
-- polynomial; if one is not available, a random primitive polynomial will
-- be used.
-- 
-- Assumes that \(p\) is a prime and \(p^d < 2^{\mathtt{FLINT\_BITS}}\).
-- 
-- Assumes that the string @var@ is a null-terminated string of length at
-- least one.
foreign import ccall "fq_zech.h fq_zech_ctx_init"
  fq_zech_ctx_init :: Ptr CFqZechCtx -> Ptr CFmpz -> CLong -> CString -> IO ()

-- | /_fq_zech_ctx_init_conway/ /ctx/ /p/ /d/ /var/ 
--
-- Attempts to initialise the context for prime \(p\) and extension degree
-- \(d\), with name @var@ for the generator using a Conway polynomial for
-- the modulus.
-- 
-- Returns \(1\) if the Conway polynomial is in the database for the given
-- size and the initialization is successful; otherwise, returns \(0\).
-- 
-- Assumes that \(p\) is a prime and \(p^d < 2^\mathtt{FLINT\_BITS}\).
-- 
-- Assumes that the string @var@ is a null-terminated string of length at
-- least one.
foreign import ccall "fq_zech.h _fq_zech_ctx_init_conway"
  _fq_zech_ctx_init_conway :: Ptr CFqZechCtx -> Ptr CFmpz -> CLong -> CString -> IO CInt

-- | /fq_zech_ctx_init_conway/ /ctx/ /p/ /d/ /var/ 
--
-- Initialises the context for prime \(p\) and extension degree \(d\), with
-- name @var@ for the generator using a Conway polynomial for the modulus.
-- 
-- Assumes that \(p\) is a prime and \(p^d < 2^\mathtt{FLINT\_BITS}\).
-- 
-- Assumes that the string @var@ is a null-terminated string of length at
-- least one.
foreign import ccall "fq_zech.h fq_zech_ctx_init_conway"
  fq_zech_ctx_init_conway :: Ptr CFqZechCtx -> Ptr CFmpz -> CLong -> CString -> IO ()

-- | /fq_zech_ctx_init_random/ /ctx/ /p/ /d/ /var/ 
--
-- Initialises the context for prime \(p\) and extension degree \(d\), with
-- name @var@ for the generator using a random primitive polynomial.
-- 
-- Assumes that \(p\) is a prime and \(p^d < 2^\mathtt{FLINT\_BITS}\).
-- 
-- Assumes that the string @var@ is a null-terminated string of length at
-- least one.
foreign import ccall "fq_zech.h fq_zech_ctx_init_random"
  fq_zech_ctx_init_random :: Ptr CFqZechCtx -> Ptr CFmpz -> CLong -> CString -> IO ()

-- | /fq_zech_ctx_init_modulus/ /ctx/ /modulus/ /var/ 
--
-- Initialises the context for given @modulus@ with name @var@ for the
-- generator.
-- 
-- Assumes that @modulus@ is an primitive polynomial over
-- \(\mathbf{F}_{p}\). An exception is raised if a non-primitive modulus is
-- detected.
-- 
-- Assumes that the string @var@ is a null-terminated string of length at
-- least one.
foreign import ccall "fq_zech.h fq_zech_ctx_init_modulus"
  fq_zech_ctx_init_modulus :: Ptr CFqZechCtx -> Ptr CNModPoly -> CString -> IO ()

-- | /fq_zech_ctx_init_modulus_check/ /ctx/ /modulus/ /var/ 
--
-- As per the previous function, but returns \(0\) if the modulus was not
-- primitive and \(1\) if the context was successfully initialised with the
-- given modulus. No exception is raised.
foreign import ccall "fq_zech.h fq_zech_ctx_init_modulus_check"
  fq_zech_ctx_init_modulus_check :: Ptr CFqZechCtx -> Ptr CNModPoly -> CString -> IO CInt

-- | /fq_zech_ctx_init_fq_nmod_ctx/ /ctx/ /ctxn/ 
--
-- Initializes the context @ctx@ to be the Zech representation for the
-- finite field given by @ctxn@.
foreign import ccall "fq_zech.h fq_zech_ctx_init_fq_nmod_ctx"
  fq_zech_ctx_init_fq_nmod_ctx :: Ptr CFqZechCtx -> Ptr CFqNModCtx -> IO ()

-- | /fq_zech_ctx_init_fq_nmod_ctx_check/ /ctx/ /ctxn/ 
--
-- As per the previous function but returns \(0\) if a non-primitive
-- modulus is detected. Returns \(0\) if the Zech representation was
-- successfully initialised.
foreign import ccall "fq_zech.h fq_zech_ctx_init_fq_nmod_ctx_check"
  fq_zech_ctx_init_fq_nmod_ctx_check :: Ptr CFqZechCtx -> Ptr CFqNModCtx -> IO CInt

-- | /fq_zech_ctx_clear/ /ctx/ 
--
-- Clears all memory that has been allocated as part of the context.
foreign import ccall "fq_zech.h fq_zech_ctx_clear"
  fq_zech_ctx_clear :: Ptr CFqZechCtx -> IO ()

foreign import ccall "fq_zech.h &fq_zech_ctx_clear"
  p_fq_zech_ctx_clear :: FunPtr (Ptr CFqZechCtx -> IO ())

-- | /fq_zech_ctx_modulus/ /ctx/ 
--
-- Returns a pointer to the modulus in the context.
foreign import ccall "fq_zech.h fq_zech_ctx_modulus"
  fq_zech_ctx_modulus :: Ptr CFqZechCtx -> IO (Ptr (Ptr CNModPoly))

-- | /fq_zech_ctx_degree/ /ctx/ 
--
-- Returns the degree of the field extension
-- \([\mathbf{F}_{q} : \mathbf{F}_{p}]\), which is equal to \(\log_{p} q\).
foreign import ccall "fq_zech.h fq_zech_ctx_degree"
  fq_zech_ctx_degree :: Ptr CFqZechCtx -> IO CLong

-- -- | /fq_zech_ctx_prime/ /ctx/ 
-- --
-- -- Returns a pointer to the prime \(p\) in the context.
-- foreign import ccall "fq_zech.h fq_zech_ctx_prime"
--   fq_zech_ctx_prime :: Ptr CFqZechCtx -> IO (Ptr CFmpz)

-- | /fq_zech_ctx_order/ /f/ /ctx/ 
--
-- Sets \(f\) to be the size of the finite field.
foreign import ccall "fq_zech.h fq_zech_ctx_order"
  fq_zech_ctx_order :: Ptr CFmpz -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_ctx_order_ui/ /ctx/ 
--
-- Returns the size of the finite field.
foreign import ccall "fq_zech.h fq_zech_ctx_order_ui"
  fq_zech_ctx_order_ui :: Ptr CFqZechCtx -> IO CMpLimb

-- | /fq_zech_ctx_fprint/ /file/ /ctx/ 
--
-- Prints the context information to {tt{file}}. Returns 1 for a success
-- and a negative number for an error.
foreign import ccall "fq_zech.h fq_zech_ctx_fprint"
  fq_zech_ctx_fprint :: Ptr CFile -> Ptr CFqZechCtx -> IO CInt

-- | /fq_zech_ctx_print/ /ctx/ 
--
-- Prints the context information to {tt{stdout}}.
foreign import ccall "fq_zech.h fq_zech_ctx_print"
  fq_zech_ctx_print :: Ptr CFqZechCtx -> IO ()

-- | /fq_zech_ctx_randtest/ /ctx/ 
--
-- Initializes @ctx@ to a random finite field. Assumes that
-- @fq_zech_ctx_init@ has not been called on @ctx@ already.
foreign import ccall "fq_zech.h fq_zech_ctx_randtest"
  fq_zech_ctx_randtest :: Ptr CFqZechCtx -> IO ()

-- | /fq_zech_ctx_randtest_reducible/ /ctx/ 
--
-- Since the Zech logarithm representation does not work with a
-- non-irreducible modulus, does the same as @fq_zech_ctx_randtest@.
foreign import ccall "fq_zech.h fq_zech_ctx_randtest_reducible"
  fq_zech_ctx_randtest_reducible :: Ptr CFqZechCtx -> IO ()

-- Memory management -----------------------------------------------------------

-- | /fq_zech_init/ /rop/ /ctx/ 
--
-- Initialises the element @rop@, setting its value to \(0\).
foreign import ccall "fq_zech.h fq_zech_init"
  fq_zech_init :: Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_init2/ /rop/ /ctx/ 
--
-- Initialises @poly@ with at least enough space for it to be an element of
-- @ctx@ and sets it to \(0\).
foreign import ccall "fq_zech.h fq_zech_init2"
  fq_zech_init2 :: Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_clear/ /rop/ /ctx/ 
--
-- Clears the element @rop@.
foreign import ccall "fq_zech.h fq_zech_clear"
  fq_zech_clear :: Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

foreign import ccall "fq_zech.h &fq_zech_clear"
  p_fq_zech_clear :: FunPtr (Ptr CFqZech -> Ptr CFqZechCtx -> IO ())

-- -- | /_fq_zech_sparse_reduce/ /R/ /lenR/ /ctx/ 
-- --
-- -- Reduces @(R, lenR)@ modulo the polynomial \(f\) given by the modulus of
-- -- @ctx@.
-- foreign import ccall "fq_zech.h _fq_zech_sparse_reduce"
--   _fq_zech_sparse_reduce :: Ptr CMp -> CLong -> Ptr CFqZechCtx -> IO ()

-- -- | /_fq_zech_dense_reduce/ /R/ /lenR/ /ctx/ 
-- --
-- -- Reduces @(R, lenR)@ modulo the polynomial \(f\) given by the modulus of
-- -- @ctx@ using Newton division.
-- foreign import ccall "fq_zech.h _fq_zech_dense_reduce"
--   _fq_zech_dense_reduce :: Ptr CMp -> CLong -> Ptr CFqZechCtx -> IO ()

-- -- | /_fq_zech_reduce/ /r/ /lenR/ /ctx/ 
-- --
-- -- Reduces @(R, lenR)@ modulo the polynomial \(f\) given by the modulus of
-- -- @ctx@. Does either sparse or dense reduction based on
-- -- @ctx->sparse_modulus@.
-- foreign import ccall "fq_zech.h _fq_zech_reduce"
--   _fq_zech_reduce :: Ptr CMp -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_reduce/ /rop/ /ctx/ 
--
-- Reduces the polynomial @rop@ as an element of
-- \(\mathbf{F}_p[X] / (f(X))\).
foreign import ccall "fq_zech.h fq_zech_reduce"
  fq_zech_reduce :: Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- Basic arithmetic ------------------------------------------------------------

-- | /fq_zech_add/ /rop/ /op1/ /op2/ /ctx/ 
--
-- Sets @rop@ to the sum of @op1@ and @op2@.
foreign import ccall "fq_zech.h fq_zech_add"
  fq_zech_add :: Ptr CFqZech -> Ptr CFqZech -> Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_sub/ /rop/ /op1/ /op2/ /ctx/ 
--
-- Sets @rop@ to the difference of @op1@ and @op2@.
foreign import ccall "fq_zech.h fq_zech_sub"
  fq_zech_sub :: Ptr CFqZech -> Ptr CFqZech -> Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_sub_one/ /rop/ /op1/ /ctx/ 
--
-- Sets @rop@ to the difference of @op1@ and \(1\).
foreign import ccall "fq_zech.h fq_zech_sub_one"
  fq_zech_sub_one :: Ptr CFqZech -> Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_neg/ /rop/ /op/ /ctx/ 
--
-- Sets @rop@ to the negative of @op@.
foreign import ccall "fq_zech.h fq_zech_neg"
  fq_zech_neg :: Ptr CFqZech -> Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_mul/ /rop/ /op1/ /op2/ /ctx/ 
--
-- Sets @rop@ to the product of @op1@ and @op2@, reducing the output in the
-- given context.
foreign import ccall "fq_zech.h fq_zech_mul"
  fq_zech_mul :: Ptr CFqZech -> Ptr CFqZech -> Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_mul_fmpz/ /rop/ /op/ /x/ /ctx/ 
--
-- Sets @rop@ to the product of @op@ and \(x\), reducing the output in the
-- given context.
foreign import ccall "fq_zech.h fq_zech_mul_fmpz"
  fq_zech_mul_fmpz :: Ptr CFqZech -> Ptr CFqZech -> Ptr CFmpz -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_mul_si/ /rop/ /op/ /x/ /ctx/ 
--
-- Sets @rop@ to the product of @op@ and \(x\), reducing the output in the
-- given context.
foreign import ccall "fq_zech.h fq_zech_mul_si"
  fq_zech_mul_si :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_mul_ui/ /rop/ /op/ /x/ /ctx/ 
--
-- Sets @rop@ to the product of @op@ and \(x\), reducing the output in the
-- given context.
foreign import ccall "fq_zech.h fq_zech_mul_ui"
  fq_zech_mul_ui :: Ptr CFqZech -> Ptr CFqZech -> CULong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_sqr/ /rop/ /op/ /ctx/ 
--
-- Sets @rop@ to the square of @op@, reducing the output in the given
-- context.
foreign import ccall "fq_zech.h fq_zech_sqr"
  fq_zech_sqr :: Ptr CFqZech -> Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_div/ /rop/ /op1/ /op2/ /ctx/ 
--
-- Sets @rop@ to the quotient of @op1@ and @op2@, reducing the output in
-- the given context.
foreign import ccall "fq_zech.h fq_zech_div"
  fq_zech_div :: Ptr CFqZech -> Ptr CFqZech -> Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- -- | /_fq_zech_inv/ /rop/ /op/ /len/ /ctx/ 
-- --
-- -- Sets @(rop, d)@ to the inverse of the non-zero element @(op, len)@.
-- foreign import ccall "fq_zech.h _fq_zech_inv"
--   _fq_zech_inv :: Ptr (Ptr CMp) -> Ptr (Ptr CMp) -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_inv/ /rop/ /op/ /ctx/ 
--
-- Sets @rop@ to the inverse of the non-zero element @op@.
foreign import ccall "fq_zech.h fq_zech_inv"
  fq_zech_inv :: Ptr CFqZech -> Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_gcdinv/ /f/ /inv/ /op/ /ctx/ 
--
-- Sets @inv@ to be the inverse of @op@ modulo the modulus of @ctx@ and
-- sets @f@ to one. Since the modulus for @ctx@ is always irreducible, @op@
-- is always invertible.
foreign import ccall "fq_zech.h fq_zech_gcdinv"
  fq_zech_gcdinv :: Ptr CFqZech -> Ptr CFqZech -> Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- -- | /_fq_zech_pow/ /rop/ /op/ /len/ /e/ /ctx/ 
-- --
-- -- Sets @(rop, 2*d-1)@ to @(op,len)@ raised to the power \(e\), reduced
-- -- modulo \(f(X)\), the modulus of @ctx@.
-- -- 
-- -- Assumes that \(e \geq 0\) and that @len@ is positive and at most \(d\).
-- -- 
-- -- Although we require that @rop@ provides space for \(2d - 1\)
-- -- coefficients, the output will be reduced modulo \(f(X)\), which is a
-- -- polynomial of degree \(d\).
-- -- 
-- -- Does not support aliasing.
-- foreign import ccall "fq_zech.h _fq_zech_pow"
--   _fq_zech_pow :: Ptr (Ptr CMp) -> Ptr (Ptr CMp) -> CLong -> Ptr CFmpz -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_pow/ /rop/ /op/ /e/ /ctx/ 
--
-- Sets @rop@ the @op@ raised to the power \(e\).
-- 
-- Currently assumes that \(e \geq 0\).
-- 
-- Note that for any input @op@, @rop@ is set to \(1\) whenever \(e = 0\).
foreign import ccall "fq_zech.h fq_zech_pow"
  fq_zech_pow :: Ptr CFqZech -> Ptr CFqZech -> Ptr CFmpz -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_pow_ui/ /rop/ /op/ /e/ /ctx/ 
--
-- Sets @rop@ the @op@ raised to the power \(e\).
-- 
-- Currently assumes that \(e \geq 0\).
-- 
-- Note that for any input @op@, @rop@ is set to \(1\) whenever \(e = 0\).
foreign import ccall "fq_zech.h fq_zech_pow_ui"
  fq_zech_pow_ui :: Ptr CFqZech -> Ptr CFqZech -> CULong -> Ptr CFqZechCtx -> IO ()

-- Roots -----------------------------------------------------------------------

-- | /fq_zech_sqrt/ /rop/ /op1/ /ctx/ 
--
-- Sets @rop@ to the square root of @op1@ if it is a square, and return
-- \(1\), otherwise return \(0\).
foreign import ccall "fq_zech.h fq_zech_sqrt"
  fq_zech_sqrt :: Ptr CFqZech -> Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_pth_root/ /rop/ /op1/ /ctx/ 
--
-- Sets @rop@ to a \(p^{th}\) root root of @op1@. Currently, this computes
-- the root by raising @op1@ to \(p^{d-1}\) where \(d\) is the degree of
-- the extension.
foreign import ccall "fq_zech.h fq_zech_pth_root"
  fq_zech_pth_root :: Ptr CFqZech -> Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_is_square/ /op/ /ctx/ 
--
-- Return @1@ if @op@ is a square.
foreign import ccall "fq_zech.h fq_zech_is_square"
  fq_zech_is_square :: Ptr CFqZech -> Ptr CFqZechCtx -> IO CInt

-- Output ----------------------------------------------------------------------

-- | /fq_zech_fprint_pretty/ /file/ /op/ /ctx/ 
--
-- Prints a pretty representation of @op@ to @file@.
-- 
-- In the current implementation, always returns \(1\). The return code is
-- part of the function\'s signature to allow for a later implementation to
-- return the number of characters printed or a non-positive error code.
foreign import ccall "fq_zech.h fq_zech_fprint_pretty"
  fq_zech_fprint_pretty :: Ptr CFile -> Ptr CFqZech -> Ptr CFqZechCtx -> IO CInt

-- | /fq_zech_print_pretty/ /op/ /ctx/ 
--
-- Prints a pretty representation of @op@ to @stdout@.
-- 
-- In the current implementation, always returns \(1\). The return code is
-- part of the function\'s signature to allow for a later implementation to
-- return the number of characters printed or a non-positive error code.
fq_zech_print_pretty :: Ptr CFqZech -> Ptr CFqZechCtx -> IO CInt
fq_zech_print_pretty op ctx = do
  printCStr (\op -> fq_zech_get_str_pretty op ctx) op

-- | /fq_zech_fprint/ /file/ /op/ /ctx/ 
--
-- Prints a representation of @op@ to @file@.
foreign import ccall "fq_zech.h fq_zech_fprint"
  fq_zech_fprint :: Ptr CFile -> Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_print/ /op/ /ctx/ 
--
-- Prints a representation of @op@ to @stdout@.
fq_zech_print :: Ptr CFqZech -> Ptr CFqZechCtx -> IO ()
fq_zech_print op ctx = do
  printCStr (\op -> fq_zech_get_str op ctx) op
  return ()

-- | /fq_zech_get_str/ /op/ /ctx/ 
--
-- Returns the plain FLINT string representation of the element @op@.
foreign import ccall "fq_zech.h fq_zech_get_str"
  fq_zech_get_str :: Ptr CFqZech -> Ptr CFqZechCtx -> IO CString

-- | /fq_zech_get_str_pretty/ /op/ /ctx/ 
--
-- Returns a pretty representation of the element @op@ using the
-- null-terminated string @x@ as the variable name.
foreign import ccall "fq_zech.h fq_zech_get_str_pretty"
  fq_zech_get_str_pretty :: Ptr CFqZech -> Ptr CFqZechCtx -> IO CString

-- Randomisation ---------------------------------------------------------------

-- | /fq_zech_randtest/ /rop/ /state/ /ctx/ 
--
-- Generates a random element of \(\mathbf{F}_q\).
foreign import ccall "fq_zech.h fq_zech_randtest"
  fq_zech_randtest :: Ptr CFqZech -> Ptr CFRandState -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_randtest_not_zero/ /rop/ /state/ /ctx/ 
--
-- Generates a random non-zero element of \(\mathbf{F}_q\).
foreign import ccall "fq_zech.h fq_zech_randtest_not_zero"
  fq_zech_randtest_not_zero :: Ptr CFqZech -> Ptr CFRandState -> Ptr CFqZechCtx -> IO ()

-- -- | /fq_zech_randtest_dense/ /rop/ /state/ /ctx/ 
-- --
-- -- Generates a random element of \(\mathbf{F}_q\) which has an underlying
-- -- polynomial with dense coefficients.
-- foreign import ccall "fq_zech.h fq_zech_randtest_dense"
--   fq_zech_randtest_dense :: Ptr CFqZech -> Ptr CFRandState -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_rand/ /rop/ /state/ /ctx/ 
--
-- Generates a high quality random element of \(\mathbf{F}_q\).
foreign import ccall "fq_zech.h fq_zech_rand"
  fq_zech_rand :: Ptr CFqZech -> Ptr CFRandState -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_rand_not_zero/ /rop/ /state/ /ctx/ 
--
-- Generates a high quality non-zero random element of \(\mathbf{F}_q\).
foreign import ccall "fq_zech.h fq_zech_rand_not_zero"
  fq_zech_rand_not_zero :: Ptr CFqZech -> Ptr CFRandState -> Ptr CFqZechCtx -> IO ()

-- Assignments and conversions -------------------------------------------------

-- | /fq_zech_set/ /rop/ /op/ /ctx/ 
--
-- Sets @rop@ to @op@.
foreign import ccall "fq_zech.h fq_zech_set"
  fq_zech_set :: Ptr CFqZech -> Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_set_si/ /rop/ /x/ /ctx/ 
--
-- Sets @rop@ to @x@, considered as an element of \(\mathbf{F}_p\).
foreign import ccall "fq_zech.h fq_zech_set_si"
  fq_zech_set_si :: Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_set_ui/ /rop/ /x/ /ctx/ 
--
-- Sets @rop@ to @x@, considered as an element of \(\mathbf{F}_p\).
foreign import ccall "fq_zech.h fq_zech_set_ui"
  fq_zech_set_ui :: Ptr CFqZech -> CULong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_set_fmpz/ /rop/ /x/ /ctx/ 
--
-- Sets @rop@ to @x@, considered as an element of \(\mathbf{F}_p\).
foreign import ccall "fq_zech.h fq_zech_set_fmpz"
  fq_zech_set_fmpz :: Ptr CFqZech -> Ptr CFmpz -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_swap/ /op1/ /op2/ /ctx/ 
--
-- Swaps the two elements @op1@ and @op2@.
foreign import ccall "fq_zech.h fq_zech_swap"
  fq_zech_swap :: Ptr CFqZech -> Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_zero/ /rop/ /ctx/ 
--
-- Sets @rop@ to zero.
foreign import ccall "fq_zech.h fq_zech_zero"
  fq_zech_zero :: Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_one/ /rop/ /ctx/ 
--
-- Sets @rop@ to one, reduced in the given context.
foreign import ccall "fq_zech.h fq_zech_one"
  fq_zech_one :: Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_gen/ /rop/ /ctx/ 
--
-- Sets @rop@ to a generator for the finite field. There is no guarantee
-- this is a multiplicative generator of the finite field.
foreign import ccall "fq_zech.h fq_zech_gen"
  fq_zech_gen :: Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_get_fmpz/ /rop/ /op/ /ctx/ 
--
-- If @op@ has a lift to the integers, return \(1\) and set @rop@ to the
-- lift in \([0,p)\). Otherwise, return \(0\) and leave \(rop\) undefined.
foreign import ccall "fq_zech.h fq_zech_get_fmpz"
  fq_zech_get_fmpz :: Ptr CFmpz -> Ptr CFqZech -> Ptr CFqZechCtx -> IO CInt

-- | /fq_zech_get_fq_nmod/ /rop/ /op/ /ctx/ 
--
-- Sets @rop@ to the @fq_nmod_t@ element corresponding to @op@.
foreign import ccall "fq_zech.h fq_zech_get_fq_nmod"
  fq_zech_get_fq_nmod :: Ptr CFqNMod -> Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_set_fq_nmod/ /rop/ /op/ /ctx/ 
--
-- Sets @rop@ to the @fq_zech_t@ element corresponding to @op@.
foreign import ccall "fq_zech.h fq_zech_set_fq_nmod"
  fq_zech_set_fq_nmod :: Ptr CFqZech -> Ptr CFqNMod -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_get_nmod_poly/ /a/ /b/ /ctx/ 
--
-- Set @a@ to a representative of @b@ in @ctx@. The representatives are
-- taken in \((\mathbb{Z}/p\mathbb{Z})[x]/h(x)\) where \(h(x)\) is the
-- defining polynomial in @ctx@.
foreign import ccall "fq_zech.h fq_zech_get_nmod_poly"
  fq_zech_get_nmod_poly :: Ptr CNModPoly -> Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_set_nmod_poly/ /a/ /b/ /ctx/ 
--
-- Set @a@ to the element in @ctx@ with representative @b@. The
-- representatives are taken in \((\mathbb{Z}/p\mathbb{Z})[x]/h(x)\) where
-- \(h(x)\) is the defining polynomial in @ctx@.
foreign import ccall "fq_zech.h fq_zech_set_nmod_poly"
  fq_zech_set_nmod_poly :: Ptr CFqZech -> Ptr CNModPoly -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_get_nmod_mat/ /col/ /a/ /ctx/ 
--
-- Convert @a@ to a column vector of length @degree(ctx)@.
foreign import ccall "fq_zech.h fq_zech_get_nmod_mat"
  fq_zech_get_nmod_mat :: Ptr CNModMat -> Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_set_nmod_mat/ /a/ /col/ /ctx/ 
--
-- Convert a column vector @col@ of length @degree(ctx)@ to an element of
-- @ctx@.
foreign import ccall "fq_zech.h fq_zech_set_nmod_mat"
  fq_zech_set_nmod_mat :: Ptr CFqZech -> Ptr CNModMat -> Ptr CFqZechCtx -> IO ()

-- Comparison ------------------------------------------------------------------

-- | /fq_zech_is_zero/ /op/ /ctx/ 
--
-- Returns whether @op@ is equal to zero.
foreign import ccall "fq_zech.h fq_zech_is_zero"
  fq_zech_is_zero :: Ptr CFqZech -> Ptr CFqZechCtx -> IO CInt

-- | /fq_zech_is_one/ /op/ /ctx/ 
--
-- Returns whether @op@ is equal to one.
foreign import ccall "fq_zech.h fq_zech_is_one"
  fq_zech_is_one :: Ptr CFqZech -> Ptr CFqZechCtx -> IO CInt

-- | /fq_zech_equal/ /op1/ /op2/ /ctx/ 
--
-- Returns whether @op1@ and @op2@ are equal.
foreign import ccall "fq_zech.h fq_zech_equal"
  fq_zech_equal :: Ptr CFqZech -> Ptr CFqZech -> Ptr CFqZechCtx -> IO CInt

-- | /fq_zech_is_invertible/ /op/ /ctx/ 
--
-- Returns whether @op@ is an invertible element.
foreign import ccall "fq_zech.h fq_zech_is_invertible"
  fq_zech_is_invertible :: Ptr CFqZech -> Ptr CFqZechCtx -> IO CInt

-- | /fq_zech_is_invertible_f/ /f/ /op/ /ctx/ 
--
-- Returns whether @op@ is an invertible element. If it is not, then @f@ is
-- set of a factor of the modulus. Since the modulus for an @fq_zech_ctx_t@
-- is always irreducible, then any non-zero @op@ will be invertible.
foreign import ccall "fq_zech.h fq_zech_is_invertible_f"
  fq_zech_is_invertible_f :: Ptr CFqZech -> Ptr CFqZech -> Ptr CFqZechCtx -> IO CInt

-- Special functions -----------------------------------------------------------

-- | /fq_zech_trace/ /rop/ /op/ /ctx/ 
--
-- Sets @rop@ to the trace of @op@.
-- 
-- For an element \(a \in \mathbf{F}_q\), multiplication by \(a\) defines a
-- \(\mathbf{F}_p\)-linear map on \(\mathbf{F}_q\). We define the trace of
-- \(a\) as the trace of this map. Equivalently, if \(\Sigma\) generates
-- \(\operatorname{Gal}(\mathbf{F}_q / \mathbf{F}_p)\) then the trace of
-- \(a\) is equal to \(\sum_{i=0}^{d-1} \Sigma^i (a)\), where \(d =
-- \log_{p} q\).
foreign import ccall "fq_zech.h fq_zech_trace"
  fq_zech_trace :: Ptr CFmpz -> Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_norm/ /rop/ /op/ /ctx/ 
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
foreign import ccall "fq_zech.h fq_zech_norm"
  fq_zech_norm :: Ptr CFmpz -> Ptr CFqZech -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_frobenius/ /rop/ /op/ /e/ /ctx/ 
--
-- Evaluates the homomorphism \(\Sigma^e\) at @op@.
-- 
-- Recall that \(\mathbf{F}_q / \mathbf{F}_p\) is Galois with Galois group
-- \(\langle \sigma \rangle\), which is also isomorphic to
-- \(\mathbf{Z}/d\mathbf{Z}\), where
-- \(\sigma \in \operatorname{Gal}(\mathbf{F}_q/\mathbf{F}_p)\) is the
-- Frobenius element \(\sigma \colon x \mapsto x^p\).
foreign import ccall "fq_zech.h fq_zech_frobenius"
  fq_zech_frobenius :: Ptr CFqZech -> Ptr CFqZech -> CLong -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_multiplicative_order/ /ord/ /op/ /ctx/ 
--
-- Computes the order of @op@ as an element of the multiplicative group of
-- @ctx@.
-- 
-- Returns 0 if @op@ is 0, otherwise it returns 1 if @op@ is a generator of
-- the multiplicative group, and -1 if it is not.
-- 
-- Note that @ctx@ must already correspond to a finite field defined by a
-- primitive polynomial and so this function cannot be used to check
-- primitivity of the generator, but can be used to check that other
-- elements are primitive.
foreign import ccall "fq_zech.h fq_zech_multiplicative_order"
  fq_zech_multiplicative_order :: Ptr CFmpz -> Ptr CFqZech -> Ptr CFqZechCtx -> IO CInt

-- -- | /fq_zech_is_primitive/ /op/ /ctx/ 
-- --
-- -- Returns whether @op@ is primitive, i.e., whether it is a generator of
-- -- the multiplicative group of @ctx@.
-- foreign import ccall "fq_zech.h fq_zech_is_primitive"
--   fq_zech_is_primitive :: Ptr CFqZech -> Ptr CFqZechCtx -> IO CInt

-- Bit packing -----------------------------------------------------------------

-- | /fq_zech_bit_pack/ /f/ /op/ /bit_size/ /ctx/ 
--
-- Packs @op@ into bitfields of size @bit_size@, writing the result to @f@.
foreign import ccall "fq_zech.h fq_zech_bit_pack"
  fq_zech_bit_pack :: Ptr CFmpz -> Ptr CFqZech -> CFBitCnt -> Ptr CFqZechCtx -> IO ()

-- | /fq_zech_bit_unpack/ /rop/ /f/ /bit_size/ /ctx/ 
--
-- Unpacks into @rop@ the element with coefficients packed into fields of
-- size @bit_size@ as represented by the integer @f@.
foreign import ccall "fq_zech.h fq_zech_bit_unpack"
  fq_zech_bit_unpack :: Ptr CFqZech -> Ptr CFmpz -> CFBitCnt -> Ptr CFqZechCtx -> IO ()

