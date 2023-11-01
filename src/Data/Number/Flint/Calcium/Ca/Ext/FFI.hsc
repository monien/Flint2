module Data.Number.Flint.Calcium.Ca.Ext.FFI (
  -- * Real and complex extension numbers
  -- * Type and macros
    CaExt (..)
  , CCaExt (..)
  , newCaExtQQbar
  , newCaExtConst
  , newCaExtFx
  , newCaExtFxy
  , newCaExtFxn
  , withCaExt
  -- * Memory management
  , ca_ext_init_qqbar
  , ca_ext_init_const
  , ca_ext_init_fx
  , ca_ext_init_fxy
  , ca_ext_init_fxn
  , ca_ext_init_set
  , ca_ext_clear
  -- * Structure
  , ca_ext_nargs
  , ca_ext_get_arg
  , ca_ext_hash
  , ca_ext_equal_repr
  , ca_ext_cmp_repr
  -- * Input and output
  , ca_ext_print
  -- * Numerical evaluation
  , ca_ext_get_acb_raw
  -- * Cache
  , ca_ext_cache_init
  , ca_ext_cache_clear
  , ca_ext_cache_insert
) where 

-- Real and complex extension numbers ------------------------------------------

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.C.Types
import Foreign.C.String
import Foreign.Storable
import Foreign.Marshal.Array

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Acb.Types
import Data.Number.Flint.NF.QQbar
import Data.Number.Flint.Calcium
import Data.Number.Flint.Calcium.Ca
import Data.Number.Flint.Calcium.Ca.Types

#include <flint/ca_ext.h>

-- ca_ext_t --------------------------------------------------------------------

instance Storable CCaExt where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size ca_ext_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment ca_ext_t}
  peek = error "CCaExt.peek: Not defined"
  poke = error "CCaExt.poke: Not defined"

newCaExtQQbar x ctx@(CaCtx ctxf) = do
  res <- mallocForeignPtr
  withForeignPtr res $ \resp -> do
    withCaCtx ctx $ \ctxp -> do
      withQQbar x $ \xp -> do
        ca_ext_init_qqbar resp xp ctxp
    addForeignPtrFinalizerEnv p_ca_ext_clear resp ctxf
  return $ CaExt res

newCaExtConst fc ctx@(CaCtx ctxf) = do
  res <- mallocForeignPtr
  withForeignPtr res $ \resp -> do
    withCaCtx ctx $ \ctxp -> do
      ca_ext_init_const resp fc ctxp
    addForeignPtrFinalizerEnv p_ca_ext_clear resp ctxf
  return $ CaExt res

newCaExtFx fx x ctx@(CaCtx ctxf) = do
  res <- mallocForeignPtr
  withForeignPtr res $ \resp -> do
    withCaCtx ctx $ \ctxp -> do
      withCa x $ \x -> do
        ca_ext_init_fx resp fx x ctxp
    addForeignPtrFinalizerEnv p_ca_ext_clear resp ctxf
  return $ CaExt res

newCaExtFxy fxy x y ctx@(CaCtx ctxf) = do
  res <- mallocForeignPtr
  withForeignPtr res $ \resp -> do
    withCaCtx ctx $ \ctxp -> do
      withCa x $ \x -> do
        withCa y $ \y -> do
          ca_ext_init_fxy resp fxy x y ctxp
    addForeignPtrFinalizerEnv p_ca_ext_clear resp ctxf
  return $ CaExt res

newCaExtFxn fxn x nargs ctx@(CaCtx ctxf) = do
  res <- mallocForeignPtr
  withForeignPtr res $ \resp -> do
    withCaCtx ctx $ \ctxp -> do
      withCa x $ \x -> do
        ca_ext_init_fxn resp fxn x nargs ctxp
    addForeignPtrFinalizerEnv p_ca_ext_clear resp ctxf
  return $ CaExt res

withCaExt (CaExt x) f = do
  withForeignPtr x $ \px -> f px >>= return . (CaExt x,)

-- Memory management -----------------------------------------------------------

-- | /ca_ext_init_qqbar/ /res/ /x/ /ctx/ 
--
-- Initializes /res/ and sets it to the algebraic constant /x/.
foreign import ccall "ca_ext.h ca_ext_init_qqbar"
  ca_ext_init_qqbar :: Ptr CCaExt -> Ptr CQQbar -> Ptr CCaCtx -> IO ()

-- | /ca_ext_init_const/ /res/ /func/ /ctx/ 
--
-- Initializes /res/ and sets it to the constant defined by /func/
-- (example: /func/ = /CA_Pi/ for \(x = \pi\)).
foreign import ccall "ca_ext.h ca_ext_init_const"
  ca_ext_init_const :: Ptr CCaExt -> CCalciumFunctionCode -> Ptr CCaCtx -> IO ()

-- | /ca_ext_init_fx/ /res/ /func/ /x/ /ctx/ 
--
-- Initializes /res/ and sets it to the univariate function value \(f(x)\)
-- where /f/ is defined by /func/ (example: /func/ = /CA_Exp/ for \(e^x\)).
foreign import ccall "ca_ext.h ca_ext_init_fx"
  ca_ext_init_fx :: Ptr CCaExt -> CCalciumFunctionCode -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_ext_init_fxy/ /res/ /func/ /x/ /y/ /ctx/ 
--
-- Initializes /res/ and sets it to the bivariate function value
-- \(f(x, y)\) where /f/ is defined by /func/ (example: /func/ = /CA_Pow/
-- for \(x^y\)).
foreign import ccall "ca_ext.h ca_ext_init_fxy"
  ca_ext_init_fxy :: Ptr CCaExt -> CCalciumFunctionCode -> Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_ext_init_fxn/ /res/ /func/ /x/ /nargs/ /ctx/ 
--
-- Initializes /res/ and sets it to the multivariate function value
-- \(f(x_1, \ldots, x_n)\) where /f/ is defined by /func/ and /n/ is given
-- by /nargs/.
foreign import ccall "ca_ext.h ca_ext_init_fxn"
  ca_ext_init_fxn :: Ptr CCaExt -> CCalciumFunctionCode -> Ptr CCa -> CLong -> Ptr CCaCtx -> IO ()

-- | /ca_ext_init_set/ /res/ /x/ /ctx/ 
--
-- Initializes /res/ and sets it to a copy of /x/.
foreign import ccall "ca_ext.h ca_ext_init_set"
  ca_ext_init_set :: Ptr CCaExt -> Ptr CCaExt -> Ptr CCaCtx -> IO ()

-- | /ca_ext_clear/ /res/ /ctx/ 
--
-- Clears /res/.
foreign import ccall "ca_ext.h ca_ext_clear"
  ca_ext_clear :: Ptr CCaExt -> Ptr CCaCtx -> IO ()

foreign import ccall "ca_ext.h &ca_ext_clear"
  p_ca_ext_clear :: FunPtr (Ptr CCaExt -> Ptr CCaCtx -> IO ())

-- Structure -------------------------------------------------------------------

-- | /ca_ext_nargs/ /x/ /ctx/ 
--
-- Returns the number of function arguments of /x/. The return value is 0
-- for any algebraic constant and for any built-in symbolic constant such
-- as \(\pi\).
foreign import ccall "ca_ext.h ca_ext_nargs"
  ca_ext_nargs :: Ptr CCaExt -> Ptr CCaCtx -> IO CLong

-- | /ca_ext_get_arg/ /res/ /x/ /i/ /ctx/ 
--
-- Sets /res/ to argument /i/ (indexed from zero) of /x/. This calls
-- /flint_abort/ if /i/ is out of range.
foreign import ccall "ca_ext.h ca_ext_get_arg"
  ca_ext_get_arg :: Ptr CCa -> Ptr CCaExt -> CLong -> Ptr CCaCtx -> IO ()

-- | /ca_ext_hash/ /x/ /ctx/ 
--
-- Returns a hash of the structural representation of /x/.
foreign import ccall "ca_ext.h ca_ext_hash"
  ca_ext_hash :: Ptr CCaExt -> Ptr CCaCtx -> IO CULong

-- | /ca_ext_equal_repr/ /x/ /y/ /ctx/ 
--
-- Tests /x/ and /y/ for structural equality, returning 0 (false) or 1
-- (true).
foreign import ccall "ca_ext.h ca_ext_equal_repr"
  ca_ext_equal_repr :: Ptr CCaExt -> Ptr CCaExt -> Ptr CCaCtx -> IO CInt

-- | /ca_ext_cmp_repr/ /x/ /y/ /ctx/ 
--
-- Compares the representations of /x/ and /y/ in a canonical sort order,
-- returning -1, 0 or 1. This only performs a structural comparison of the
-- symbolic representations; the return value does not say anything
-- meaningful about the numbers represented by /x/ and /y/.
foreign import ccall "ca_ext.h ca_ext_cmp_repr"
  ca_ext_cmp_repr :: Ptr CCaExt -> Ptr CCaExt -> Ptr CCaCtx -> IO CInt

-- Input and output ------------------------------------------------------------

foreign import ccall "ca_ext.h ca_ext_get_str"
  ca_ext_get_str :: Ptr CCaExt -> Ptr CCaCtx -> IO CString

foreign import ccall "ca_ext.h ca_ext_fprint"
  ca_ext_fprint :: Ptr CFile -> Ptr CCaExt -> Ptr CCaCtx -> IO ()

-- | /ca_ext_print/ /x/ /ctx/ 
--
-- Prints a description of /x/ to standard output.
ca_ext_print :: Ptr CCaExt -> Ptr CCaCtx -> IO ()
ca_ext_print x ctx = do
  printCStr (flip ca_ext_get_str ctx) x
  return ()

-- Numerical evaluation --------------------------------------------------------

-- | /ca_ext_get_acb_raw/ /res/ /x/ /prec/ /ctx/ 
--
-- Sets /res/ to an enclosure of the numerical value of /x/. A working
-- precision of /prec/ bits is used for the evaluation, without adaptive
-- refinement.
foreign import ccall "ca_ext.h ca_ext_get_acb_raw"
  ca_ext_get_acb_raw :: Ptr CAcb -> Ptr CCaExt -> CLong -> Ptr CCaCtx -> IO ()

-- Cache -----------------------------------------------------------------------







-- | /ca_ext_cache_init/ /cache/ /ctx/ 
--
-- Initializes /cache/ for use.
foreign import ccall "ca_ext.h ca_ext_cache_init"
  ca_ext_cache_init :: Ptr CCaExtCache -> Ptr CCaCtx -> IO ()

-- | /ca_ext_cache_clear/ /cache/ /ctx/ 
--
-- Clears /cache/, freeing the memory allocated internally.
foreign import ccall "ca_ext.h ca_ext_cache_clear"
  ca_ext_cache_clear :: Ptr CCaExtCache -> Ptr CCaCtx -> IO ()

-- | /ca_ext_cache_insert/ /cache/ /x/ /ctx/ 
--
-- Adds /x/ to /cache/ without duplication. If a structurally identical
-- instance already exists in /cache/, a pointer to that instance is
-- returned. Otherwise, a copy of /x/ is inserted into /cache/ and a
-- pointer to that new instance is returned.
foreign import ccall "ca_ext.h ca_ext_cache_insert"
  ca_ext_cache_insert :: Ptr CCaExtCache -> Ptr CCaExt -> Ptr CCaCtx -> IO (Ptr CCaExt)




