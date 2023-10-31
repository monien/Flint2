module Data.Number.Flint.Calcium.Ca.Field.FFI (
  -- * Extension fields
    CaField (..)
  , CCaField (..)
  -- * Memory management
  , ca_field_init_qq
  , ca_field_init_nf
  , ca_field_init_const
  , ca_field_init_fx
  , ca_field_init_fxy
  , ca_field_init_multi
  , ca_field_set_ext
  , ca_field_clear
  -- * Input and output
  , ca_field_print
  -- * Ideal
  , ca_field_build_ideal
  , ca_field_build_ideal_erf
  -- * Structure operations
  , ca_field_cmp
  -- * Cache
  , ca_field_cache_init
  , ca_field_cache_clear
  , ca_field_cache_insert_ext
) where 

-- Extension fields ------------------------------------------------------------

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.C.Types

import Data.Number.Flint.NF.QQbar
import Data.Number.Flint.Calcium
import Data.Number.Flint.Calcium.Ca.Types

-- ca_field -------------------------------------------------------------------
  
-- Memory management -----------------------------------------------------------

-- | /ca_field_init_qq/ /K/ /ctx/ 
--
-- Initializes /K/ to represent the trivial field \(\mathbb{Q}\).
foreign import ccall "ca_field.h ca_field_init_qq"
  ca_field_init_qq :: Ptr CCaField -> Ptr CCaCtx -> IO ()

-- | /ca_field_init_nf/ /K/ /x/ /ctx/ 
--
-- Initializes /K/ to represent the algebraic number field
-- \(\mathbb{Q}(x)\).
foreign import ccall "ca_field.h ca_field_init_nf"
  ca_field_init_nf :: Ptr CCaField -> Ptr CQQbar -> Ptr CCaCtx -> IO ()

-- | /ca_field_init_const/ /K/ /func/ /ctx/ 
--
-- Initializes /K/ to represent the field \(\mathbb{Q}(x)\) where /x/ is a
-- builtin constant defined by /func/ (example: /func/ = /CA_Pi/ for
-- \(x = \pi\)).
foreign import ccall "ca_field.h ca_field_init_const"
  ca_field_init_const :: Ptr CCaField -> CCalciumFunctionCode -> Ptr CCaCtx -> IO ()

-- | /ca_field_init_fx/ /K/ /func/ /x/ /ctx/ 
--
-- Initializes /K/ to represent the field \(\mathbb{Q}(a)\) where
-- \(a = f(x)\), given a number /x/ and a builtin univariate function
-- /func/ (example: /func/ = /CA_Exp/ for \(e^x\)).
foreign import ccall "ca_field.h ca_field_init_fx"
  ca_field_init_fx :: Ptr CCaField -> CCalciumFunctionCode -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_field_init_fxy/ /K/ /func/ /x/ /y/ /ctx/ 
--
-- Initializes /K/ to represent the field \(\mathbb{Q}(a,b)\) where
-- \(a = f(x, y)\).
foreign import ccall "ca_field.h ca_field_init_fxy"
  ca_field_init_fxy :: Ptr CCaField -> CCalciumFunctionCode -> Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_field_init_multi/ /K/ /len/ /ctx/ 
--
-- Initializes /K/ to represent a multivariate field
-- \(\mathbb{Q}(a_1, \ldots, a_n)\) in /n/ extension numbers. The extension
-- numbers must subsequently be assigned one by one using
-- @ca_field_set_ext@.
foreign import ccall "ca_field.h ca_field_init_multi"
  ca_field_init_multi :: Ptr CCaField -> CLong -> Ptr CCaCtx -> IO ()

-- | /ca_field_set_ext/ /K/ /i/ /x_index/ /ctx/ 
--
-- Sets the extension number at position /i/ (here indexed from 0) of /K/
-- to the generator of the field with index /x_index/ in /ctx/. (It is
-- assumed that the generating field is a univariate field.)
-- 
-- This only inserts a shallow reference: the field at index /x_index/ must
-- be kept alive until /K/ has been cleared.
foreign import ccall "ca_field.h ca_field_set_ext"
  ca_field_set_ext :: Ptr CCaField -> CLong -> Ptr CCaExt -> Ptr CCaCtx -> IO ()

-- | /ca_field_clear/ /K/ /ctx/ 
--
-- Clears the field /K/. This does not clear the individual extension
-- numbers, which are only held as references.
foreign import ccall "ca_field.h ca_field_clear"
  ca_field_clear :: Ptr CCaField -> Ptr CCaCtx -> IO ()

foreign import ccall "ca_field.h &ca_field_clear"
  p_ca_field_clear :: FunPtr (Ptr CCaField -> Ptr CCaCtx -> IO ())

-- Input and output ------------------------------------------------------------

-- | /ca_field_print/ /K/ /ctx/ 
--
-- Prints a description of the field /K/ to standard output.
foreign import ccall "ca_field.h ca_field_print"
  ca_field_print :: Ptr CCaField -> Ptr CCaCtx -> IO ()

-- Ideal -----------------------------------------------------------------------

-- | /ca_field_build_ideal/ /K/ /ctx/ 
--
-- Given /K/ with assigned extension numbers, builds the reduction ideal
-- in-place.
foreign import ccall "ca_field.h ca_field_build_ideal"
  ca_field_build_ideal :: Ptr CCaField -> Ptr CCaCtx -> IO ()

-- | /ca_field_build_ideal_erf/ /K/ /ctx/ 
--
-- Builds relations for error functions present among the extension numbers
-- in /K/. This heuristic adds relations that are consequences of the
-- functional equations
-- \(\operatorname{erf}(x) = -\operatorname{erf}(-x)\),
-- \(\operatorname{erfc}(x) = 1-\operatorname{erf}(x)\),
-- \(\operatorname{erfi}(x) = -i\operatorname{erf}(ix)\).
foreign import ccall "ca_field.h ca_field_build_ideal_erf"
  ca_field_build_ideal_erf :: Ptr CCaField -> Ptr CCaCtx -> IO ()

-- Structure operations --------------------------------------------------------

-- | /ca_field_cmp/ /K1/ /K2/ /ctx/ 
--
-- Compares the field objects /K1/ and /K2/ in a canonical sort order,
-- returning -1, 0 or 1. This only performs a lexicographic comparison of
-- the representations of /K1/ and /K2/; the return value does not say
-- anything meaningful about the relative structures of /K1/ and /K2/ as
-- mathematical fields.
foreign import ccall "ca_field.h ca_field_cmp"
  ca_field_cmp :: Ptr CCaField -> Ptr CCaField -> Ptr CCaCtx -> IO CInt

-- Cache -----------------------------------------------------------------------

-- | /ca_field_cache_init/ /cache/ /ctx/ 
--
-- Initializes /cache/ for use.
foreign import ccall "ca_field.h ca_field_cache_init"
  ca_field_cache_init :: Ptr CCaFieldCache -> Ptr CCaCtx -> IO ()

-- | /ca_field_cache_clear/ /cache/ /ctx/ 
--
-- Clears /cache/, freeing the memory allocated internally. This does not
-- clear the individual extension numbers, which are only held as
-- references.
foreign import ccall "ca_field.h ca_field_cache_clear"
  ca_field_cache_clear :: Ptr CCaFieldCache -> Ptr CCaCtx -> IO ()

-- | /ca_field_cache_insert_ext/ /cache/ /x/ /len/ /ctx/ 
--
-- Adds the field defined by the length-/len/ list of extension numbers /x/
-- to /cache/ without duplication. If such a field already exists in
-- /cache/, a pointer to that instance is returned. Otherwise, a field with
-- extension numbers /x/ is inserted into /cache/ and a pointer to that new
-- instance is returned. Upon insertion of a new field, the reduction ideal
-- is constructed via @ca_field_build_ideal@.
foreign import ccall "ca_field.h ca_field_cache_insert_ext"
  ca_field_cache_insert_ext :: Ptr CCaFieldCache -> Ptr (Ptr CCaExt) -> CLong -> Ptr CCaCtx -> IO (Ptr CCaField)




