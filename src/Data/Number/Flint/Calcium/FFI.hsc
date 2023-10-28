{-|
module      :  Data.Number.Flint.Calcium.FFI
copyright   :  (c) 2023 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de
-}
module Data.Number.Flint.Calcium.FFI (
  -- * Calcium
    CalciumStream (..)
  , CCalciumStream (..)
  -- * Version
  , calcium_version
  -- * Triple-valued logic
  -- * Flint, Arb and Antic extras
--, calcium_fmpz_hash
  -- * Input and output
  , calcium_stream_init_file
--, calcium_stream_init_str
  , calcium_write
--, calcium_write_free
  , calcium_write_si
  , calcium_write_fmpz
  , calcium_write_arb
  , calcium_write_acb
) where

-- Calcium ---------------------------------------------------------------------

import Foreign.C.Types
import Foreign.C.String
import Foreign.ForeignPtr
import Foreign.Ptr
import Foreign.Storable

import Data.Number.Flint.Fmpz
import Data.Number.Flint.Arb.Types
import Data.Number.Flint.Acb.Types

#include <flint/flint.h>
#include <flint/calcium.h>

-- calcium_stream_t ------------------------------------------------------------

data CalciumStream = CalciumStream {-# UNPACK #-} !(ForeignPtr CCalciumStream)
data CCalciumStream = CCalciumStream (Ptr CFile) CString CLong CLong

instance Storable CCalciumStream where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size calcium_stream_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment calcium_stream_t}
  peek ptr = CCalciumStream
    <$> (return $ castPtr ptr)
    <*> #{peek calcium_stream_struct, s    } ptr
    <*> #{peek calcium_stream_struct, len  } ptr
    <*> #{peek calcium_stream_struct, alloc} ptr
  poke = undefined
  
-- Version ---------------------------------------------------------------------

-- | /calcium_version/ 
--
-- Returns a pointer to the version of the library as a string @X.Y.Z@.
foreign import ccall "calcium.h calcium_version"
  calcium_version :: IO CString

-- Triple-valued logic ---------------------------------------------------------

-- | Triple-valued logic
newtype CTruth = CTruth {_CTruth :: CULong} deriving (Show, Eq)

#{enum CTruth, CTruth
  , t_true    = T_TRUE
  , t_false   = T_FALSE
  , t_unknown = T_UNKNOWN
  }

newtype CCalciumFunctionCode =
  CCalciumFunctionCode {_CCalciumFunctionCode :: CULong} deriving (Show, Eq)

#{enum CCalciumFunctionCode, CCalciumFunctionCode
  , ca_QQBar = CA_QQBar
  , ca_Neg = CA_Neg
  , ca_Add = CA_Add
  , ca_Sub = CA_Sub
  , ca_Mul = CA_Mul
  , ca_Div = CA_Div
  , ca_Sqrt = CA_Sqrt
  , ca_Cbrt = CA_Cbrt
  , ca_Root = CA_Root
  , ca_Floor = CA_Floor
  , ca_Ceil = CA_Ceil
  , ca_Abs = CA_Abs
  , ca_Sign = CA_Sign
  , ca_Re = CA_Re
  , ca_Im = CA_Im
  , ca_Arg = CA_Arg
  , ca_Conjugate = CA_Conjugate
  , ca_Pi = CA_Pi
  , ca_Sin = CA_Sin
  , ca_Cos = CA_Cos
  , ca_Exp = CA_Exp
  , ca_Log = CA_Log
  , ca_Pow = CA_Pow
  , ca_Tan = CA_Tan
  , ca_Cot = CA_Cot
  , ca_Cosh = CA_Cosh
  , ca_Sinh = CA_Sinh
  , ca_Tanh = CA_Tanh
  , ca_Coth = CA_Coth
  , ca_Atan = CA_Atan
  , ca_Acos = CA_Acos
  , ca_Asin = CA_Asin
  , ca_Acot = CA_Acot
  , ca_Atanh = CA_Atanh
  , ca_Acosh = CA_Acosh
  , ca_Asinh = CA_Asinh
  , ca_Acoth = CA_Acoth
  , ca_Euler = CA_Euler
  , ca_Gamma = CA_Gamma
  , ca_LogGamma = CA_LogGamma
  , ca_Psi = CA_Psi
  , ca_Erf = CA_Erf
  , ca_Erfc = CA_Erfc
  , ca_Erfi = CA_Erfi
  , ca_RiemannZeta = CA_RiemannZeta
  , ca_HurwitzZeta = CA_HurwitzZeta
  , ca_FUNC_CODE_LENGTH = CA_FUNC_CODE_LENGTH
  }

-- Flint, Arb and Antic extras -------------------------------------------------

-- Here we collect various utility methods for Flint, Arb and Antic types
-- that are missing in those libraries. Some of these functions may be
-- migrated upstream in the future.
--
-- -- | /calcium_fmpz_hash/ /x/ 
--
-- -- Hash function for integers. The algorithm may change; presently, this
-- -- simply extracts the low word (with sign).
-- foreign import ccall "calcium.h calcium_fmpz_hash"
--   calcium_fmpz_hash :: Ptr CFmpz -> IO CULong

-- Input and output ------------------------------------------------------------

-- | /calcium_stream_init_file/ /out/ /fp/ 
--
-- Initializes the stream /out/ for writing to the file /fp/. The file can
-- be /stdout/, /stderr/, or any file opened for writing by the user.
foreign import ccall "calcium.h calcium_stream_init_file"
  calcium_stream_init_file :: Ptr CCalciumStream -> Ptr CFile -> IO ()

-- -- | /calcium_stream_init_str/ /out/ 
--
-- -- Initializes the stream /out/ for writing to a string in memory. When
-- -- finished, the user should free the string (the /s/ member of /out/ with
-- -- @flint_free()@).
-- foreign import ccall "calcium.h calcium_stream_init_str"
--   calcium_stream_init_str :: Ptr CCalciumStream -> IO ()

-- | /calcium_write/ /out/ /s/ 
--
-- Writes the string /s/ to /out/.
foreign import ccall "calcium.h calcium_write"
  calcium_write :: Ptr CCalciumStream -> CString -> IO ()

-- -- | /calcium_write_free/ /out/ /s/ 
--
-- -- Writes /s/ to /out/ and then frees /s/ by calling @flint_free()@.
-- foreign import ccall "calcium.h calcium_write_free"
--   calcium_write_free :: Ptr CCalciumStream -> CString -> IO ()

-- | /calcium_write_si/ /out/ /x/ 
foreign import ccall "calcium.h calcium_write_si"
  calcium_write_si :: Ptr CCalciumStream -> CLong -> IO ()
  
-- | /calcium_write_fmpz/ /out/ /x/ 
--
-- Writes the integer /x/ to /out/.
foreign import ccall "calcium.h calcium_write_fmpz"
  calcium_write_fmpz :: Ptr CCalciumStream
                     -> Ptr CFmpz -> IO ()

-- | /calcium_write_arb/ /out/ /z/ /digits/ /flags/ 
foreign import ccall "calcium.h calcium_write_arb"
  calcium_write_arb :: Ptr CCalciumStream
                    -> Ptr CArb -> CLong -> CULong -> IO ()
-- | /calcium_write_acb/ /out/ /z/ /digits/ /flags/ 
--
-- Writes the Arb number /z/ to /out/, showing /digits/ digits and with the
-- display style specified by /flags/ (@ARB_STR_NO_RADIUS@, etc.).
foreign import ccall "calcium.h calcium_write_acb"
  calcium_write_acb :: Ptr CCalciumStream
  -> Ptr CAcb -> CLong -> CULong -> IO ()