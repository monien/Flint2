module Data.Number.Flint.External.Mpfr.FFI where

import Data.Word
import Foreign.C.Types
import Foreign.ForeignPtr
import Data.Number.Flint.Internal

-- MPFR ------------------------------------------------------------------------

-- | Data structure containing the CMpfr pointer
data Mpfr = CMpfr {-# UNPACK #-} !(ForeignPtr CMpfr) 
type CMpfr = CFlint Mpfr

newtype CMpfrRnd  = CMpfrRnd  {_MpfrRnd  :: CInt} deriving (Show, Eq)
newtype CMpfrPrec = CMpfrPrec {_MpfrPrec :: CInt} deriving (Show, Eq)
