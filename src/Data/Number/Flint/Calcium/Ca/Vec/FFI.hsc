module Data.Number.Flint.Calcium.Ca.Vec.FFI (
  -- * Vectors of real and complex numbers
  -- * Types, macros and constants
  -- * Memory management
    CaVec (..)
  , CCaVec (..)
  , newCaVec
  , withCaVec
  , withNewCaVec
  , _ca_vec_init
  , ca_vec_init
  , _ca_vec_clear
  , ca_vec_clear
  , _ca_vec_swap
  , ca_vec_swap
  -- * Length
  , ca_vec_length
  , _ca_vec_fit_length
  , ca_vec_set_length
  -- * Assignment
  , _ca_vec_set
  , ca_vec_set
  -- * Special vectors
  , _ca_vec_zero
  , ca_vec_zero
  -- * Input and output
  , ca_vec_print
  , ca_vec_printn
  -- * List operations
  , ca_vec_append
  -- * Arithmetic
  , _ca_vec_neg
  , ca_vec_neg
  , _ca_vec_add
  , _ca_vec_sub
  , _ca_vec_scalar_mul_ca
  , _ca_vec_scalar_div_ca
  , _ca_vec_scalar_addmul_ca
  , _ca_vec_scalar_submul_ca
  -- * Comparisons and properties
  , _ca_vec_check_is_zero
  -- * Internal representation
  , _ca_vec_is_fmpq_vec
  , _ca_vec_fmpq_vec_is_fmpz_vec
  , _ca_vec_fmpq_vec_get_fmpz_vec_den
  , _ca_vec_set_fmpz_vec_div_fmpz
) where

-- Vectors of real and complex numbers -----------------------------------------

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.C.Types
import Foreign.Storable

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Calcium
import Data.Number.Flint.Calcium.Ca
import Data.Number.Flint.Calcium.Ca.Types

#include <flint/ca_vec.h>

-- ca_vec_t --------------------------------------------------------------------

instance Storable CCaVec where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size ca_vec_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment ca_vec_t}
  peek = error "CCaVec.peek: Not defined"
  poke = error "CCaVec.poke: Not defined"

newCaVec len ctx@(CaCtx ctxf) = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> do
    withCaCtx ctx $ \ctx -> do
      ca_vec_init x len ctx
    addForeignPtrFinalizerEnv p_ca_vec_clear x ctxf
  return $ CaVec x
      
withCaVec (CaVec x) f = do
  withForeignPtr x $ \px -> f px >>= return . (CaVec x,)

withNewCaVec len ctx f = do
  x <- newCaVec len ctx
  withCaCtx ctx $ \ctx -> do
    withCaVec x $ \x -> do
      f x
      
-- Memory management -----------------------------------------------------------

-- | /_ca_vec_init/ /len/ /ctx/ 
--
-- Returns a pointer to an array of /len/ coefficients initialized to zero.
foreign import ccall "ca_vec.h _ca_vec_init"
  _ca_vec_init :: CLong -> Ptr CCaCtx -> IO (Ptr CCa)

-- | /ca_vec_init/ /vec/ /len/ /ctx/ 
--
-- Initializes /vec/ to a length /len/ vector. All entries are set to zero.
foreign import ccall "ca_vec.h ca_vec_init"
  ca_vec_init :: Ptr CCaVec -> CLong -> Ptr CCaCtx -> IO ()

-- | /_ca_vec_clear/ /vec/ /len/ /ctx/ 
--
-- Clears all /len/ entries in /vec/ and frees the pointer /vec/ itself.
foreign import ccall "ca_vec.h _ca_vec_clear"
  _ca_vec_clear :: Ptr CCa -> CLong -> Ptr CCaCtx -> IO ()

-- | /ca_vec_clear/ /vec/ /ctx/ 
--
-- Clears the vector /vec/.
foreign import ccall "ca_vec.h ca_vec_clear"
  ca_vec_clear :: Ptr CCaVec -> Ptr CCaCtx -> IO ()

foreign import ccall "ca_vec.h &ca_vec_clear"
  p_ca_vec_clear :: FunPtr (Ptr CCaVec -> Ptr CCaCtx -> IO ())

-- | /_ca_vec_swap/ /vec1/ /vec2/ /len/ /ctx/ 
--
-- Swaps the entries in /vec1/ and /vec2/ efficiently.
foreign import ccall "ca_vec.h _ca_vec_swap"
  _ca_vec_swap :: Ptr CCa -> Ptr CCa -> CLong -> Ptr CCaCtx -> IO ()

-- | /ca_vec_swap/ /vec1/ /vec2/ /ctx/ 
--
-- Swaps the vectors /vec1/ and /vec2/ efficiently.
foreign import ccall "ca_vec.h ca_vec_swap"
  ca_vec_swap :: Ptr CCaVec -> Ptr CCaVec -> Ptr CCaCtx -> IO ()

-- Length ----------------------------------------------------------------------

-- | /ca_vec_length/ /vec/ /ctx/ 
--
-- Returns the length of /vec/.
foreign import ccall "ca_vec.h ca_vec_length"
  ca_vec_length :: Ptr CCaVec -> Ptr CCaCtx -> IO CLong

-- | /_ca_vec_fit_length/ /vec/ /len/ /ctx/ 
--
-- Allocates space in /vec/ for /len/ elements.
foreign import ccall "ca_vec.h _ca_vec_fit_length"
  _ca_vec_fit_length :: Ptr CCaVec -> CLong -> Ptr CCaCtx -> IO ()

-- | /ca_vec_set_length/ /vec/ /len/ /ctx/ 
--
-- Sets the length of /vec/ to /len/. If /vec/ is shorter on input, it will
-- be zero-extended. If /vec/ is longer on input, it will be truncated.
foreign import ccall "ca_vec.h ca_vec_set_length"
  ca_vec_set_length :: Ptr CCaVec -> CLong -> Ptr CCaCtx -> IO ()

-- Assignment ------------------------------------------------------------------

-- | /_ca_vec_set/ /res/ /src/ /len/ /ctx/ 
--
-- Sets /res/ to a copy of /src/ of length /len/.
foreign import ccall "ca_vec.h _ca_vec_set"
  _ca_vec_set :: Ptr CCa -> Ptr CCa -> CLong -> Ptr CCaCtx -> IO ()

-- | /ca_vec_set/ /res/ /src/ /ctx/ 
--
-- Sets /res/ to a copy of /src/.
foreign import ccall "ca_vec.h ca_vec_set"
  ca_vec_set :: Ptr CCaVec -> Ptr CCaVec -> Ptr CCaCtx -> IO ()

-- Special vectors -------------------------------------------------------------

-- | /_ca_vec_zero/ /res/ /len/ /ctx/ 
--
-- Sets the /len/ entries in /res/ to zeros.
foreign import ccall "ca_vec.h _ca_vec_zero"
  _ca_vec_zero :: Ptr CCa -> CLong -> Ptr CCaCtx -> IO ()

-- | /ca_vec_zero/ /res/ /len/ /ctx/ 
--
-- Sets /res/ to the length /len/ zero vector.
foreign import ccall "ca_vec.h ca_vec_zero"
  ca_vec_zero :: Ptr CCaVec -> CLong -> Ptr CCaCtx -> IO ()

-- Input and output ------------------------------------------------------------

-- | /ca_vec_print/ /vec/ /ctx/ 
--
-- Prints /vec/ to standard output. The coefficients are printed on
-- separate lines.
foreign import ccall "ca_vec.h ca_vec_print"
  ca_vec_print :: Ptr CCaVec -> Ptr CCaCtx -> IO ()

-- | /ca_vec_printn/ /poly/ /digits/ /ctx/ 
--
-- Prints a decimal representation of /vec/ with precision specified by
-- /digits/. The coefficients are comma-separated and the whole list is
-- enclosed in square brackets.
foreign import ccall "ca_vec.h ca_vec_printn"
  ca_vec_printn :: Ptr CCaVec -> CLong -> Ptr CCaCtx -> IO ()

-- List operations -------------------------------------------------------------

-- | /ca_vec_append/ /vec/ /f/ /ctx/ 
--
-- Appends /f/ to the end of /vec/.
foreign import ccall "ca_vec.h ca_vec_append"
  ca_vec_append :: Ptr CCaVec -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- Arithmetic ------------------------------------------------------------------

-- | /_ca_vec_neg/ /res/ /src/ /len/ /ctx/ 
--
foreign import ccall "ca_vec.h _ca_vec_neg"
  _ca_vec_neg :: Ptr CCa -> Ptr CCa -> CLong -> Ptr CCaCtx -> IO ()

-- | /ca_vec_neg/ /res/ /src/ /ctx/ 
--
-- Sets /res/ to the negation of /src/.
foreign import ccall "ca_vec.h ca_vec_neg"
  ca_vec_neg :: Ptr CCaVec -> Ptr CCaVec -> Ptr CCaCtx -> IO ()

-- | /_ca_vec_add/ /res/ /vec1/ /vec2/ /len/ /ctx/ 
--
foreign import ccall "ca_vec.h _ca_vec_add"
  _ca_vec_add :: Ptr CCa -> Ptr CCa -> Ptr CCa -> CLong -> Ptr CCaCtx -> IO ()

-- | /_ca_vec_sub/ /res/ /vec1/ /vec2/ /len/ /ctx/ 
--
-- Sets /res/ to the sum or difference of /vec1/ and /vec2/, all vectors
-- having length /len/.
foreign import ccall "ca_vec.h _ca_vec_sub"
  _ca_vec_sub :: Ptr CCa -> Ptr CCa -> Ptr CCa -> CLong -> Ptr CCaCtx -> IO ()

-- | /_ca_vec_scalar_mul_ca/ /res/ /src/ /len/ /c/ /ctx/ 
--
-- Sets /res/ to /src/ multiplied by /c/, all vectors having length /len/.
foreign import ccall "ca_vec.h _ca_vec_scalar_mul_ca"
  _ca_vec_scalar_mul_ca :: Ptr CCa -> Ptr CCa -> CLong -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /_ca_vec_scalar_div_ca/ /res/ /src/ /len/ /c/ /ctx/ 
--
-- Sets /res/ to /src/ divided by /c/, all vectors having length /len/.
foreign import ccall "ca_vec.h _ca_vec_scalar_div_ca"
  _ca_vec_scalar_div_ca :: Ptr CCa -> Ptr CCa -> CLong -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /_ca_vec_scalar_addmul_ca/ /res/ /src/ /len/ /c/ /ctx/ 
--
-- Adds /src/ multiplied by /c/ to the vector /res/, all vectors having
-- length /len/.
foreign import ccall "ca_vec.h _ca_vec_scalar_addmul_ca"
  _ca_vec_scalar_addmul_ca :: Ptr CCa -> Ptr CCa -> CLong -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /_ca_vec_scalar_submul_ca/ /res/ /src/ /len/ /c/ /ctx/ 
--
-- Subtracts /src/ multiplied by /c/ from the vector /res/, all vectors
-- having length /len/.
foreign import ccall "ca_vec.h _ca_vec_scalar_submul_ca"
  _ca_vec_scalar_submul_ca :: Ptr CCa -> Ptr CCa -> CLong -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- Comparisons and properties --------------------------------------------------

-- | /_ca_vec_check_is_zero/ /vec/ /len/ /ctx/ 
--
-- Returns whether /vec/ is the zero vector.
foreign import ccall "ca_vec.h _ca_vec_check_is_zero"
  _ca_vec_check_is_zero :: Ptr CCa -> CLong -> Ptr CCaCtx -> IO (Ptr CTruth)

-- Internal representation -----------------------------------------------------

-- | /_ca_vec_is_fmpq_vec/ /vec/ /len/ /ctx/ 
--
-- Checks if all elements of /vec/ are structurally rational numbers.
foreign import ccall "ca_vec.h _ca_vec_is_fmpq_vec"
  _ca_vec_is_fmpq_vec :: Ptr CCa -> CLong -> Ptr CCaCtx -> IO CInt

-- | /_ca_vec_fmpq_vec_is_fmpz_vec/ /vec/ /len/ /ctx/ 
--
-- Assuming that all elements of /vec/ are structurally rational numbers,
-- checks if all elements are integers.
foreign import ccall "ca_vec.h _ca_vec_fmpq_vec_is_fmpz_vec"
  _ca_vec_fmpq_vec_is_fmpz_vec :: Ptr CCa -> CLong -> Ptr CCaCtx -> IO CInt

-- | /_ca_vec_fmpq_vec_get_fmpz_vec_den/ /c/ /den/ /vec/ /len/ /ctx/ 
--
-- Assuming that all elements of /vec/ are structurally rational numbers,
-- converts them to a vector of integers /c/ on a common denominator /den/.
foreign import ccall "ca_vec.h _ca_vec_fmpq_vec_get_fmpz_vec_den"
  _ca_vec_fmpq_vec_get_fmpz_vec_den :: Ptr CFmpz -> Ptr CFmpz -> Ptr CCa -> CLong -> Ptr CCaCtx -> IO ()

-- | /_ca_vec_set_fmpz_vec_div_fmpz/ /res/ /v/ /den/ /len/ /ctx/ 
--
-- Sets /res/ to the rational vector given by numerators /v/ and the common
-- denominator /den/.
foreign import ccall "ca_vec.h _ca_vec_set_fmpz_vec_div_fmpz"
  _ca_vec_set_fmpz_vec_div_fmpz :: Ptr CCa -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CCaCtx -> IO ()




