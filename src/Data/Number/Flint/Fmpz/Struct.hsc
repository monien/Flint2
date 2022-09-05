{-# language
    CApiFFI
  , FlexibleInstances
  , ForeignFunctionInterface
  , TupleSections
  #-}

module Data.Number.Flint.Fmpz.Struct (
  -- * Flint integers
    Fmpz (..)
  , CFmpz (..)
  , newFmpz
  , withFmpz
  , withNewFmpz
  -- * Memory management mpz
  , _fmpz_new_mpz
  , _fmpz_clear_mpz
  , _fmpz_cleanup_mpz_content
  , _fmpz_cleanup
  , _fmpz_promote
  , _fmpz_promote_val
  , _fmpz_demote
  , _fmpz_demote_val
  -- * Memory management
  , fmpz_init
  , fmpz_init2
  , fmpz_clear
  , fmpz_init_set
  , fmpz_init_set_ui
  , fmpz_init_set_si
  -- * Conversion Haskell Integer
  , fromFmpz
  , toFmpz
  -- * Macros
  , ptr_to_coeff
  , coeff_to_ptr
  , coeff_is_mpz
  -- * Precomputed inverse
  , FmpzPreInvN (..)
  , CFmpzPreInvN (..)
  -- * Comb for multi CRT
  , FmpzComb (..)
  , CFmpzComb (..)
  , FmpzCombTemp (..)
  , CFmpzCombTemp (..)
  , fmpz_comb_init
  , fmpz_comb_clear
  , fmpz_comb_tmp_init
  , fmpz_comb_tmp_clear
  -- * Multi CRT
  , FmpzMultiCRT (..)
  , CFmpzMultiCRT(..)
  , fmpz_multi_crt_init
  , fmpz_multi_crt_clear
  ) where

-- Types, macros and constants -------------------------------------------------

import System.IO.Unsafe

import Control.Monad

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr, nullPtr )
import Foreign.Storable
import Foreign.Marshal ( free )

import Numeric.GMP.Utils (withInInteger, withOutInteger_) 
import Numeric.GMP.Types (MPZ)

import Data.Number.Flint.Internal
import Data.Number.Flint.External
import Data.Number.Flint.Flint
import Data.Number.Flint.NMod.Struct
import Data.Number.Flint.Fmpz.Factor.Struct

#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpz_factor.h>

-- fmpz_t ----------------------------------------------------------------------

-- | Integer (opaque pointer)
data Fmpz = Fmpz {-# UNPACK #-} !(ForeignPtr CFmpz)
type CFmpz = CFlint Fmpz

instance Storable CFmpz where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fmpz_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fmpz_t}
  peek = error "CFmpz.peek: Not defined"
  poke = error "CFmpz.poke: Not defined"

-- | Create a new `Fmpz` structure.
newFmpz = do
  x <- mallocForeignPtr
  withForeignPtr p fmpz_init
  addForeignPtrFinalizer p_fmpz_clear x
  return $ Fmpz x

-- | Use `Fmpz` structure.
{-# INLINE withFmpz #-}
withFmpz (Fmpz x) f = do
  withForeignPtr x $ \xp -> f xp >>= return . (Fmpz x,)

withNewFmpz f = do
  x <- newFmpz
  withFmpz x $ \x -> f x
  
-- fmpz_preinv_t --------------------------------------------------

-- | Data structure containing the /CFmpz/ pointer
data FmpzPreInvN = FmpzPreInvN
  {-# UNPACK #-} !(ForeignPtr CFmpzPreInvN) 
type CFmpzPreInvN = CFlint FmpzPreInvN 

--- conversion Integer <-> Fmpz ------------------------------------------------

fromFmpz x = withOutInteger_ $ \y -> withFmpz x $ \x -> fmpz_get_mpz y x
      
toFmpz x = do
  y <- newFmpz
  withInInteger x $ \x ->
    withFmpz y $ \y ->
      fmpz_set_mpz y x
  return y

-- macros ----------------------------------------------------------------------

-- | /PTR_TO_COEFF/ /ptr/ 
-- 
-- a macro to convert an @mpz_t@ (or more generally any @__mpz_struct *@)
-- to an @fmpz@ (shifts the pointer right by \(2\) and sets the second most
-- significant bit).
foreign import ccall "fmpz.h PTR_TO_COEFF"
  ptr_to_coeff :: Ptr CMpz -> IO CFmpz

-- | /COEFF_TO_PTR/ /f/ 
-- 
-- a macro to convert an @fmpz@ which represents a pointer into an actual
-- pointer to an @__mpz_struct@ (i.e. to an @mpz_t@).
foreign import ccall "fmpz.h COEFF_TO_PTR"
  coeff_to_ptr :: CFmpz -> IO (Ptr CMpz)

-- | /COEFF_IS_MPZ/ /f/ 
-- 
-- a macro which returns \(1\) if \(f\) represents an @mpz_t@, otherwise
-- \(0\) is returned.
foreign import ccall "fmpz.h COEFF_IS_MPZ"
  coeff_is_mpz :: CFmpz -> IO CInt

-- Memory management -----------------------------------------------------------

-- | /_fmpz_new_mpz/ 
-- 
-- initialises a new @mpz_t@ and returns a pointer to it. This is only used
-- internally.
foreign import ccall "fmpz.h _fmpz_new_mpz"
  _fmpz_new_mpz :: IO (Ptr CMpz)

-- | /_fmpz_clear_mpz/ /f/ 
-- 
-- clears the @mpz_t@ \"pointed to\" by the @fmpz@ \(f\). This is only used
-- internally.
foreign import ccall "fmpz.h _fmpz_clear_mpz"
  _fmpz_clear_mpz :: CFmpz -> IO ()

-- | /_fmpz_cleanup_mpz_content/ 
-- 
-- this function does nothing in the reentrant version of @fmpz@.
foreign import ccall "fmpz.h _fmpz_cleanup_mpz_content"
  _fmpz_cleanup_mpz_content :: IO ()

-- | /_fmpz_cleanup/ 
-- 
-- this function does nothing in the reentrant version of @fmpz@.
foreign import ccall "fmpz.h _fmpz_cleanup"
  _fmpz_cleanup :: IO ()

-- | /_fmpz_promote/ /f/ 
-- 
-- if \(f\) doesn\'t represent an @mpz_t@, initialise one and associate it
-- to \(f\).
foreign import ccall "fmpz.h _fmpz_promote"
  _fmpz_promote :: Ptr CFmpz -> IO (Ptr CMpz)

-- | /_fmpz_promote_val/ /f/ 
-- 
-- if \(f\) doesn\'t represent an @mpz_t@, initialise one and associate it
-- to \(f\), but preserve the value of \(f\).
-- 
-- This function is for internal use. The resulting @fmpz@ will be backed
-- by an @mpz_t@ that can be passed to GMP, but the @fmpz@ will be in an
-- inconsistent state with respect to the other Flint @fmpz@ functions such
-- as @fmpz_is_zero@, etc.
foreign import ccall "fmpz.h _fmpz_promote_val"
  _fmpz_promote_val :: Ptr CFmpz -> IO (Ptr CMpz)

-- | /_fmpz_demote/ /f/ 
-- 
-- if \(f\) represents an @mpz_t@ clear it and make \(f\) just represent an
-- @slong@.
foreign import ccall "fmpz.h _fmpz_demote"
  _fmpz_demote :: Ptr CFmpz -> IO ()

-- | /_fmpz_demote_val/ /f/ 
-- 
-- if \(f\) represents an @mpz_t@ and its value will fit in an @slong@,
-- preserve the value in \(f\) which we make to represent an @slong@, and
-- clear the @mpz_t@.
foreign import ccall "fmpz.h _fmpz_demote_val"
  _fmpz_demote_val :: Ptr CFmpz -> IO ()

-- Memory management -----------------------------------------------------------

-- | /fmpz_init/ /f/ 
-- 
-- A small @fmpz_t@ is initialised, i.e.just a @slong@. The value is set to
-- zero.
foreign import ccall "fmpz.h fmpz_init"
  fmpz_init :: Ptr CFmpz -> IO ()

-- | /fmpz_init2/ /f/ /limbs/ 
-- 
-- Initialises the given @fmpz_t@ to have space for the given number of
-- limbs.
-- 
-- If @limbs@ is zero then a small @fmpz_t@ is allocated, i.e.just a
-- @slong@. The value is also set to zero. It is not necessary to call this
-- function except to save time. A call to @fmpz_init@ will do just fine.
foreign import ccall "fmpz.h fmpz_init2"
  fmpz_init2 :: Ptr CFmpz -> CULong -> IO ()

-- | /fmpz_clear/ /f/ 
-- 
-- Clears the given @fmpz_t@, releasing any memory associated with it,
-- either back to the stack or the OS, depending on whether the reentrant
-- or non-reentrant version of FLINT is built.
foreign import ccall "fmpz.h fmpz_clear"
  fmpz_clear :: Ptr CFmpz -> IO ()

foreign import capi "flint/fmpz.h &fmpz_clear"
  p_fmpz_clear :: FunPtr (Ptr CFmpz -> IO ())

foreign import ccall "fmpz.h fmpz_init_set"
  fmpz_init_set :: Ptr CFmpz -> Ptr CFmpz -> IO ()

foreign import ccall "fmpz.h fmpz_init_set_ui"
  fmpz_init_set_ui :: Ptr CFmpz -> CULong -> IO ()

-- | /fmpz_init_set_si/ /f/ /g/ 
-- 
-- Initialises \(f\) and sets it to the value of \(g\).
foreign import ccall "fmpz.h fmpz_init_set_si"
  fmpz_init_set_si :: Ptr CFmpz -> CLong -> IO ()

-- fmpz_comb_t -----------------------------------------------------------------

data FmpzComb = FmpzComb {-# UNPACK #-} !(ForeignPtr CFmpzComb)
type CFmpzComb = CFlint FmpzComb

instance Storable CFmpzComb where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fmpz_comb_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fmpz_comb_t}
  peek = error "CFmpzComb.peek: Not defined"
  poke = error "CFmpzComb.poke: Not defined"

newFmpzComb primes num_primes = do
  p <- mallocForeignPtr
  withForeignPtr p $ \p -> fmpz_comb_init p primes num_primes
  addForeignPtrFinalizer p_fmpz_comb_clear p
  return $ FmpzComb p

{-# INLINE withFmpzComb #-}
withFmpzComb (FmpzComb p) f = do
  withForeignPtr p $ \fp -> f fp >>= return . (FmpzComb p,)

-- fmpz_comb_temp_t ------------------------------------------------------------

data FmpzCombTemp = FmpzCombTemp {-# UNPACK #-} !(ForeignPtr CFmpzCombTemp)
type CFmpzCombTemp = CFlint FmpzCombTemp

instance Storable CFmpzCombTemp where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fmpz_comb_temp_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fmpz_comb_temp_t}
  peek = error "CFmpzCombTemp.peek: Not defined"
  poke = error "CFmpzCombTemp.poke: Not defined"

newFmpzCombTemp comb = do
  p <- mallocForeignPtr
  withForeignPtr p $ \p -> fmpz_comb_temp_init p comb
  addForeignPtrFinalizer p_fmpz_comb_temp_clear p
  return $ FmpzCombTemp p

{-# INLINE withFmpzCombTemp #-}
withFmpzCombTemp (FmpzCombTemp p) f = do
  withForeignPtr p $ \fp -> f fp >>= return . (FmpzCombTemp p,)

--------------------------------------------------------------------------------

-- | /fmpz_comb_init/ /comb/ /primes/ /num_primes/ 
-- 
-- Initialises a @comb@ structure for multimodular reduction and
-- recombination. The array @primes@ is assumed to contain @num_primes@
-- primes each of @FLINT_BITS - 1@ bits. Modular reductions and
-- recombinations will be done modulo this list of primes. The @primes@
-- array must not be @free@\'d until the @comb@ structure is no longer
-- required and must be cleared by the user.
foreign import ccall "fmpz.h fmpz_comb_init"
  fmpz_comb_init :: Ptr CFmpzComb -> Ptr CMp -> CLong -> IO ()

-- | /fmpz_comb_temp_init/ /temp/ /comb/ 
-- 
-- Creates temporary space to be used by multimodular and CRT functions
-- based on an initialised @comb@ structure.
foreign import ccall "fmpz.h fmpz_comb_temp_init"
  fmpz_comb_temp_init :: Ptr CFmpzCombTemp -> Ptr CFmpzComb -> IO ()

-- | /fmpz_comb_clear/ /comb/ 
-- 
-- Clears the given @comb@ structure, releasing any memory it uses.
foreign import ccall "fmpz.h fmpz_comb_clear"
  fmpz_comb_clear :: Ptr CFmpzComb -> IO ()

-- | /fmpz_comb_temp_clear/ /temp/ 
-- 
-- Clears temporary space @temp@ used by multimodular and CRT functions
-- using the given @comb@ structure.
foreign import ccall "fmpz.h fmpz_comb_temp_clear"
  fmpz_comb_temp_clear :: Ptr CFmpzCombTemp -> IO ()

-- fmpz_multi_crt_t ------------------------------------------------------------

data FmpzMultiCRT = FmpzMultiCRT {-# UNPACK #-} !(ForeignPtr CFmpzMultiCRT)
type CFmpzMultiCRT = CFlint FmpzMultiCRT

instance Storable CFmpzMultiCRT where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fmpz_multi_crt_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fmpz_multi_crt_t}
  peek = error "CFmpzMultiCRT.peek: Not defined"
  poke = error "CFmpzMultiCRT.poke: Not defined"

newFmpzMultiCRT = do
  p <- mallocForeignPtr
  withForeignPtr p fmpz_multi_crt_init
  addForeignPtrFinalizer p_fmpz_multi_crt_clear p
  return $ FmpzMultiCRT p

{-# INLINE withFmpzMultiCRT #-}
withFmpzMultiCRT (FmpzMultiCRT p) f = do
  withForeignPtr p $ \fp -> f fp >>= return . (FmpzMultiCRT p,)

--------------------------------------------------------------------------------

-- | /fmpz_multi_crt_init/ /CRT/ 
-- 
-- Initialize @CRT@ for Chinese remaindering.
foreign import ccall "fmpz.h fmpz_multi_crt_init"
  fmpz_multi_crt_init :: Ptr CFmpzMultiCRT -> IO ()

-- | /fmpz_multi_crt_clear/ /P/ 
-- 
-- Free all space used by @CRT@.
foreign import ccall "fmpz.h fmpz_multi_crt_clear"
   :: Ptr CFmpzMultiCRT -> IO ()
