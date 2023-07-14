{-|
module      :  Data.Number.Flint.Flint.FFI
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de
-}
module Data.Number.Flint.Flint.FFI (
  -- * Allocation Functions
    flint_malloc
  , flint_realloc
  , flint_calloc
  -- * Random Numbers
  , FRandState (..)
  , CFRandState (..)
  , newFRandState
  , withFRandState
  , flint_rand_alloc
  , flint_rand_free
  , flint_randinit
  , flint_randclear
  -- * Thread functions
  , flint_set_num_threads
  , flint_get_num_threads
  , flint_set_num_workers
  , flint_reset_num_workers
) where 

-- global definitions ----------------------------------------------------------

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr )
import Foreign.Storable
import Foreign.Marshal ( free )

import Data.Number.Flint.Flint.Internal

#include <flint/flint.h>

-- Allocation Functions --------------------------------------------------------

-- | /flint_malloc/ /size/ 
-- 
-- Allocate @size@ bytes of memory.
foreign import ccall "flint.h flint_malloc"
  flint_malloc :: Ptr CSize -> IO ()

-- | /flint_realloc/ /ptr/ /size/ 
-- 
-- Reallocate an area of memory previously allocated by @flint_malloc@,
-- @flint_realloc@, or @flint_calloc@.
foreign import ccall "flint.h flint_realloc"
  flint_realloc :: Ptr () -> Ptr CSize -> IO ()

-- | /flint_calloc/ /num/ /size/ 
-- 
-- Allocate @num@ objects of @size@ bytes each, and zero the allocated
-- memory.
foreign import ccall "flint.h flint_calloc"
  flint_calloc :: Ptr CSize -> Ptr CSize -> IO ()

-- Random Numbers --------------------------------------------------------------

data FRandState = FRandState {-# UNPACK #-} !(ForeignPtr CFRandState)
type CFRandState = CFlint FRandState

instance Storable CFRandState where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size flint_rand_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment flint_rand_t}
  peek = error "CFRandState.peek: Not defined"
  poke = error "CFRandState.poke: Not defined"

newFRandState = do
  p <- mallocForeignPtr
  withForeignPtr p flint_randinit
  addForeignPtrFinalizer p_flint_randclear p
  return $ FRandState p

{-# INLINE withFRandState #-}
withFRandState (FRandState p) f = do
  withForeignPtr p $ \fp -> f fp >>= return . (FRandState p,)

--------------------------------------------------------------------------------

-- | /flint_rand_alloc/ 
-- 
-- Allocates a @flint_rand_t@ object to be used like a heap-allocated
-- @flint_rand_t@ in external libraries. The random state is not
-- initialised.
foreign import ccall "flint.h flint_rand_alloc"
  flint_rand_alloc :: IO (Ptr CFRandState)

-- | /flint_rand_free/ /state/ 
-- 
-- Frees a random state object as allocated using @flint_rand_alloc@.
foreign import ccall "flint.h flint_rand_free"
  flint_rand_free :: Ptr CFRandState -> IO ()

-- | /flint_randinit/ /state/ 
-- 
-- Initialize a @flint_rand_t@.
foreign import ccall "flint.h flint_randinit"
  flint_randinit :: Ptr CFRandState -> IO ()

-- | /flint_randclear/ /state/ 
-- 
-- Free all memory allocated by @flint_rand_init@.
foreign import ccall "flint.h flint_randclear"
  flint_randclear :: Ptr CFRandState -> IO ()

foreign import ccall "flint.h &flint_randclear"
  p_flint_randclear :: FunPtr (Ptr CFRandState -> IO ())

-- Thread functions ------------------------------------------------------------

-- | /flint_set_num_threads/ /num_threads/ 
-- 
-- Set up a thread pool of @num_threads - 1@ worker threads (in addition to
-- the master thread) and set the maximum number of worker threads the
-- master thread can start to @num_threads - 1@.
-- 
-- This function may only be called globally from the master thread. It can
-- also be called at a global level to change the size of the thread pool,
-- but an exception is raised if the thread pool is in use (threads have
-- been woken but not given back). The function cannot be called from
-- inside worker threads.
foreign import ccall "flint.h flint_set_num_threads"
  flint_set_num_threads :: CInt -> IO ()

-- | /flint_get_num_threads/ 
-- 
-- When called at the global level, this function returns one more than the
-- number of worker threads in the Flint thread pool, i.e. it counts the
-- workers in the thread pool plus one more for the master thread.
-- 
-- In general, this function returns one more than the number of additional
-- worker threads that can be started by the current thread.
-- 
-- Use @thread_pool_wake@ to set this number for a given worker thread.
foreign import ccall "flint.h flint_get_num_threads"
  flint_get_num_threads :: IO ()

-- | /flint_set_num_workers/ /num_workers/ 
-- 
-- Restricts the number of worker threads that can be started by the
-- current thread to @num_workers@. This function can be called from any
-- thread.
-- 
-- Assumes that the Flint thread pool is already set up.
-- 
-- The function returns the old number of worker threads that can be
-- started.
-- 
-- The function can only be used to reduce the number of workers that can
-- be started from a thread. It cannot be used to increase the number. If a
-- higher number is passed, the function has no effect.
-- 
-- The number of workers must be restored to the original value by a call
-- to @flint_reset_num_workers@ before the thread is returned to the thread
-- pool.
-- 
-- The main use of this function and @flint_reset_num_workers@ is to
-- cheaply and temporarily restrict the number of workers that can be
-- started, e.g. by a function that one wishes to call from a thread, and
-- cheaply restore the number of workers to its original value before
-- exiting the current thread.
foreign import ccall "flint.h flint_set_num_workers"
  flint_set_num_workers :: CInt -> IO CInt

-- | /flint_reset_num_workers/ /num_workers/ 
-- 
-- After a call to @flint_set_num_workers@ this function must be called to
-- set the number of workers that may be started by the current thread back
-- to its original value.
foreign import ccall "flint.h flint_reset_num_workers"
  flint_reset_num_workers :: CInt -> IO ()

