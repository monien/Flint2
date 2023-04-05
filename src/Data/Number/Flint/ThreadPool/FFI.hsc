{-# language
    TupleSections
  , TypeSynonymInstances
  , FlexibleInstances
#-}

module Data.Number.Flint.ThreadPool.FFI (
  -- * Thread pool
    ThreadPool (..)
  , CThreadPool (..)
  , ThreadPoolHandle (..)
  , CThreadPoolHandle (..)
  -- * Thread pool functions
  , thread_pool_init
  , thread_pool_get_size
  , thread_pool_set_size
  , thread_pool_request
  , thread_pool_wake
  , thread_pool_wait
  , thread_pool_give_back
  , thread_pool_clear
) where

-- thread pool -----------------------------------------------------------------

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr )
import Foreign.Storable
import Foreign.Marshal ( free )

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpq

#include <flint/flint.h>
#include <flint/thread_pool.h>

-- thread_pool_t ---------------------------------------------------------------

data ThreadPool = ThreadPool {-# UNPACK #-} !(ForeignPtr CThreadPool)
type CThreadPool = CFlint ThreadPool

instance Storable CThreadPool where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size thread_pool_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment thread_pool_t}
  peek = undefined
  poke = undefined

newThreadPool size = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> thread_pool_init x size
  addForeignPtrFinalizer p_thread_pool_clear x
  return $ ThreadPool x

{-# INLINE withThreadPool #-}
withThreadPool (ThreadPool x) f = do
  withForeignPtr x $ \px -> f px >>= return . (ThreadPool x,)

-- thread_pool_handle_t --------------------------------------------------------

data ThreadPoolHandle = ThreadPoolHandle {-# UNPACK #-} !(ForeignPtr CThreadPoolHandle)
type CThreadPoolHandle = CFlint ThreadPoolHandle

-- Thread pool -----------------------------------------------------------------

-- | /thread_pool_init/ /T/ /size/ 
-- 
-- Initialise @T@ and create @size@ sleeping threads that are available to
-- work. If @size \\le 0@ no threads are created and future calls to
-- @thread_pool_request@ will return \(0\) (unless @thread_pool_set_size@
-- has been called).
foreign import ccall "flint/thread_pool.h thread_pool_init"
  thread_pool_init :: Ptr CThreadPool -> CLong -> IO ()

-- | /thread_pool_get_size/ /T/ 
-- 
-- Return the number of threads in @T@.
foreign import ccall "flint/thread_pool.h thread_pool_get_size"
  thread_pool_get_size :: Ptr CThreadPool -> IO CLong

-- | /thread_pool_set_size/ /T/ /new_size/ 
-- 
-- If all threads in @T@ are in the available state, resize @T@ and return
-- 1. Otherwise, return @0@.
foreign import ccall "flint/thread_pool.h thread_pool_set_size"
  thread_pool_set_size :: Ptr CThreadPool -> CLong -> IO CInt

-- | /thread_pool_request/ /T/ /out/ /requested/ 
-- 
-- Put at most @requested@ threads in the unavailable state and return
-- their handles. The handles are written to @out@ and the number of
-- handles written is returned. These threads must be released by a call to
-- @thread_pool_give_back@.
foreign import ccall "flint/thread_pool.h thread_pool_request"
  thread_pool_request :: Ptr CThreadPool -> Ptr CThreadPoolHandle -> CLong -> IO CLong

-- | /thread_pool_wake/ /T/ /i/ /max_workers/ /f/ /a/ 
-- 
-- Wake up a sleeping thread @i@ and have it work on @f(a)@. The thread
-- being woken will be allowed to start @max_workers@ additional worker
-- threads. Usually this value should be set to @0@.
foreign import ccall "flint/thread_pool.h thread_pool_wake"
  thread_pool_wake :: Ptr CThreadPool -> Ptr CThreadPoolHandle -> CInt -> FunPtr (Ptr () -> IO ())  -> Ptr () -> IO ()

-- | /thread_pool_wait/ /T/ /i/ 
-- 
-- Wait for thread @i@ to finish working and go back to sleep.
foreign import ccall "flint/thread_pool.h thread_pool_wait"
  thread_pool_wait :: Ptr CThreadPool -> Ptr CThreadPoolHandle -> IO ()

-- | /thread_pool_give_back/ /T/ /i/ 
-- 
-- Put thread @i@ back in the available state. This thread should be
-- sleeping when this function is called.
foreign import ccall "flint/thread_pool.h thread_pool_give_back"
  thread_pool_give_back :: Ptr CThreadPool -> Ptr CThreadPoolHandle -> IO ()

-- | /thread_pool_clear/ /T/ 
-- 
-- Release any resources used by @T@. All threads should be given back
-- before this function is called.
foreign import ccall "flint/thread_pool.h thread_pool_clear"
  thread_pool_clear :: Ptr CThreadPool -> IO ()

foreign import ccall "flint/thread_pool.h &thread_pool_clear"
  p_thread_pool_clear :: FunPtr (Ptr CThreadPool -> IO ())

