
module Data.Number.Flint.Hypgeom.FFI (
  -- * Support for hypergeometric series
  -- * Types
    Hypgeom (..)
  , CHypgeom (..)
  , withHypgeom
  , withNewHypgeom
  -- * Memory management
  , hypgeom_init
  , hypgeom_clear
  -- * Error bounding
  , hypgeom_estimate_terms
  , hypgeom_bound
  , hypgeom_precompute
  -- * Summation
  , arb_hypgeom_sum
  , arb_hypgeom_infsum
) where

-- Support for hypergeometric series -------------------------------------------

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.Storable
import Foreign.C.Types

import Data.Number.Flint.Flint
import Data.Number.Flint.Arb.Types

#include <flint/hypgeom.h>

-- Types -----------------------------------------------------------------------

data Hypgeom = Hypgeom {-# UNPACK #-} !(ForeignPtr CHypgeom)
type CHypgeom = CFlint Hypgeom

instance Storable CHypgeom where
  sizeOf    _ = #{size      hypgeom_t}
  alignment _ = #{alignment hypgeom_t}
  peek = undefined
  poke = undefined

newHypgeom = do
  x <- mallocForeignPtr
  withForeignPtr x hypgeom_init
  addForeignPtrFinalizer p_hypgeom_clear x
  return $ Hypgeom x

withHypgeom (Hypgeom p) f = do
  withForeignPtr p $ \fp -> (Hypgeom p,) <$> f fp

withNewHypgeom f = do
  x <- newHypgeom
  withHypgeom x f
  
-- Memory management -----------------------------------------------------------

-- | /hypgeom_init/ /hyp/ 
--
foreign import ccall "hypgeom.h hypgeom_init"
  hypgeom_init :: Ptr CHypgeom -> IO ()

-- | /hypgeom_clear/ /hyp/ 
--
foreign import ccall "hypgeom.h hypgeom_clear"
  hypgeom_clear :: Ptr CHypgeom -> IO ()

foreign import ccall "hypgeom.h &hypgeom_clear"
  p_hypgeom_clear :: FunPtr (Ptr CHypgeom -> IO ())

-- Error bounding --------------------------------------------------------------

-- | /hypgeom_estimate_terms/ /z/ /r/ /d/ 
--
-- Computes an approximation of the largest \(n\) such that
-- \(|z|^n/(n!)^r = 2^{-d}\), giving a first-order estimate of the number
-- of terms needed to approximate the sum of a hypergeometric series of
-- weight \(r \ge 0\) and argument \(z\) to an absolute precision of
-- \(d \ge 0\) bits. If \(r = 0\), the direct solution of the equation is
-- given by \(n = (\log(1-z) - d \log 2) / \log z\). If \(r > 0\), using
-- \(\log n! \approx n \log n - n\) gives an equation that can be solved in
-- terms of the Lambert /W/-function as \(n = (d \log 2) / (r\,W\!(t))\)
-- where \(t = (d \log 2) / (e r z^{1/r})\).
-- 
-- The evaluation is done using double precision arithmetic. The function
-- aborts if the computed value of \(n\) is greater than or equal to
-- LONG_MAX \/ 2.
foreign import ccall "hypgeom.h hypgeom_estimate_terms"
  hypgeom_estimate_terms :: Ptr CMag -> CInt -> CLong -> IO CLong

-- | /hypgeom_bound/ /error/ /r/ /C/ /D/ /K/ /TK/ /z/ /prec/ 
--
-- Computes a truncation parameter sufficient to achieve /prec/ bits of
-- absolute accuracy, according to the strategy described above. The input
-- consists of \(r\), \(C\), \(D\), \(K\), precomputed bound for \(T(K)\),
-- and \(\tilde z = z (a_p / b_q)\), such that for \(k > K\), the
-- hypergeometric term ratio is bounded by
-- 
-- \[`\]
-- \[\frac{\tilde z}{k^r} \frac{k(k-D)}{(k-C)(k-2D)}.\]
-- 
-- Given this information, we compute a \(\varepsilon\) and an integer
-- \(n\) such that
-- \(\left| \sum_{k=n}^{\infty} T(k) \right| \le \varepsilon \le 2^{-\mathrm{prec}}\).
-- The output variable /error/ is set to the value of \(\varepsilon\), and
-- \(n\) is returned.
foreign import ccall "hypgeom.h hypgeom_bound"
  hypgeom_bound :: Ptr CMag -> CInt -> CLong -> CLong -> CLong -> Ptr CMag -> Ptr CMag -> CLong -> IO CLong

-- | /hypgeom_precompute/ /hyp/ 
--
-- Precomputes the bounds data \(C\), \(D\), \(K\) and an upper bound for
-- \(T(K)\).
foreign import ccall "hypgeom.h hypgeom_precompute"
  hypgeom_precompute :: Ptr CHypgeom -> IO ()

-- Summation -------------------------------------------------------------------

-- | /arb_hypgeom_sum/ /P/ /Q/ /hyp/ /n/ /prec/ 
--
-- Computes \(P, Q\) such that \(P / Q = \sum_{k=0}^{n-1} T(k)\) where
-- \(T(k)\) is defined by /hyp/, using binary splitting and a working
-- precision of /prec/ bits.
foreign import ccall "hypgeom.h arb_hypgeom_sum"
  arb_hypgeom_sum :: Ptr CArb -> Ptr CArb -> Ptr CHypgeom -> CLong -> CLong -> IO ()

-- | /arb_hypgeom_infsum/ /P/ /Q/ /hyp/ /tol/ /prec/ 
--
-- Computes \(P, Q\) such that \(P / Q = \sum_{k=0}^{\infty} T(k)\) where
-- \(T(k)\) is defined by /hyp/, using binary splitting and working
-- precision of /prec/ bits. The number of terms is chosen automatically to
-- bound the truncation error by at most \(2^{-\mathrm{tol}}\). The bound
-- for the truncation error is included in the output as part of /P/.
foreign import ccall "hypgeom.h arb_hypgeom_infsum"
  arb_hypgeom_infsum :: Ptr CArb -> Ptr CArb -> Ptr CHypgeom -> CLong -> CLong -> IO ()

