module Data.Number.Flint.Partitions.FFI (
  -- * Computation of the partition function
    partitions_rademacher_bound
  , partitions_hrr_sum_arb
  , partitions_fmpz_fmpz
  , partitions_fmpz_ui
  -- , partitions_fmpz_ui_using_doubles
  , partitions_leading_fmpz
) where 

-- Computation of the partition function ---------------------------------------

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.C.Types

import Data.Number.Flint.Fmpz

import Data.Number.Flint.Arb.Types
import Data.Number.Flint.Acb.Types

--------------------------------------------------------------------------------

-- | /partitions_rademacher_bound/ /b/ /n/ /N/ 
-- 
-- Sets \(b\) to an upper bound for
-- 
-- \[M(n,N) = \frac{44 \pi^2}{225 \sqrt 3} N^{-1/2}
--           + \frac{\pi \sqrt{2}}{75} \left( \frac{N}{n-1} \right)^{1/2}
--         \sinh\left(\frac{\pi}{N} \sqrt{\frac{2n}{3}}\right).\]
-- 
-- This formula gives an upper bound for the truncation error in the
-- Hardy-Ramanujan-Rademacher formula when the series is taken up to the
-- term \(t(n,N)\) inclusive.
foreign import ccall "partitions.h partitions_rademacher_bound"
  partitions_rademacher_bound :: Ptr CArf -> Ptr CFmpz -> CULong -> IO ()

-- | /partitions_hrr_sum_arb/ /x/ /n/ /N0/ /N/ /use_doubles/ 
-- 
-- Evaluates the partial sum \(\sum_{k=N_0}^N t(n,k)\) of the
-- Hardy-Ramanujan-Rademacher series.
-- 
-- If /use_doubles/ is nonzero, doubles and the system\'s standard library
-- math functions are used to evaluate the smallest terms. This
-- significantly speeds up evaluation for small \(n\) (e.g. \(n < 10^6\)),
-- and gives a small speed improvement for larger \(n\), but the result is
-- not guaranteed to be correct. In practice, the error is estimated very
-- conservatively, and unless the system\'s standard library is broken, use
-- of doubles can be considered safe. Setting /use_doubles/ to zero gives a
-- fully guaranteed bound.
foreign import ccall "partitions.h partitions_hrr_sum_arb"
  partitions_hrr_sum_arb :: Ptr CArb -> Ptr CFmpz -> CLong -> CLong -> CInt -> IO ()

-- | /partitions_fmpz_fmpz/ /p/ /n/ /use_doubles/ 
-- 
-- Computes the partition function \(p(n)\) using the
-- Hardy-Ramanujan-Rademacher formula. This function computes a numerical
-- ball containing \(p(n)\) and verifies that the ball contains a unique
-- integer.
-- 
-- If /n/ is sufficiently large and a number of threads greater than 1 has
-- been selected with @flint_set_num_threads()@, the computation time will
-- be reduced by using two threads.
-- 
-- See @partitions_hrr_sum_arb@ for an explanation of the /use_doubles/
-- option.
foreign import ccall "partitions.h partitions_fmpz_fmpz"
  partitions_fmpz_fmpz :: Ptr CFmpz -> Ptr CFmpz -> CInt -> IO ()

-- | /partitions_fmpz_ui/ /p/ /n/ 
-- 
-- Computes the partition function \(p(n)\) using the
-- Hardy-Ramanujan-Rademacher formula. This function computes a numerical
-- ball containing \(p(n)\) and verifies that the ball contains a unique
-- integer.
foreign import ccall "partitions.h partitions_fmpz_ui"
  partitions_fmpz_ui :: Ptr CFmpz -> CULong -> IO ()

-- -- | /partitions_fmpz_ui_using_doubles/ /p/ /n/ 
-- -- 
-- -- Computes the partition function \(p(n)\), enabling the use of doubles
-- -- internally. This significantly speeds up evaluation for small \(n\)
-- -- (e.g. \(n < 10^6\)), but the error bounds are not certified (see remarks
-- -- for @partitions_hrr_sum_arb@).
-- foreign import ccall "partitions.h partitions_fmpz_ui_using_doubles"
--   partitions_fmpz_ui_using_doubles :: Ptr CFmpz -> CULong -> IO ()

-- | /partitions_leading_fmpz/ /res/ /n/ /prec/ 
-- 
-- Sets /res/ to the leading term in the Hardy-Ramanujan series for
-- \(p(n)\) (without Rademacher\'s correction of this term, which is
-- vanishingly small when \(n\) is large), that is,
-- \(\sqrt{12} (1-1/t) e^t / (24n-1)\) where \(t = \pi \sqrt{24n-1} / 6\).
foreign import ccall "partitions.h partitions_leading_fmpz"
  partitions_leading_fmpz :: Ptr CArb -> Ptr CFmpz -> CLong -> IO ()

