{-# language
    CApiFFI
  , FlexibleInstances
  , ForeignFunctionInterface
  , MultiParamTypeClasses
  , TupleSections
  , TypeFamilies
  #-}

module Data.Number.Flint.Acb.DFT.FFI (
  -- * Discrete Fourier transform
  -- DFTAlgorithms
  -- * Main DFT functions
  -- | If \(G=\mathbb Z/n\mathbb Z\), we compute the DFT according to the usual
  -- convention
  --
  -- \[w_x = \sum_{y\bmod n} v_y e^{-\frac{2i \pi}nxy}\]
  --
    acb_dft
  , acb_dft_inverse
  -- * DFT Precomputation
  , AcbDftPre (..)
  , CAcbDftPre (..)
  , newAcbDftPre
  , withAcbDftPre
  , withNewAcbDftPre
  -- *
  , acb_dft_precomp_init
  , acb_dft_precomp_clear
  , acb_dft_precomp
  , acb_dft_inverse_precomp
  -- -- * DFT on products
  -- -- $Products
  -- , AcbDftProd (..)
  -- , CAcbDftProd (..)
  -- , newAcbDftProd
  -- , withAcbDftProd
  -- , withNewAcbDftProd
  -- -- *
  -- -- , acb_dirichlet_dft_prod
  -- , acb_dft_prod_init
  -- , acb_dft_prod_clear
  -- , acb_dirichlet_dft_prod_precomp
  -- * Convolution
  , acb_dft_convol_naive
  , acb_dft_convol_rad2
  , acb_dft_convol
  -- * FFT algorithms
  -- -- * Naive algorithm
  -- , AcbDftNaive (..)
  -- , CAcbDftNaive (..)
  -- , newAcbDftNaive
  -- , withAcbDftNaive
  -- , withNewAcbDftNaive
  -- -- *
  -- , acb_dft_naive
  -- , acb_dft_naive_init
  -- , acb_dft_naive_clear
  -- , acb_dft_naive_precomp
  -- * CRT decomposition
  , AcbDftCrt (..)
  , CAcbDftCrt (..)
  , newAcbDftCrt
  , withAcbDftCrt
  , withNewAcbDftCrt
  -- *
  , acb_dft_crt
  , acb_dft_crt_init
  , acb_dft_crt_clear
  , acb_dft_crt_precomp
  -- -- * Cooley-Tukey decomposition
  -- , AcbDftCyc (..)
  -- , CAcbDftCyc (..)
  -- , newAcbDftCyc
  -- , withAcbDftCyc
  -- , withNewAcbDftCyc
  -- -- *
  -- , acb_dft_cyc
  -- , acb_dft_cyc_init
  -- , acb_dft_cyc_clear
  -- , acb_dft_cyc_precomp
  -- * Radix 2 decomposition
  -- , AcbDftRad2 (..)
  -- , CAcbDftRad2 (..)
  -- , newAcbDftRad2
  -- , withAcbDftRad2
  -- , withNewAcbDftRad2
  -- -- *
  -- , acb_dft_rad2
  -- , acb_dft_inverse_rad2
  -- , acb_dft_rad2_init
  -- , acb_dft_rad2_clear
  -- , acb_dft_rad2_precomp
  -- * Bluestein transform
  -- , AcbDftBluestein (..)
  -- , CAcbDftBluestein (..)
  -- , newAcbDftBluestein
  -- , withAcbDftBluestein
  -- , withNewAcbDftBluestein
  -- -- *
  -- , acb_dft_bluestein
  -- , acb_dft_bluestein_init
  -- , acb_dft_bluestein_clear
  -- , acb_dft_bluestein_precomp
) where

-- Discrete Fourier transform --------------------------------------------------

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.C.Types
import Foreign.C.String
import Foreign.Storable
import Foreign.Marshal.Alloc (free)
import Foreign.Marshal.Array (advancePtr)

import Data.Typeable

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpq

import Data.Number.Flint.Arb.Types
import Data.Number.Flint.Acb.Types

#include <flint/acb.h>
#include <flint/acb_dft.h>
  
-- Main DFT functions ----------------------------------------------------------


-- | /acb_dft/ /w/ /v/ /n/ /prec/ 
--
-- Set /w/ to the DFT of /v/ of length /len/, using an automatic choice of
-- algorithm.
foreign import ccall "acb_dft.h acb_dft"
  acb_dft :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /acb_dft_inverse/ /w/ /v/ /n/ /prec/ 
--
-- Compute the inverse DFT of /v/ into /w/.
foreign import ccall "acb_dft.h acb_dft_inverse"
  acb_dft_inverse :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

-- acb_dft_pre -----------------------------------------------------------------

data AcbDftPre = AcbDftPre {-# UNPACK #-} !(ForeignPtr CAcbDftPre)
type CAcbDftPre = CFlint AcbDftPre

instance Storable CAcbDftPre where
  sizeOf _ = #{size acb_dft_pre_t}
  alignment _ = #{alignment acb_dft_pre_t}
  peek = undefined
  poke = undefined

newAcbDftPre len prec = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> do
    acb_dft_precomp_init x len prec
  addForeignPtrFinalizer p_acb_dft_precomp_clear x
  return $ AcbDftPre x

withAcbDftPre (AcbDftPre p) f = do
  withForeignPtr p $ \fp -> (AcbDftPre p,) <$> f fp

withNewAcbDftPre len prec f = do
  x <- newAcbDftPre len prec
  withAcbDftPre x f

--------------------------------------------------------------------------------

-- | /acb_dft_precomp_init/ /pre/ /len/ /prec/ 
--
-- Initializes the fast DFT scheme of length /len/, using an automatic
-- choice of algorithms depending on the factorization of /len/.
-- 
-- The length /len/ is stored as /pre->n/.
--
-- If several computations are to be done on the same group, the FFT scheme
-- should be reused.
--
foreign import ccall "acb_dft.h acb_dft_precomp_init"
  acb_dft_precomp_init :: Ptr CAcbDftPre -> CLong -> CLong -> IO ()

-- | /acb_dft_precomp_clear/ /pre/ 
--
-- Clears /pre/.
foreign import ccall "acb_dft.h acb_dft_precomp_clear"
  acb_dft_precomp_clear :: Ptr CAcbDftPre -> IO ()

foreign import ccall "acb_dft.h &acb_dft_precomp_clear"
  p_acb_dft_precomp_clear :: FunPtr (Ptr CAcbDftPre -> IO ())

-- | /acb_dft_precomp/ /w/ /v/ /pre/ /prec/ 
--
-- Computes the DFT of the sequence /v/ into /w/ by applying the
-- precomputed scheme /pre/. Both /v/ and /w/ must have length /pre->n/.
foreign import ccall "acb_dft.h acb_dft_precomp"
  acb_dft_precomp :: Ptr CAcb -> Ptr CAcb -> Ptr CAcbDftPre -> CLong -> IO ()

-- | /acb_dft_inverse_precomp/ /w/ /v/ /pre/ /prec/ 
--
-- Compute the inverse DFT of /v/ into /w/.
foreign import ccall "acb_dft.h acb_dft_inverse_precomp"
  acb_dft_inverse_precomp :: Ptr CAcb -> Ptr CAcb -> Ptr CAcbDftPre -> CLong -> IO ()

-- -- DFT on products -------------------------------------------------------------

-- data AcbDftProd = AcbDftProd {-# UNPACK #-} !(ForeignPtr CAcbDftProd)
-- type CAcbDftProd = CFlint AcbDftProd

-- instance Storable CAcbDftProd where
--   sizeOf _ = #{size acb_dft_prod_t}
--   alignment _ = #{alignment acb_dft_prod_t}
--   peek = undefined
--   poke = undefined

-- newAcbDftProd cyc num prec = do
--   x <- mallocForeignPtr
--   withForeignPtr x $ \x -> do
--     acb_dft_prod_init x cyc num prec
--   addForeignPtrFinalizer p_acb_dft_prod_clear x
--   return $ AcbDftProd x

-- withAcbDftProd (AcbDftProd p) f = do
--   withForeignPtr p $ \fp -> (AcbDftProd p,) <$> f fp

-- withNewAcbDftProd cyc num prec f = do
--   x <- newAcbDftProd cyc num prec
--   withAcbDftProd x f

-- --------------------------------------------------------------------------------

-- -- $Products
-- --
-- -- A finite abelian group is isomorphic to a product of cyclic components
-- --
-- -- \[G = \bigoplus_{i=1}^r \mathbb Z/n_i\mathbb Z\]
-- --
-- -- Characters are product of component characters and the DFT reads
-- --
-- -- \[\hat f(x_1,\dots x_r) = \sum_{y_1\dots y_r} f(y_1,\dots y_r)
-- -- e^{-2i \pi \sum\frac{x_i y_i}{n_i}}\]
-- --
-- -- We assume that \(f\) is given by a vector of length \(\prod n_i\)
-- -- corresponding to a lexicographic ordering of the values
-- -- \(y_1,\dots y_r\), and the computation returns the same indexing for
-- -- values of \(\hat f\).
-- --

-- -- -- | /acb_dirichlet_dft_prod/ /w/ /v/ /cyc/ /num/ /prec/ 
-- -- --
-- -- -- Computes the DFT on the group product of /num/ cyclic components of
-- -- -- sizes /cyc/. Assume the entries of /v/ are indexed according to
-- -- -- lexicographic ordering of the cyclic components.
-- -- foreign import ccall "acb_dft.h acb_dirichlet_dft_prod"
-- --   acb_dirichlet_dft_prod :: Ptr CAcb -> Ptr CAcb -> Ptr CLong -> CLong -> CLong -> IO ()

-- -- | /acb_dft_prod_init/ /t/ /cyc/ /num/ /prec/ 
-- --
-- -- Stores in /t/ a DFT scheme for the product of /num/ cyclic components
-- -- whose sizes are given in the array /cyc/.
-- foreign import ccall "acb_dft.h acb_dft_prod_init"
--   acb_dft_prod_init :: Ptr CAcbDftProd -> Ptr CLong -> CLong -> CLong -> IO ()

-- -- | /acb_dft_prod_clear/ /t/ 
-- --
-- -- Clears /t/.
-- foreign import ccall "acb_dft.h acb_dft_prod_clear"
--   acb_dft_prod_clear :: Ptr CAcbDftProd -> IO ()

-- foreign import ccall "acb_dft.h &acb_dft_prod_clear"
--   p_acb_dft_prod_clear :: FunPtr (Ptr CAcbDftProd -> IO ())

-- -- | /acb_dirichlet_dft_prod_precomp/ /w/ /v/ /prod/ /prec/ 
-- --
-- -- Sets /w/ to the DFT of /v/. Assume the entries are lexicographically
-- -- ordered according to the product of cyclic groups initialized in /t/.
-- foreign import ccall "acb_dft.h acb_dirichlet_dft_prod_precomp"
--   acb_dirichlet_dft_prod_precomp :: Ptr CAcb -> Ptr CAcb -> Ptr CAcbDftProd -> CLong -> IO ()

-- Convolution -----------------------------------------------------------------

-- For functions \(f\) and \(g\) on \(G\) we consider the convolution
--
-- \[(f \star g)(x) = \sum_{y\in G} f(x-y)g(y)\]
--
-- | /acb_dft_convol_naive/ /w/ /f/ /g/ /len/ /prec/ 
--
foreign import ccall "acb_dft.h acb_dft_convol_naive"
  acb_dft_convol_naive :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /acb_dft_convol_rad2/ /w/ /f/ /g/ /len/ /prec/ 
--
foreign import ccall "acb_dft.h acb_dft_convol_rad2"
  acb_dft_convol_rad2 :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /acb_dft_convol/ /w/ /f/ /g/ /len/ /prec/ 
--
-- Sets /w/ to the convolution of /f/ and /g/ of length /len/.
-- 
-- The /naive/ version simply uses the definition.
-- 
-- The /rad2/ version embeds the sequence into a power of 2 length and uses
-- the formula
-- 
-- \[\widehat{f \star g}(\chi) = \hat f(\chi)\hat g(\chi)\]
-- 
-- to compute it using three radix 2 FFT.
-- 
-- The default version uses radix 2 FFT unless /len/ is a product of small
-- primes where a non padded FFT is faster.
foreign import ccall "acb_dft.h acb_dft_convol"
  acb_dft_convol :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

-- -- FFT algorithms --------------------------------------------------------------

-- -- $FFTAlgorithms
-- --
-- -- Fast Fourier transform techniques allow to compute efficiently all
-- -- values \(\hat f(\chi)\) by reusing common computations.
-- --
-- -- Specifically, if \(H\triangleleft G\) is a subgroup of size \(M\) and
-- -- index [G:H]=m, then writing \(f_x(h)=f(xh)\) the translate of \(f\) by
-- -- representatives x of \(G/H\), one has a decomposition
-- --
-- -- \[\hat f(\chi) = \sum_{x\in G/H} \overline{\chi(x)} \hat{f_x}(\chi_{H})\]
-- --
-- -- so that the DFT on \(G\) can be computed using \(m\) DFT on \(H\) (of
-- -- appropriate translates of \(f\)), then \(M\) DFT on \(G/H\), one for
-- -- each restriction \(\chi_{H}\).
-- --
-- -- This decomposition can be done recursively.
-- --

-- -- Naive algorithm -------------------------------------------------------------

-- data AcbDftNaive = AcbDftNaive {-# UNPACK #-} !(ForeignPtr CAcbDftNaive)
-- type CAcbDftNaive = CFlint AcbDftNaive

-- instance Storable CAcbDftNaive where
--   sizeOf _ = #{size acb_dft_naive_t}
--   alignment _ = #{alignment acb_dft_naive_t}
--   peek = undefined
--   poke = undefined

-- newAcbDftNaive len prec = do
--   x <- mallocForeignPtr
--   withForeignPtr x $ \x -> do
--     acb_dft_naive_init x len prec
--   addForeignPtrFinalizer p_acb_dft_naive_clear x
--   return $ AcbDftNaive x

-- withAcbDftNaive (AcbDftNaive p) f = do
--   withForeignPtr p $ \fp -> (AcbDftNaive p,) <$> f fp

-- withNewAcbDftNaive len prec f = do
--   x <- newAcbDftNaive len prec
--   withAcbDftNaive x f

-- --------------------------------------------------------------------------------

-- -- | /acb_dft_naive/ /w/ /v/ /n/ /prec/ 
-- --
-- -- Computes the DFT of /v/ into /w/, where /v/ and /w/ have size /n/, using
-- -- the naive \(O(n^2)\) algorithm.
-- foreign import ccall "acb_dft.h acb_dft_naive"
--   acb_dft_naive :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

-- -- | /acb_dft_naive_init/ /t/ /len/ /prec/ 
-- --
-- foreign import ccall "acb_dft.h acb_dft_naive_init"
--   acb_dft_naive_init :: Ptr CAcbDftNaive -> CLong -> CLong -> IO ()

-- -- | /acb_dft_naive_clear/ /t/ 
-- --
-- -- Stores a table of roots of unity in /t/. The length /len/ is stored as
-- -- /t->n/.
-- foreign import ccall "acb_dft.h acb_dft_naive_clear"
--   acb_dft_naive_clear :: Ptr CAcbDftNaive -> IO ()

-- foreign import ccall "acb_dft.h &acb_dft_naive_clear"
--   p_acb_dft_naive_clear :: FunPtr (Ptr CAcbDftNaive -> IO ())

-- -- | /acb_dft_naive_precomp/ /w/ /v/ /t/ /prec/ 
-- --
-- -- Sets /w/ to the DFT of /v/ of size /t->n/, using the naive algorithm
-- -- data /t/.
-- foreign import ccall "acb_dft.h acb_dft_naive_precomp"
--   acb_dft_naive_precomp :: Ptr CAcb -> Ptr CAcb -> Ptr CAcbDftNaive -> CLong -> IO ()

-- CRT decomposition -----------------------------------------------------------

data AcbDftCrt = AcbDftCrt {-# UNPACK #-} !(ForeignPtr CAcbDftCrt)
type CAcbDftCrt = CFlint AcbDftCrt

instance Storable CAcbDftCrt where
  sizeOf _ = #{size acb_dft_crt_t}
  alignment _ = #{alignment acb_dft_crt_t}
  peek = undefined
  poke = undefined

newAcbDftCrt len prec = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> do
    acb_dft_crt_init x len prec
  addForeignPtrFinalizer p_acb_dft_crt_clear x
  return $ AcbDftCrt x

withAcbDftCrt (AcbDftCrt p) f = do
  withForeignPtr p $ \fp -> (AcbDftCrt p,) <$> f fp

withNewAcbDftCrt len prec f = do
  x <- newAcbDftCrt len prec
  withAcbDftCrt x f

--------------------------------------------------------------------------------

-- | /acb_dft_crt/ /w/ /v/ /n/ /prec/ 
--
-- Computes the DFT of /v/ into /w/, where /v/ and /w/ have size /len/,
-- using CRT to express \(\mathbb Z/n\mathbb Z\) as a product of cyclic
-- groups.
foreign import ccall "acb_dft.h acb_dft_crt"
  acb_dft_crt :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /acb_dft_crt_init/ /t/ /len/ /prec/ 
--
foreign import ccall "acb_dft.h acb_dft_crt_init"
  acb_dft_crt_init :: Ptr CAcbDftCrt -> CLong -> CLong -> IO ()

-- | /acb_dft_crt_clear/ /t/ 
--
-- Initialize a CRT decomposition of \(\mathbb Z/n\mathbb Z\) as a direct
-- product of cyclic groups. The length /len/ is stored as /t->n/.
foreign import ccall "acb_dft.h acb_dft_crt_clear"
  acb_dft_crt_clear :: Ptr CAcbDftCrt -> IO ()

foreign import ccall "acb_dft.h &acb_dft_crt_clear"
  p_acb_dft_crt_clear :: FunPtr (Ptr CAcbDftCrt -> IO ())

-- | /acb_dft_crt_precomp/ /w/ /v/ /t/ /prec/ 
--
-- Sets /w/ to the DFT of /v/ of size /t->n/, using the CRT decomposition
-- scheme /t/.
foreign import ccall "acb_dft.h acb_dft_crt_precomp"
  acb_dft_crt_precomp :: Ptr CAcb -> Ptr CAcb -> Ptr CAcbDftCrt -> CLong -> IO ()

-- -- Cooley-Tukey decomposition --------------------------------------------------

-- data AcbDftCyc = AcbDftCyc {-# UNPACK #-} !(ForeignPtr CAcbDftCyc)
-- type CAcbDftCyc = CFlint AcbDftCyc

-- instance Storable CAcbDftCyc where
--   sizeOf _ = #{size acb_dft_cyc_t}
--   alignment _ = #{alignment acb_dft_cyc_t}
--   peek = undefined
--   poke = undefined

-- newAcbDftCyc len prec = do
--   x <- mallocForeignPtr
--   withForeignPtr x $ \x -> do
--     acb_dft_cyc_init x len prec
--   addForeignPtrFinalizer p_acb_dft_cyc_clear x
--   return $ AcbDftCyc x

-- withAcbDftCyc (AcbDftCyc p) f = do
--   withForeignPtr p $ \fp -> (AcbDftCyc p,) <$> f fp

-- withNewAcbDftCyc len prec f = do
--   x <- newAcbDftCyc len prec
--   withAcbDftCyc x f

-- --------------------------------------------------------------------------------

-- -- | /acb_dft_cyc/ /w/ /v/ /n/ /prec/ 
-- --
-- -- Computes the DFT of /v/ into /w/, where /v/ and /w/ have size /n/, using
-- -- each prime factor of \(m\) of \(n\) to decompose with the subgroup
-- -- \(H=m\mathbb Z/n\mathbb Z\).
-- foreign import ccall "acb_dft.h acb_dft_cyc"
--   acb_dft_cyc :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

-- -- | /acb_dft_cyc_init/ /t/ /len/ /prec/ 
-- --
-- foreign import ccall "acb_dft.h acb_dft_cyc_init"
--   acb_dft_cyc_init :: Ptr CAcbDftCyc -> CLong -> CLong -> IO ()

-- -- | /acb_dft_cyc_clear/ /t/ 
-- --
-- -- Initialize a decomposition of \(\mathbb Z/n\mathbb Z\) into cyclic
-- -- subgroups. The length /len/ is stored as /t->n/.
-- foreign import ccall "acb_dft.h acb_dft_cyc_clear"
--   acb_dft_cyc_clear :: Ptr CAcbDftCyc -> IO ()

-- foreign import ccall "acb_dft.h &acb_dft_cyc_clear"
--   p_acb_dft_cyc_clear :: FunPtr (Ptr CAcbDftCyc -> IO ())

-- -- | /acb_dft_cyc_precomp/ /w/ /v/ /t/ /prec/ 
-- --
-- -- Sets /w/ to the DFT of /v/ of size /t->n/, using the cyclic
-- -- decomposition scheme /t/.
-- foreign import ccall "acb_dft.h acb_dft_cyc_precomp"
--   acb_dft_cyc_precomp :: Ptr CAcb -> Ptr CAcb -> Ptr CAcbDftCyc -> CLong -> IO ()

-- -- Radix 2 decomposition -------------------------------------------------------

-- data AcbDftRad2 = AcbDftRad2 {-# UNPACK #-} !(ForeignPtr CAcbDftRad2)
-- type CAcbDftRad2 = CFlint AcbDftRad2

-- instance Storable CAcbDftRad2 where
--   sizeOf _ = #{size acb_dft_rad2_t}
--   alignment _ = #{alignment acb_dft_rad2_t}
--   peek = undefined
--   poke = undefined

-- newAcbDftRad2 len prec = do
--   x <- mallocForeignPtr
--   withForeignPtr x $ \x -> do
--     acb_dft_rad2_init x len prec
--   addForeignPtrFinalizer p_acb_dft_rad2_clear x
--   return $ AcbDftRad2 x

-- withAcbDftRad2 (AcbDftRad2 p) f = do
--   withForeignPtr p $ \fp -> (AcbDftRad2 p,) <$> f fp

-- withNewAcbDftRad2 len prec f = do
--   x <- newAcbDftRad2 len prec
--   withAcbDftRad2 x f

-- --------------------------------------------------------------------------------

-- -- | /acb_dft_rad2/ /w/ /v/ /e/ /prec/ 
-- --
-- -- Computes the DFT of /v/ into /w/, where /v/ and /w/ have size \(2^e\),
-- -- using a radix 2 FFT.
-- foreign import ccall "acb_dft.h acb_dft_rad2"
--   acb_dft_rad2 :: Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- -- | /acb_dft_inverse_rad2/ /w/ /v/ /e/ /prec/ 
-- --
-- -- Computes the inverse DFT of /v/ into /w/, where /v/ and /w/ have size
-- -- \(2^e\), using a radix 2 FFT.
-- foreign import ccall "acb_dft.h acb_dft_inverse_rad2"
--   acb_dft_inverse_rad2 :: Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- -- | /acb_dft_rad2_init/ /t/ /e/ /prec/ 
-- --
-- foreign import ccall "acb_dft.h acb_dft_rad2_init"
--   acb_dft_rad2_init :: Ptr CAcbDftRad2 -> CInt -> CLong -> IO ()

-- -- | /acb_dft_rad2_clear/ /t/ 
-- --
-- -- Initialize and clear a radix 2 FFT of size \(2^e\), stored as /t->n/.
-- foreign import ccall "acb_dft.h acb_dft_rad2_clear"
--   acb_dft_rad2_clear :: Ptr CAcbDftRad2 -> IO ()

-- foreign import ccall "acb_dft.h &acb_dft_rad2_clear"
--   p_acb_dft_rad2_clear :: FunPtr (Ptr CAcbDftRad2 -> IO ())

-- -- | /acb_dft_rad2_precomp/ /w/ /v/ /t/ /prec/ 
-- --
-- -- Sets /w/ to the DFT of /v/ of size /t->n/, using the precomputed radix 2
-- -- scheme /t/.
-- foreign import ccall "acb_dft.h acb_dft_rad2_precomp"
--   acb_dft_rad2_precomp :: Ptr CAcb -> Ptr CAcb -> Ptr CAcbDftRad2 -> CLong -> IO ()

-- -- Bluestein transform ---------------------------------------------------------

-- data AcbDftBluestein = AcbDftBluestein {-# UNPACK #-} !(ForeignPtr CAcbDftBluestein)
-- type CAcbDftBluestein = CFlint AcbDftBluestein

-- instance Storable CAcbDftBluestein where
--   sizeOf _ = #{size acb_dft_bluestein_t}
--   alignment _ = #{alignment acb_dft_bluestein_t}
--   peek = undefined
--   poke = undefined

-- newAcbDftBluestein len prec = do
--   x <- mallocForeignPtr
--   withForeignPtr x $ \x -> do
--     acb_dft_bluestein_init x len prec
--   addForeignPtrFinalizer p_acb_dft_bluestein_clear x
--   return $ AcbDftBluestein x

-- withAcbDftBluestein (AcbDftBluestein p) f = do
--   withForeignPtr p $ \fp -> (AcbDftBluestein p,) <$> f fp

-- withNewAcbDftBluestein len prec f = do
--   x <- newAcbDftBluestein len prec
--   withAcbDftBluestein x f

-- --------------------------------------------------------------------------------

-- -- | /acb_dft_bluestein/ /w/ /v/ /n/ /prec/ 
-- --
-- -- Computes the DFT of /v/ into /w/, where /v/ and /w/ have size /n/, by
-- -- conversion to a radix 2 one using Bluestein\'s convolution trick.
-- foreign import ccall "acb_dft.h acb_dft_bluestein"
--   acb_dft_bluestein :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

-- -- | /acb_dft_bluestein_init/ /t/ /len/ /prec/ 
-- --
-- foreign import ccall "acb_dft.h acb_dft_bluestein_init"
--   acb_dft_bluestein_init :: Ptr CAcbDftBluestein -> CLong -> CLong -> IO ()

-- -- | /acb_dft_bluestein_clear/ /t/ 
-- --
-- -- Initialize and clear a Bluestein scheme to compute DFT of size /len/.
-- foreign import ccall "acb_dft.h acb_dft_bluestein_clear"
--   acb_dft_bluestein_clear :: Ptr CAcbDftBluestein -> IO ()

-- foreign import ccall "acb_dft.h &acb_dft_bluestein_clear"
--   p_acb_dft_bluestein_clear :: FunPtr (Ptr CAcbDftBluestein -> IO ())

-- -- | /acb_dft_bluestein_precomp/ /w/ /v/ /t/ /prec/ 
-- --
-- -- Sets /w/ to the DFT of /v/ of size /t->n/, using the precomputed
-- -- Bluestein scheme /t/.
-- foreign import ccall "acb_dft.h acb_dft_bluestein_precomp"
--   acb_dft_bluestein_precomp :: Ptr CAcb -> Ptr CAcb -> Ptr CAcbDftBluestein -> CLong -> IO ()

