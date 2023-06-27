{-# language
    CApiFFI
  , FlexibleInstances
  , ForeignFunctionInterface
  , MultiParamTypeClasses
  , TupleSections
  , TypeFamilies
  #-}

module Data.Number.Flint.APRCL.FFI (
  -- * APRCL primality testing
    APRCLConfig (..)
  , CAPRCLConfig (..)
  , newAPRCLConfigGauss
  , newAPRCLConfigJacobi
  , withAPRCLConfig
  -- * Primality test functions
  , aprcl_is_prime
  , aprcl_is_prime_jacobi
  , aprcl_is_prime_gauss
  , _aprcl_is_prime_jacobi
  , _aprcl_is_prime_gauss
  , aprcl_is_prime_gauss_min_R
  , aprcl_is_prime_final_division
  -- * Configuration functions
  , aprcl_config_gauss_init
  , aprcl_config_gauss_init_min_R
  , aprcl_config_gauss_clear
  , aprcl_R_value
  , aprcl_config_jacobi_init
  , aprcl_config_jacobi_clear
  -- * Cyclotomic arithmetic
  , UnityZp (..)
  , CUnityZp (..)
  , newUnityZp
  , withUnityZp
  , UnityZpq (..)
  , CUnityZpq (..)
  , newUnityZpq
  , withUnityZpq
  -- * Memory management
  , unity_zp_init
  , unity_zp_clear
  , unity_zp_copy
  , unity_zp_swap
  , unity_zp_set_zero
  -- * Comparison
  , unity_zp_is_unity
  , unity_zp_equal
  -- * Output
  , unity_zp_print
  -- * Coefficient management
  , unity_zp_coeff_set_fmpz
  , unity_zp_coeff_set_ui
  , unity_zp_coeff_add_fmpz
  , unity_zp_coeff_add_ui
  , unity_zp_coeff_inc
  , unity_zp_coeff_dec
  -- * Scalar multiplication
  , unity_zp_mul_scalar_fmpz
  , unity_zp_mul_scalar_ui
  -- * Addition and multiplication
  , unity_zp_add
  , unity_zp_mul
  , unity_zp_sqr
  , unity_zp_mul_inplace
  , unity_zp_sqr_inplace
  -- * Powering functions
  , unity_zp_pow_fmpz
  , unity_zp_pow_ui
  , _unity_zp_pow_select_k
  , unity_zp_pow_2k_fmpz
  , unity_zp_pow_2k_ui
  , unity_zp_pow_sliding_fmpz
  -- * Cyclotomic reduction
  , _unity_zp_reduce_cyclotomic_divmod
  , _unity_zp_reduce_cyclotomic
  , unity_zp_reduce_cyclotomic
  -- * Automorphism and inverse
  , unity_zp_aut
  , unity_zp_aut_inv
  -- * Jacobi sum
  , unity_zp_jacobi_sum_pq
  , unity_zp_jacobi_sum_2q_one
  , unity_zp_jacobi_sum_2q_two
  -- * Extended rings
  , unity_zpq_init
  , unity_zpq_clear
  , unity_zpq_copy
  , unity_zpq_swap
  , unity_zpq_equal
  , unity_zpq_p_unity
  , unity_zpq_is_p_unity
  , unity_zpq_is_p_unity_generator
  , unity_zpq_coeff_set_fmpz
  , unity_zpq_coeff_set_ui
  , unity_zpq_coeff_add
  , unity_zpq_add
  , unity_zpq_mul
  , _unity_zpq_mul_unity_p
  , unity_zpq_mul_unity_p_pow
  , unity_zpq_pow
  , unity_zpq_pow_ui
  , unity_zpq_gauss_sum
  , unity_zpq_gauss_sum_sigma_pow
) where

-- APRCL primality testing -----------------------------------------------------

import Control.Monad

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr )
import Foreign.Storable
import Foreign.Marshal ( free )

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Mod
import Data.Number.Flint.Fmpz.Mod.Poly
import Data.Number.Flint.Support.ULong.Extras

#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/aprcl.h>

-- aprcl_config ----------------------------------------------------------------

data APRCLConfig =
    Gauss  {-# UNPACK #-} !(ForeignPtr CAPRCLConfig)
  | Jacobi {-# UNPACK #-} !(ForeignPtr CAPRCLConfig)
  
data CAPRCLConfig = CAPRCLConfig CULong
                                 (Ptr CFmpz)
                                 (Ptr CNFactor)
                                 (Ptr CFmpz)
                                 (Ptr CInt)
  
instance Storable CAPRCLConfig where
  {-# INLINE sizeOf #-}
  sizeOf    _ = #{size      aprcl_config}
  {-# INLINE alignment #-}
  alignment _ = #{alignment aprcl_config}
  peek = undefined
  poke = undefined

newAPRCLConfigGauss n = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x ->
    withFmpz n $ \n ->
      aprcl_config_gauss_init x n
  addForeignPtrFinalizer p_aprcl_config_gauss_clear x
  return $ Gauss x

newAPRCLConfigJacobi n = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x ->
    withFmpz n $ \n ->
      aprcl_config_jacobi_init x n
  addForeignPtrFinalizer p_aprcl_config_jacobi_clear x
  return $ Jacobi x

withAPRCLConfig (Gauss x) f = do
  withForeignPtr x $ \px -> f px >>= return . (Gauss x,)

withAPRCLConfig (Jacobi x) f = do
  withForeignPtr x $ \px -> f px >>= return . (Jacobi x,)

-- primality_test_status -------------------------------------------------------

newtype PrimalityTestStatus =
  PrimalityTestStatus { _PrimalityTestStatus :: CInt } deriving Eq

instance Show PrimalityTestStatus where
  show status
    | status == unknown    = "UNKNOWN"
    | status == prime      = "PRIME"
    | status == composite  = "COMPOSITE"
    | status == probaprime = "PROBABPRIME"
    | otherwise = "unknown PrimalityTestStatus."

unknown    = PrimalityTestStatus #const UNKNOWN
prime      = PrimalityTestStatus #const PRIME
composite  = PrimalityTestStatus #const COMPOSITE
probaprime = PrimalityTestStatus #const PROBABPRIME

-- Primality test functions ----------------------------------------------------

-- | /aprcl_is_prime/ /n/ 
--
-- Tests \(n\) for primality using the APRCL test. This is the same as
-- @aprcl_is_prime_jacobi@.
foreign import ccall "aprcl.h aprcl_is_prime"
  aprcl_is_prime :: Ptr CFmpz -> IO CInt

-- | /aprcl_is_prime_jacobi/ /n/ 
--
-- If \(n\) is prime returns 1; otherwise returns 0. The algorithm is well
-- described in \"Implementation of a New Primality Test\" by H. Cohen and
-- A.K. Lenstra and \"A Course in Computational Algebraic Number Theory\"
-- by H. Cohen.
-- 
-- It is theoretically possible that this function fails to prove that
-- \(n\) is prime. In this event, @flint_abort@ is called. To handle this
-- condition, the @_aprcl_is_prime_jacobi@ function can be used.
foreign import ccall "aprcl.h aprcl_is_prime_jacobi"
  aprcl_is_prime_jacobi :: Ptr CFmpz -> IO CInt

-- | /aprcl_is_prime_gauss/ /n/ 
--
-- If \(n\) is prime returns 1; otherwise returns 0. Uses the cyclotomic
-- primality testing algorithm described in \"Four primality testing
-- algorithms\" by Rene Schoof. The minimum required numbers \(s\) and
-- \(R\) are computed automatically.
-- 
-- By default \(R \ge 180\). In some cases this function fails to prove
-- that \(n\) is prime. This means that we select a too small \(R\) value.
-- In this event, @flint_abort@ is called. To handle this condition, the
-- @_aprcl_is_prime_jacobi@ function can be used.
foreign import ccall "aprcl.h aprcl_is_prime_gauss"
  aprcl_is_prime_gauss :: Ptr CFmpz -> IO CInt

-- | /_aprcl_is_prime_jacobi/ /n/ /config/ 
--
-- Jacobi sum test for \(n\). Possible return values: @PRIME@, @COMPOSITE@
-- and @UNKNOWN@ (if we cannot prove primality).
foreign import ccall "aprcl.h _aprcl_is_prime_jacobi"
  _aprcl_is_prime_jacobi :: Ptr CFmpz -> Ptr CAPRCLConfig -> IO PrimalityTestStatus

-- | /_aprcl_is_prime_gauss/ /n/ /config/ 
--
-- Tests \(n\) for primality with fixed @config@. Possible return values:
-- @PRIME@, @COMPOSITE@ and @PROBABPRIME@ (if we cannot prove primality).
foreign import ccall "aprcl.h _aprcl_is_prime_gauss"
  _aprcl_is_prime_gauss :: Ptr CFmpz -> Ptr CAPRCLConfig -> IO PrimalityTestStatus

-- | /aprcl_is_prime_gauss_min_R/ /n/ /R/ 
--
-- Same as @aprcl_is_prime_gauss@ with fixed minimum value of \(R\).
foreign import ccall "aprcl.h aprcl_is_prime_gauss_min_R"
  aprcl_is_prime_gauss_min_R :: Ptr CFmpz -> CULong -> IO ()

-- | /aprcl_is_prime_final_division/ /n/ /s/ /r/ 
--
-- Returns 0 if for some \(a = n^k \bmod s\), where \(k \in [1, r - 1]\),
-- we have that \(a \mid n\); otherwise returns 1.
foreign import ccall "aprcl.h aprcl_is_prime_final_division"
  aprcl_is_prime_final_division :: Ptr CFmpz -> Ptr CFmpz -> CULong -> IO CInt

-- Configuration functions -----------------------------------------------------

-- | /aprcl_config_gauss_init/ /conf/ /n/ 
--
-- Computes the \(s\) and \(R\) values used in the cyclotomic primality
-- test, \(s^2 > n\) and
-- \(s=\prod\limits_{\substack{q-1\mid R \\ q \text{ prime}}}q\). Also
-- stores factors of \(R\) and \(s\).
foreign import ccall "aprcl.h aprcl_config_gauss_init"
  aprcl_config_gauss_init :: Ptr CAPRCLConfig -> Ptr CFmpz -> IO ()

-- | /aprcl_config_gauss_init_min_R/ /conf/ /n/ /R/ 
--
-- Computes the \(s\) with fixed minimum \(R\) such that
-- \(a^R \equiv 1 \mod{s}\) for all integers \(a\) coprime to \(s\).
foreign import ccall "aprcl.h aprcl_config_gauss_init_min_R"
  aprcl_config_gauss_init_min_R :: Ptr CAPRCLConfig -> Ptr CFmpz -> CULong -> IO ()

-- | /aprcl_config_gauss_clear/ /conf/ 
--
-- Clears the given @aprcl_config@ element. It must be reinitialised in
-- order to be used again.
foreign import ccall "aprcl.h aprcl_config_gauss_clear"
  aprcl_config_gauss_clear :: Ptr CAPRCLConfig -> IO ()

foreign import ccall "aprcl.h &aprcl_config_gauss_clear"
  p_aprcl_config_gauss_clear :: FunPtr (Ptr CAPRCLConfig -> IO ())

-- | /aprcl_R_value/ /n/ 
--
-- Returns a precomputed \(R\) value for APRCL, such that the corresponding
-- \(s\) value is greater than \(\sqrt{n}\). The maximum stored value
-- \(6983776800\) allows to test numbers up to \(6000\) digits.
foreign import ccall "aprcl.h aprcl_R_value"
  aprcl_R_value :: Ptr CFmpz -> IO CULong

-- | /aprcl_config_jacobi_init/ /conf/ /n/ 
--
-- Computes the \(s\) and \(R\) values used in the cyclotomic primality
-- test, \(s^2 > n\) and \(a^R \equiv 1 \mod{s}\) for all \(a\) coprime to
-- \(s\). Also stores factors of \(R\) and \(s\).
foreign import ccall "aprcl.h aprcl_config_jacobi_init"
  aprcl_config_jacobi_init :: Ptr CAPRCLConfig -> Ptr CFmpz -> IO ()

-- | /aprcl_config_jacobi_clear/ /conf/ 
--
-- Clears the given @aprcl_config@ element. It must be reinitialised in
-- order to be used again.
foreign import ccall "aprcl.h aprcl_config_jacobi_clear"
  aprcl_config_jacobi_clear :: Ptr CAPRCLConfig -> IO ()

foreign import ccall "aprcl.h &aprcl_config_jacobi_clear"
  p_aprcl_config_jacobi_clear :: FunPtr (Ptr CAPRCLConfig -> IO ())

-- Cyclotomic arithmetic -------------------------------------------------------

-- unity_zpq -------------------------------------------------------------------

data UnityZpq = UnityZpq {-# UNPACK #-} !(ForeignPtr CUnityZpq)
type CUnityZpq = CFlint UnityZpq

instance Storable CUnityZpq where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size unity_zpq}
  {-# INLINE alignment #-}
  alignment _ = #{alignment unity_zpq}
  peek = undefined
  poke = undefined

newUnityZpq q p n = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> 
    withFmpz n $ \n -> 
      unity_zpq_init x q p n
  addForeignPtrFinalizer p_unity_zpq_clear x
  return $ UnityZpq x

{-# INLINE withUnityZpq #-}
withUnityZpq (UnityZpq x) f = do
  withForeignPtr x $ \px -> f px >>= return . (UnityZpq x,)

-- unity_zp --------------------------------------------------------------------

data UnityZp = UnityZp {-# UNPACK #-} !(ForeignPtr CUnityZp )
data CUnityZp = CUnityZp (Ptr CFmpzModPoly) CULong CULong (Ptr CFmpzModCtx)

instance Storable CUnityZp where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size unity_zp}
  {-# INLINE alignment #-}
  alignment _ = #{alignment unity_zp}
  peek ptr = CUnityZp
    <$> #{peek _unity_zp, poly} ptr
    <*> #{peek _unity_zp, p   } ptr
    <*> #{peek _unity_zp, exp } ptr
    <*> #{peek _unity_zp, ctx } ptr
  poke = undefined

newUnityZp p exp n = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x ->
    withFmpz n $ \n -> 
    unity_zp_init x p exp n
  addForeignPtrFinalizer p_unity_zp_clear x
  return $ UnityZp x

{-# INLINE withUnityZp #-}
withUnityZp (UnityZp x) f = do
  withForeignPtr x $ \px -> f px >>= return . (UnityZp x,)
  
-- Memory management -----------------------------------------------------------

-- | /unity_zp_init/ /f/ /p/ /exp/ /n/ 
--
-- Initializes \(f\) as an element of \(\mathbb{Z}[\zeta_{p^{exp}}]/(n)\).
foreign import ccall "aprcl.h unity_zp_init"
  unity_zp_init :: Ptr CUnityZp -> CULong -> CULong -> Ptr CFmpz -> IO ()

-- | /unity_zp_clear/ /f/ 
--
-- Clears the given element. It must be reinitialised in order to be used
-- again.
foreign import ccall "aprcl.h unity_zp_clear"
  unity_zp_clear :: Ptr CUnityZp -> IO ()

foreign import ccall "aprcl.h &unity_zp_clear"
  p_unity_zp_clear :: FunPtr (Ptr CUnityZp -> IO ())

-- | /unity_zp_copy/ /f/ /g/ 
--
-- Sets \(f\) to \(g\). \(f\) and \(g\) must be initialized with same \(p\)
-- and \(n\).
foreign import ccall "aprcl.h unity_zp_copy"
  unity_zp_copy :: Ptr CUnityZp -> Ptr CUnityZp -> IO ()

-- | /unity_zp_swap/ /f/ /q/ 
--
-- Swaps \(f\) and \(g\). \(f\) and \(g\) must be initialized with same
-- \(p\) and \(n\).
foreign import ccall "aprcl.h unity_zp_swap"
  unity_zp_swap :: Ptr CUnityZp -> Ptr CUnityZp -> IO ()

-- | /unity_zp_set_zero/ /f/ 
--
-- Sets \(f\) to zero.
foreign import ccall "aprcl.h unity_zp_set_zero"
  unity_zp_set_zero :: Ptr CUnityZp -> IO ()

-- Comparison ------------------------------------------------------------------

-- | /unity_zp_is_unity/ /f/ 
--
-- If \(f = \zeta^h\) returns h; otherwise returns -1.
foreign import ccall "aprcl.h unity_zp_is_unity"
  unity_zp_is_unity :: Ptr CUnityZp -> IO CLong

-- | /unity_zp_equal/ /f/ /g/ 
--
-- Returns nonzero if \(f = g\) reduced by the \(p^{exp}\)-th cyclotomic
-- polynomial.
foreign import ccall "aprcl.h unity_zp_equal"
  unity_zp_equal :: Ptr CUnityZp -> Ptr CUnityZp -> IO CInt

-- Output ----------------------------------------------------------------------

foreign import ccall "aprcl.h unity_zp_get_str"
  unity_zp_get_str :: Ptr CUnityZp -> IO CString
  
-- | /unity_zp_print/ /f/ 
--
-- Prints the contents of the \(f\).
unity_zp_print :: Ptr CUnityZp -> IO ()
unity_zp_print z = do
  printCStr unity_zp_get_str z
  return ()
  
-- Coefficient management ------------------------------------------------------

-- | /unity_zp_coeff_set_fmpz/ /f/ /ind/ /x/ 
foreign import ccall "aprcl.h unity_zp_coeff_set_fmpz"
  unity_zp_coeff_set_fmpz :: Ptr CUnityZp -> CULong -> Ptr CFmpz -> IO ()
-- | /unity_zp_coeff_set_ui/ /f/ /ind/ /x/ 
--
-- Sets the coefficient of \(\zeta^{ind}\) to \(x\). \(ind\) must be less
-- than \(p^{exp}\).
foreign import ccall "aprcl.h unity_zp_coeff_set_ui"
  unity_zp_coeff_set_ui :: Ptr CUnityZp -> CULong -> CULong -> IO ()

-- | /unity_zp_coeff_add_fmpz/ /f/ /ind/ /x/ 
foreign import ccall "aprcl.h unity_zp_coeff_add_fmpz"
  unity_zp_coeff_add_fmpz :: Ptr CUnityZp -> CULong -> Ptr CFmpz -> IO ()
-- | /unity_zp_coeff_add_ui/ /f/ /ind/ /x/ 
--
-- Adds \(x\) to the coefficient of \(\zeta^{ind}\). \(x\) must be less
-- than \(n\). \(ind\) must be less than \(p^{exp}\).
foreign import ccall "aprcl.h unity_zp_coeff_add_ui"
  unity_zp_coeff_add_ui :: Ptr CUnityZp -> CULong -> CULong -> IO ()

-- | /unity_zp_coeff_inc/ /f/ /ind/ 
--
-- Increments the coefficient of \(\zeta^{ind}\). \(ind\) must be less than
-- \(p^{exp}\).
foreign import ccall "aprcl.h unity_zp_coeff_inc"
  unity_zp_coeff_inc :: Ptr CUnityZp -> CULong -> IO ()

-- | /unity_zp_coeff_dec/ /f/ /ind/ 
--
-- Decrements the coefficient of \(\zeta^{ind}\). \(ind\) must be less than
-- \(p^{exp}\).
foreign import ccall "aprcl.h unity_zp_coeff_dec"
  unity_zp_coeff_dec :: Ptr CUnityZp -> CULong -> IO ()

-- Scalar multiplication -------------------------------------------------------

-- | /unity_zp_mul_scalar_fmpz/ /f/ /g/ /s/ 
--
-- Sets \(f\) to \(s \cdot g\). \(f\) and \(g\) must be initialized with
-- same \(p\), \(exp\) and \(n\).
foreign import ccall "aprcl.h unity_zp_mul_scalar_fmpz"
  unity_zp_mul_scalar_fmpz :: Ptr CUnityZp -> Ptr CUnityZp -> Ptr CFmpz -> IO ()

-- | /unity_zp_mul_scalar_ui/ /f/ /g/ /s/ 
--
-- Sets \(f\) to \(s \cdot g\). \(f\) and \(g\) must be initialized with
-- same \(p\), \(exp\) and \(n\).
foreign import ccall "aprcl.h unity_zp_mul_scalar_ui"
  unity_zp_mul_scalar_ui :: Ptr CUnityZp -> Ptr CUnityZp -> CULong -> IO ()

-- Addition and multiplication -------------------------------------------------

-- | /unity_zp_add/ /f/ /g/ /h/ 
--
-- Sets \(f\) to \(g + h\). \(f\), \(g\) and \(h\) must be initialized with
-- same \(p\), \(exp\) and \(n\).
foreign import ccall "aprcl.h unity_zp_add"
  unity_zp_add :: Ptr CUnityZp -> Ptr CUnityZp -> Ptr CUnityZp -> IO ()

-- | /unity_zp_mul/ /f/ /g/ /h/ 
--
-- Sets \(f\) to \(g \cdot h\). \(f\), \(g\) and \(h\) must be initialized
-- with same \(p\), \(exp\) and \(n\).
foreign import ccall "aprcl.h unity_zp_mul"
  unity_zp_mul :: Ptr CUnityZp -> Ptr CUnityZp -> Ptr CUnityZp -> IO ()

-- | /unity_zp_sqr/ /f/ /g/ 
--
-- Sets \(f\) to \(g \cdot g\). \(f\), \(g\) and \(h\) must be initialized
-- with same \(p\), \(exp\) and \(n\).
foreign import ccall "aprcl.h unity_zp_sqr"
  unity_zp_sqr :: Ptr CUnityZp -> Ptr CUnityZp -> IO ()

-- | /unity_zp_mul_inplace/ /f/ /g/ /h/ /t/ 
--
-- Sets \(f\) to \(g \cdot h\). If \(p^{exp} = 3, 4, 5, 7, 8, 9, 11, 16\)
-- special multiplication functions are used. The preallocated array \(t\)
-- of @fmpz_t@ is used for all computations in this case. \(f\), \(g\) and
-- \(h\) must be initialized with same \(p\), \(exp\) and \(n\).
foreign import ccall "aprcl.h unity_zp_mul_inplace"
  unity_zp_mul_inplace :: Ptr CUnityZp -> Ptr CUnityZp -> Ptr CUnityZp -> Ptr (Ptr CFmpz) -> IO ()

-- | /unity_zp_sqr_inplace/ /f/ /g/ /t/ 
--
-- Sets \(f\) to \(g \cdot g\). If \(p^{exp} = 3, 4, 5, 7, 8, 9, 11, 16\)
-- special multiplication functions are used. The preallocated array \(t\)
-- of @fmpz_t@ is used for all computations in this case. \(f\) and \(g\)
-- must be initialized with same \(p\), \(exp\) and \(n\).
foreign import ccall "aprcl.h unity_zp_sqr_inplace"
  unity_zp_sqr_inplace :: Ptr CUnityZp -> Ptr CUnityZp -> Ptr (Ptr CFmpz) -> IO ()

-- Powering functions ----------------------------------------------------------

-- | /unity_zp_pow_fmpz/ /f/ /g/ /pow/ 
--
-- Sets \(f\) to \(g^{pow}\). \(f\) and \(g\) must be initialized with same
-- \(p\), \(exp\) and \(n\).
foreign import ccall "aprcl.h unity_zp_pow_fmpz"
  unity_zp_pow_fmpz :: Ptr CUnityZp -> Ptr CUnityZp -> Ptr CFmpz -> IO ()

-- | /unity_zp_pow_ui/ /f/ /g/ /pow/ 
--
-- Sets \(f\) to \(g^{pow}\). \(f\) and \(g\) must be initialized with same
-- \(p\), \(exp\) and \(n\).
foreign import ccall "aprcl.h unity_zp_pow_ui"
  unity_zp_pow_ui :: Ptr CUnityZp -> Ptr CUnityZp -> CULong -> IO ()

-- | /_unity_zp_pow_select_k/ /n/ 
--
-- Returns the smallest integer \(k\) satisfying
-- \(\log (n) < (k(k + 1)2^{2k}) / (2^{k + 1} - k - 2) + 1\)
foreign import ccall "aprcl.h _unity_zp_pow_select_k"
  _unity_zp_pow_select_k :: Ptr CFmpz -> IO CULong

-- | /unity_zp_pow_2k_fmpz/ /f/ /g/ /pow/ 
--
-- Sets \(f\) to \(g^{pow}\) using the \(2^k\)-ary exponentiation method.
-- \(f\) and \(g\) must be initialized with same \(p\), \(exp\) and \(n\).
foreign import ccall "aprcl.h unity_zp_pow_2k_fmpz"
  unity_zp_pow_2k_fmpz :: Ptr CUnityZp -> Ptr CUnityZp -> Ptr CFmpz -> IO ()

-- | /unity_zp_pow_2k_ui/ /f/ /g/ /pow/ 
--
-- Sets \(f\) to \(g^{pow}\) using the \(2^k\)-ary exponentiation method.
-- \(f\) and \(g\) must be initialized with same \(p\), \(exp\) and \(n\).
foreign import ccall "aprcl.h unity_zp_pow_2k_ui"
  unity_zp_pow_2k_ui :: Ptr CUnityZp -> Ptr CUnityZp -> CULong -> IO ()

-- | /unity_zp_pow_sliding_fmpz/ /f/ /g/ /pow/ 
--
-- Sets \(f\) to \(g^{pow}\) using the sliding window exponentiation
-- method. \(f\) and \(g\) must be initialized with same \(p\), \(exp\) and
-- \(n\).
foreign import ccall "aprcl.h unity_zp_pow_sliding_fmpz"
  unity_zp_pow_sliding_fmpz :: Ptr CUnityZp -> Ptr CUnityZp -> Ptr CFmpz -> IO ()

-- Cyclotomic reduction --------------------------------------------------------

-- | /_unity_zp_reduce_cyclotomic_divmod/ /f/ 
foreign import ccall "aprcl.h _unity_zp_reduce_cyclotomic_divmod"
  _unity_zp_reduce_cyclotomic_divmod :: Ptr CUnityZp -> IO ()
-- | /_unity_zp_reduce_cyclotomic/ /f/ 
--
-- Sets \(f = f \bmod \Phi_{p^{exp}}\). \(\Phi_{p^{exp}}\) is the
-- \(p^{exp}\)-th cyclotomic polynomial. \(g\) must be reduced by
-- \(x^{p^{exp}}-1\) poly. \(f\) and \(g\) must be initialized with same
-- \(p\), \(exp\) and \(n\).
foreign import ccall "aprcl.h _unity_zp_reduce_cyclotomic"
  _unity_zp_reduce_cyclotomic :: Ptr CUnityZp -> IO ()

-- | /unity_zp_reduce_cyclotomic/ /f/ /g/ 
--
-- Sets \(f = g \bmod \Phi_{p^{exp}}\). \(\Phi_{p^{exp}}\) is the
-- \(p^{exp}\)-th cyclotomic polynomial.
foreign import ccall "aprcl.h unity_zp_reduce_cyclotomic"
  unity_zp_reduce_cyclotomic :: Ptr CUnityZp -> Ptr CUnityZp -> IO ()

-- Automorphism and inverse ----------------------------------------------------

-- | /unity_zp_aut/ /f/ /g/ /x/ 
--
-- Sets \(f = \sigma_x(g)\), the automorphism \(\sigma_x(\zeta)=\zeta^x\).
-- \(f\) and \(g\) must be initialized with the same \(p\), \(exp\) and
-- \(n\).
foreign import ccall "aprcl.h unity_zp_aut"
  unity_zp_aut :: Ptr CUnityZp -> Ptr CUnityZp -> CULong -> IO ()

-- | /unity_zp_aut_inv/ /f/ /g/ /x/ 
--
-- Sets \(f = \sigma_x^{-1}(g)\), so \(\sigma_x(f) = g\). \(g\) must be
-- reduced by \(\Phi_{p^{exp}}\). \(f\) and \(g\) must be initialized with
-- the same \(p\), \(exp\) and \(n\).
foreign import ccall "aprcl.h unity_zp_aut_inv"
  unity_zp_aut_inv :: Ptr CUnityZp -> Ptr CUnityZp -> CULong -> IO ()

-- Jacobi sum ------------------------------------------------------------------

-- Here \(\chi_{p, q}\) is the character defined by chi_{p, q}(g^x) =
-- zeta_{p^k}^x, where \(g\) is a primitive root modulo \(q\).
--
-- | /unity_zp_jacobi_sum_pq/ /f/ /q/ /p/ 
--
-- Sets \(f\) to the Jacobi sum \(J(p, q) = j(\chi_{p, q}, \chi_{p, q})\).
foreign import ccall "aprcl.h unity_zp_jacobi_sum_pq"
  unity_zp_jacobi_sum_pq :: Ptr CUnityZp -> CULong -> CULong -> IO ()

-- | /unity_zp_jacobi_sum_2q_one/ /f/ /q/ 
--
-- Sets \(f\) to the Jacobi sum
-- \(J_2(q) = j(\chi_{2, q}^{2^{k - 3}}, \chi_{2, q}^{3 \cdot 2^{k - 3}}))^2\).
foreign import ccall "aprcl.h unity_zp_jacobi_sum_2q_one"
  unity_zp_jacobi_sum_2q_one :: Ptr CUnityZp -> CULong -> IO ()

-- | /unity_zp_jacobi_sum_2q_two/ /f/ /q/ 
--
-- Sets \(f\) to the Jacobi sum
-- \(J_3(1) = j(\chi_{2, q}, \chi_{2, q}, \chi_{2, q}) =
-- J(2, q) \cdot j(\chi_{2, q}^2, \chi_{2, q})\).
foreign import ccall "aprcl.h unity_zp_jacobi_sum_2q_two"
  unity_zp_jacobi_sum_2q_two :: Ptr CUnityZp -> CULong -> IO ()

-- Extended rings --------------------------------------------------------------

-- | /unity_zpq_init/ /f/ /q/ /p/ /n/ 
--
-- Initializes \(f\) as an element of \(\mathbb{Z}[\zeta_q, \zeta_p]/(n)\).
foreign import ccall "aprcl.h unity_zpq_init"
  unity_zpq_init :: Ptr CUnityZpq -> CULong -> CULong -> Ptr CFmpz -> IO ()

-- | /unity_zpq_clear/ /f/ 
--
-- Clears the given element. It must be reinitialized in order to be used
-- again.
foreign import ccall "aprcl.h unity_zpq_clear"
  unity_zpq_clear :: Ptr CUnityZpq -> IO ()

foreign import ccall "aprcl.h &unity_zpq_clear"
  p_unity_zpq_clear :: FunPtr (Ptr CUnityZpq -> IO ())

-- | /unity_zpq_copy/ /f/ /g/ 
--
-- Sets \(f\) to \(g\). \(f\) and \(g\) must be initialized with same
-- \(p\), \(q\) and \(n\).
foreign import ccall "aprcl.h unity_zpq_copy"
  unity_zpq_copy :: Ptr CUnityZpq ->Ptr CUnityZpq -> IO ()

-- | /unity_zpq_swap/ /f/ /q/ 
--
-- Swaps \(f\) and \(g\). \(f\) and \(g\) must be initialized with same
-- \(p\), \(q\) and \(n\).
foreign import ccall "aprcl.h unity_zpq_swap"
  unity_zpq_swap :: Ptr CUnityZpq ->Ptr CUnityZpq -> IO ()

-- | /unity_zpq_equal/ /f/ /g/ 
--
-- Returns nonzero if \(f = g\).
foreign import ccall "aprcl.h unity_zpq_equal"
  unity_zpq_equal :: Ptr CUnityZpq ->Ptr CUnityZpq -> IO CInt

-- | /unity_zpq_p_unity/ /f/ 
--
-- If \(f = \zeta_p^x\) returns \(x \in [0, p - 1]\); otherwise returns
-- \(p\).
foreign import ccall "aprcl.h unity_zpq_p_unity"
  unity_zpq_p_unity :: Ptr CUnityZpq -> IO CULong

-- | /unity_zpq_is_p_unity/ /f/ 
--
-- Returns nonzero if \(f = \zeta_p^x\).
foreign import ccall "aprcl.h unity_zpq_is_p_unity"
  unity_zpq_is_p_unity :: Ptr CUnityZpq -> IO CInt

-- | /unity_zpq_is_p_unity_generator/ /f/ 
--
-- Returns nonzero if \(f\) is a generator of the cyclic group
-- \(\langle\zeta_p\rangle\).
foreign import ccall "aprcl.h unity_zpq_is_p_unity_generator"
  unity_zpq_is_p_unity_generator :: Ptr CUnityZpq -> IO CInt

-- | /unity_zpq_coeff_set_fmpz/ /f/ /i/ /j/ /x/ 
--
-- Sets the coefficient of \(\zeta_q^i \zeta_p^j\) to \(x\). \(i\) must be
-- less than \(q\) and \(j\) must be less than \(p\).
foreign import ccall "aprcl.h unity_zpq_coeff_set_fmpz"
  unity_zpq_coeff_set_fmpz :: Ptr CUnityZpq -> CULong -> CULong -> Ptr CFmpz -> IO ()

-- | /unity_zpq_coeff_set_ui/ /f/ /i/ /j/ /x/ 
--
-- Sets the coefficient of \(\zeta_q^i \zeta_p^j\) to \(x\). \(i\) must be
-- less than \(q\) and \(j\) must be less then \(p\).
foreign import ccall "aprcl.h unity_zpq_coeff_set_ui"
  unity_zpq_coeff_set_ui :: Ptr CUnityZpq -> CULong -> CULong -> CULong -> IO ()

-- | /unity_zpq_coeff_add/ /f/ /i/ /j/ /x/ 
--
-- Adds \(x\) to the coefficient of \(\zeta_p^i \zeta_q^j\). \(x\) must be
-- less than \(n\).
foreign import ccall "aprcl.h unity_zpq_coeff_add"
  unity_zpq_coeff_add :: Ptr CUnityZpq -> CULong -> CULong -> Ptr CFmpz -> IO ()

-- | /unity_zpq_add/ /f/ /g/ /h/ 
--
-- Sets \(f\) to \(g + h\). \(f\), \(g\) and \(h\) must be initialized with
-- same \(q\), \(p\) and \(n\).
foreign import ccall "aprcl.h unity_zpq_add"
  unity_zpq_add :: Ptr CUnityZpq ->Ptr CUnityZpq ->Ptr CUnityZpq -> IO ()

-- | /unity_zpq_mul/ /f/ /g/ /h/ 
--
-- Sets the \(f\) to \(g \cdot h\). \(f\), \(g\) and \(h\) must be
-- initialized with same \(q\), \(p\) and \(n\).
foreign import ccall "aprcl.h unity_zpq_mul"
  unity_zpq_mul :: Ptr CUnityZpq ->Ptr CUnityZpq ->Ptr CUnityZpq -> IO ()

-- | /_unity_zpq_mul_unity_p/ /f/ 
--
-- Sets \(f = f \cdot \zeta_p\).
foreign import ccall "aprcl.h _unity_zpq_mul_unity_p"
  _unity_zpq_mul_unity_p :: Ptr CUnityZpq -> IO ()

-- | /unity_zpq_mul_unity_p_pow/ /f/ /g/ /k/ 
--
-- Sets \(f\) to \(g \cdot \zeta_p^k\).
foreign import ccall "aprcl.h unity_zpq_mul_unity_p_pow"
  unity_zpq_mul_unity_p_pow :: Ptr CUnityZpq ->Ptr CUnityZpq -> CULong -> IO ()

-- | /unity_zpq_pow/ /f/ /g/ /p/ 
--
-- Sets \(f\) to \(g^p\). \(f\) and \(g\) must be initialized with same
-- \(p\), \(q\) and \(n\).
foreign import ccall "aprcl.h unity_zpq_pow"
  unity_zpq_pow :: Ptr CUnityZpq ->Ptr CUnityZpq -> Ptr CFmpz -> IO ()

-- | /unity_zpq_pow_ui/ /f/ /g/ /p/ 
--
-- Sets \(f\) to \(g^p\). \(f\) and \(g\) must be initialized with same
-- \(p\), \(q\) and \(n\).
foreign import ccall "aprcl.h unity_zpq_pow_ui"
  unity_zpq_pow_ui :: Ptr CUnityZpq ->Ptr CUnityZpq -> CULong -> IO ()

-- | /unity_zpq_gauss_sum/ /f/ /q/ /p/ 
--
-- Sets \(f = \tau(\chi_{p, q})\).
foreign import ccall "aprcl.h unity_zpq_gauss_sum"
  unity_zpq_gauss_sum :: Ptr CUnityZpq -> CULong -> CULong -> IO ()

-- | /unity_zpq_gauss_sum_sigma_pow/ /f/ /q/ /p/ 
--
-- Sets \(f = \tau^{\sigma_n}(\chi_{p, q})\).
foreign import ccall "aprcl.h unity_zpq_gauss_sum_sigma_pow"
  unity_zpq_gauss_sum_sigma_pow :: Ptr CUnityZpq -> CULong -> CULong -> IO ()

