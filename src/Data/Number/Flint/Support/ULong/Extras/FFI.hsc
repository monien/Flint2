{-# language 
    GADTs
  , ScopedTypeVariables 
  , UndecidableInstances
  , DataKinds 
  , TypeFamilies 
  , TypeApplications
  , TypeOperators 
  , PolyKinds
  , KindSignatures
  , TypeSynonymInstances
  , TupleSections
  , FlexibleInstances 
 #-}

module Data.Number.Flint.Support.ULong.Extras.FFI (
  -- * Arithmetic and number-theoretic functions for single-word integers
  -- * Random functions
    n_randlimb
  , n_randbits
  , n_randtest_bits
  , n_randint
  , n_urandint
  , n_randtest
  , n_randtest_not_zero
  , n_randprime
  , n_randtest_prime
  -- * Basic arithmetic
  , n_pow
  , n_flog
  , n_clog
  , n_clog_2exp
  -- * Miscellaneous
  , n_revbin
  , n_sizeinbase
  -- * Basic arithmetic with precomputed inverses
  , n_preinvert_limb_prenorm
  , n_preinvert_limb
  , n_precompute_inverse
  , n_mod_precomp
  , n_mod2_precomp
  , n_divrem2_preinv
  , n_div2_preinv
  , n_mod2_preinv
  , n_divrem2_precomp
  , n_ll_mod_preinv
  , n_lll_mod_preinv
  , n_mulmod_precomp
  , n_mulmod2_preinv
  , n_mulmod2
  , n_mulmod_preinv
  -- * Greatest common divisor
  , n_gcd
  , n_gcdinv
  , n_xgcd
  -- * Jacobi and Kronecker symbols
  , n_jacobi
  , n_jacobi_unsigned
  -- * Modular Arithmetic
  , n_addmod
  , n_submod
  , n_invmod
  , n_powmod_precomp
  , n_powmod_ui_precomp
  , n_powmod
  , n_powmod2_preinv
  , n_powmod2
  , n_powmod2_ui_preinv
  , n_powmod2_fmpz_preinv
  , n_sqrtmod
  , n_sqrtmod_2pow
  , n_sqrtmod_primepow
  , n_sqrtmodn
  , n_mulmod_shoup
  , n_mulmod_precomp_shoup
  -- * Divisibility testing
  , n_divides
  -- * Prime number generation and counting
  , n_primes_init
  , n_primes_clear
  , n_primes_next
  , n_primes_jump_after
  , n_primes_extend_small
  , n_primes_sieve_range
  , n_compute_primes
  , n_primes_arr_readonly
  , n_prime_inverses_arr_readonly
  , n_cleanup_primes
  , n_nextprime
  , n_prime_pi
  , n_prime_pi_bounds
  , n_nth_prime
  , n_nth_prime_bounds
  -- * Primality testing
  , n_is_oddprime_small
  , n_is_oddprime_binary
  , n_is_prime_pocklington
  , n_is_prime_pseudosquare
  , n_is_prime
  , n_is_strong_probabprime_precomp
  , n_is_strong_probabprime2_preinv
  , n_is_probabprime_fermat
  , n_is_probabprime_fibonacci
  , n_is_probabprime_BPSW
  , n_is_probabprime_lucas
  , n_is_probabprime
  -- * Chinese remaindering
  , n_CRT
  -- * Square root and perfect power testing
  , n_sqrt
  , n_sqrtrem
  , n_is_square
  , n_is_perfect_power235
  , n_is_perfect_power
  , n_rootrem
  , n_cbrt
  , n_cbrt_newton_iteration
  , n_cbrt_binary_search
  , n_cbrt_chebyshev_approx
  , n_cbrtrem
  -- * Factorisation
  , n_remove
  , n_remove2_precomp
  , n_factor_insert
  , n_factor_trial_range
  , n_factor_trial
  , n_factor_power235
  , n_factor_one_line
  , n_factor_lehman
  , n_factor_SQUFOF
  , n_factor
  , n_factor_trial_partial
  , n_factor_partial
  , n_factor_pp1
  , n_factor_pp1_wrapper
  , n_factor_pollard_brent_single
  , n_factor_pollard_brent
  -- * Arithmetic functions
  , n_moebius_mu
  , n_moebius_mu_vec
  , n_is_squarefree
  , n_euler_phi
  -- * Factorials
  , n_factorial_fast_mod2_preinv
  , n_factorial_mod2_preinv
  -- * Primitive Roots and Discrete Logarithms
  , n_primitive_root_prime_prefactor
  , n_primitive_root_prime
  , n_discrete_log_bsgs
  -- * Elliptic curve method for factorization of @mp_limb_t@
  , n_factor_ecm_double
  , n_factor_ecm_add
  , n_factor_ecm_mul_montgomery_ladder
  , n_factor_ecm_select_curve
  , n_factor_ecm_stage_I
  , n_factor_ecm_stage_II
  , n_factor_ecm
) where 

-- Arithmetic and number-theoretic functions for single-word integers ----------

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.C.Types
import Foreign.Storable

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz

#define ULONG_EXTRAS_INLINES_C
#include <flint/ulong_extras.h>

-- n_factor_t ------------------------------------------------------------------

data NFactor = NFactor {-# UNPACK #-} !(ForeignPtr CNFactor)
data CNFactor = CNFactor CInt (Ptr CInt) (Ptr CULong)

instance Storable CNFactor where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size n_factor_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment n_factor_t}
  peek ptr = do
    num <- #{peek n_factor_t, num} ptr
    exp <- return $ castPtr $ ptr `plusPtr` (sizeOf (undefined :: CInt))
    p   <- return $ castPtr $ ptr `plusPtr` (sizeOf (undefined :: CInt) * (1 + #const FLINT_MAX_FACTORS_IN_LIMB))
    return $ CNFactor num exp p
  poke = undefined

newNFactor = do
  x <- mallocForeignPtr
  withForeignPtr x n_factor_init
  -- addForeignPtrFinalizer p_n_factor_clear x
  return $ NFactor x

{-# INLINE withNFactor #-}
withNFactor (NFactor x) f = do
  withForeignPtr x $ \px -> f px >>= return . (NFactor x,)

-- n_primes_t ------------------------------------------------------------------

data NPrimes = NPrimes {-# UNPACK #-} !(ForeignPtr CNPrimes)
type CNPrimes = CFlint NPrimes

instance Storable CNPrimes where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size n_primes_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment n_primes_t}
  peek = undefined
  poke = undefined

newNPrimes = do
  x <- mallocForeignPtr
  withForeignPtr x n_primes_init
  addForeignPtrFinalizer p_n_primes_clear x
  return $ NPrimes x

{-# INLINE withNPrimes #-}
withNPrimes (NPrimes x) f = do
  withForeignPtr x $ \px -> f px >>= return . (NPrimes x,)

-- n_ecm_t ---------------------------------------------------------------------

data NEcm = NEcm {-# UNPACK #-} !(ForeignPtr CNEcm)
type CNEcm = CFlint NEcm

instance Storable CNEcm where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size n_ecm_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment n_ecm_t}
  peek = undefined
  poke = undefined

newNEcm = do
  x <- mallocForeignPtr
  return $ NEcm x

{-# INLINE withNEcm #-}
withNEcm (NEcm x) f = do
  withForeignPtr x $ \px -> f px >>= return . (NEcm x,)

-- Random functions ------------------------------------------------------------

-- | /n_randlimb/ /state/ 
--
-- Returns a uniformly pseudo random limb.
-- 
-- The algorithm generates two random half limbs \(s_j\), \(j = 0, 1\), by
-- iterating respectively \(v_{i+1} = (v_i a + b) \bmod{p_j}\) for some
-- initial seed \(v_0\), randomly chosen values \(a\) and \(b\) and
-- @p_0 = 4294967311 = nextprime(2^32)@ on a 64-bit machine and
-- @p_0 = nextprime(2^16)@ on a 32-bit machine and @p_1 = nextprime(p_0)@.
foreign import ccall "ulong_extras.h n_randlimb"
  n_randlimb :: Ptr CFRandState -> IO CULong

-- | /n_randbits/ /state/ /bits/ 
--
-- Returns a uniformly pseudo random number with the given number of bits.
-- The most significant bit is always set, unless zero is passed, in which
-- case zero is returned.
foreign import ccall "ulong_extras.h n_randbits"
  n_randbits :: Ptr CFRandState -> CUInt -> IO CULong

-- | /n_randtest_bits/ /state/ /bits/ 
--
-- Returns a uniformly pseudo random number with the given number of bits.
-- The most significant bit is always set, unless zero is passed, in which
-- case zero is returned. The probability of a value with a sparse binary
-- representation being returned is increased. This function is intended
-- for use in test code.
foreign import ccall "ulong_extras.h n_randtest_bits"
  n_randtest_bits :: Ptr CFRandState -> CInt -> IO CULong

-- | /n_randint/ /state/ /limit/ 
--
-- Returns a uniformly pseudo random number up to but not including the
-- given limit. If zero is passed as a parameter, an entire random limb is
-- returned.
foreign import ccall "ulong_extras.h n_randint"
  n_randint :: Ptr CFRandState -> CULong -> IO CULong

-- | /n_urandint/ /state/ /limit/ 
--
-- Returns a uniformly pseudo random number up to but not including the
-- given limit. If zero is passed as a parameter, an entire random limb is
-- returned. This function provides somewhat better randomness as compared
-- to @n_randint@, especially for larger values of limit.
foreign import ccall "ulong_extras.h n_urandint"
  n_urandint :: Ptr CFRandState -> CULong -> IO CULong

-- | /n_randtest/ /state/ 
--
-- Returns a pseudo random number with a random number of bits, from \(0\)
-- to @FLINT_BITS@. The probability of the special values \(0\), \(1\),
-- @COEFF_MAX@ and @WORD_MAX@ is increased as is the probability of a value
-- with sparse binary representation. This random function is mainly used
-- for testing purposes. This function is intended for use in test code.
foreign import ccall "ulong_extras.h n_randtest"
  n_randtest :: Ptr CFRandState -> IO CULong

-- | /n_randtest_not_zero/ /state/ 
--
-- As for @n_randtest@, but does not return \(0\). This function is
-- intended for use in test code.
foreign import ccall "ulong_extras.h n_randtest_not_zero"
  n_randtest_not_zero :: Ptr CFRandState -> IO CULong

-- | /n_randprime/ /state/ /bits/ /proved/ 
--
-- Returns a random prime number @(proved = 1)@ or probable prime
-- @(proved = 0)@ with @bits@ bits, where @bits@ must be at least 2 and at
-- most @FLINT_BITS@.
foreign import ccall "ulong_extras.h n_randprime"
  n_randprime :: Ptr CFRandState -> CULong -> CInt -> IO CULong

-- | /n_randtest_prime/ /state/ /proved/ 
--
-- Returns a random prime number @(proved = 1)@ or probable prime
-- @(proved = 0)@ with size randomly chosen between 2 and @FLINT_BITS@
-- bits. This function is intended for use in test code.
foreign import ccall "ulong_extras.h n_randtest_prime"
  n_randtest_prime :: Ptr CFRandState -> CInt -> IO CULong

-- Basic arithmetic ------------------------------------------------------------

-- | /n_pow/ /n/ /exp/ 
--
-- Returns @n^exp@. No checking is done for overflow. The exponent may be
-- zero. We define \(0^0 = 1\).
-- 
-- The algorithm simply uses a for loop. Repeated squaring is unlikely to
-- speed up this algorithm.
foreign import ccall "ulong_extras.h n_pow"
  n_pow :: CULong -> CULong -> IO CULong

-- | /n_flog/ /n/ /b/ 
--
-- Returns \(\lfloor\log_b n\rfloor\).
-- 
-- Assumes that \(n \geq 1\) and \(b \geq 2\).
foreign import ccall "ulong_extras.h n_flog"
  n_flog :: CULong -> CULong -> IO CULong

-- | /n_clog/ /n/ /b/ 
--
-- Returns \(\lceil\log_b n\rceil\).
-- 
-- Assumes that \(n \geq 1\) and \(b \geq 2\).
foreign import ccall "ulong_extras.h n_clog"
  n_clog :: CULong -> CULong -> IO CULong

-- | /n_clog_2exp/ /n/ /b/ 
--
-- Returns \(\lceil\log_b 2^n\rceil\).
-- 
-- Assumes that \(b \geq 2\).
foreign import ccall "ulong_extras.h n_clog_2exp"
  n_clog_2exp :: CULong -> CULong -> IO CULong

-- Miscellaneous ---------------------------------------------------------------

-- | /n_revbin/ /n/ /b/ 
--
-- Returns the binary reverse of \(n\), assuming it is \(b\) bits in
-- length, e.g. @n_revbin(10110, 6)@ will return @110100@.
foreign import ccall "ulong_extras.h n_revbin"
  n_revbin :: CULong -> CULong -> IO CULong

-- | /n_sizeinbase/ /n/ /base/ 
--
-- Returns the exact number of digits needed to represent \(n\) as a string
-- in base @base@ assumed to be between 2 and 36. Returns 1 when \(n = 0\).
foreign import ccall "ulong_extras.h n_sizeinbase"
  n_sizeinbase :: CULong -> CInt -> IO CInt

-- Basic arithmetic with precomputed inverses ----------------------------------

-- | /n_preinvert_limb_prenorm/ /n/ 
--
-- Computes an approximate inverse @invxl@ of the limb @xl@, with an
-- implicit leading~\`1\`. More formally it computes:
-- 
-- > invxl = (B^2 - B*x - 1)/x = (B^2 - 1)/x - B
-- 
-- Note that \(x\) must be normalised, i.e. with msb set. This inverse
-- makes use of the following theorem of Torbjorn Granlund and Peter
-- Montgomery~[Lemma~8.1]< [GraMon1994]>:
-- 
-- Let \(d\) be normalised, \(d < B\), i.e. it fits in a word, and suppose
-- that \(m d < B^2 \leq (m+1) d\). Let \(0 \leq n \leq B d - 1\). Write
-- \(n = n_2 B + n_1 B/2 + n_0\) with \(n_1 = 0\) or \(1\) and
-- \(n_0 < B/2\). Suppose
-- \(q_1 B + q_0 = n_2 B + (n_2 + n_1) (m - B) + n_1 (d-B/2) + n_0\) and
-- \(0 \leq q_0 < B\). Then \(0 \leq q_1 < B\) and
-- \(0 \leq n - q_1 d < 2 d\).
-- 
-- In the theorem, \(m\) is the inverse of \(d\). If we let @m = invxl + B@
-- and \(d = x\) we have \(m d = B^2 - 1 < B^2\) and
-- \((m+1) x = B^2 + d - 1 \geq B^2\).
-- 
-- The theorem is often applied as follows: note that \(n_0\) and
-- \(n_1 (d-B/2)\) are both less than \(B/2\). Also note that
-- \(n_1 (m-B) < B\). Thus the sum of all these terms contributes at most
-- \(1\) to \(q_1\). We are left with \(n_2 B + n_2 (m-B)\). But note that
-- \((m-B)\) is precisely our precomputed inverse @invxl@. If we write
-- \(q_1 B + q_0 = n_2 B + n_2 (m-B)\), then from the theorem, we have
-- \(0 \leq n - q_1 d < 3 d\), i.e. the quotient is out by at most \(2\)
-- and is always either correct or too small.
foreign import ccall "ulong_extras.h n_preinvert_limb_prenorm"
  n_preinvert_limb_prenorm :: CULong -> IO CULong

-- | /n_preinvert_limb/ /n/ 
--
-- Returns a precomputed inverse of \(n\), as defined in < [GraMol2010]>.
-- This precomputed inverse can be used with all of the functions that take
-- a precomputed inverse whose names are suffixed by @_preinv@.
-- 
-- We require \(n > 0\).
foreign import ccall "ulong_extras.h n_preinvert_limb"
  n_preinvert_limb :: CULong -> IO CULong

-- | /n_precompute_inverse/ /n/ 
--
-- Returns a precomputed inverse of \(n\) with double precision value
-- \(1/n\). This precomputed inverse can be used with all of the functions
-- that take a precomputed inverse whose names are suffixed by @_precomp@.
-- 
-- We require \(n > 0\).
foreign import ccall "ulong_extras.h n_precompute_inverse"
  n_precompute_inverse :: CULong -> IO CDouble

-- | /n_mod_precomp/ /a/ /n/ /ninv/ 
--
-- Returns \(a \bmod{n}\) given a precomputed inverse of \(n\) computed by
-- @n_precompute_inverse@. We require @n \< 2^FLINT_D_BITS@ and
-- @a \< 2^(FLINT_BITS-1)@ and \(0 \leq a < n^2\).
-- 
-- We assume the processor is in the standard round to nearest mode. Thus
-- @ninv@ is correct to \(53\) binary bits, the least significant bit of
-- which we shall call a place, and can be at most half a place out. When
-- \(a\) is multiplied by \(ninv\), the binary representation of \(a\) is
-- exact and the mantissa is less than \(2\), thus we see that @a * ninv@
-- can be at most one out in the mantissa. We now truncate @a * ninv@ to
-- the nearest integer, which is always a round down. Either we already
-- have an integer, or we need to make a change down of at least \(1\) in
-- the last place. In the latter case we either get precisely the exact
-- quotient or below it as when we rounded the product to the nearest place
-- we changed by at most half a place. In the case that truncating to an
-- integer takes us below the exact quotient, we have rounded down by less
-- than \(1\) plus half a place. But as the product is less than \(n\) and
-- \(n\) is less than \(2^{53}\), half a place is less than \(1\), thus we
-- are out by less than \(2\) from the exact quotient, i.e. the quotient we
-- have computed is the quotient we are after or one too small. That leaves
-- only the case where we had to round up to the nearest place which
-- happened to be an integer, so that truncating to an integer didn\'t
-- change anything. But this implies that the exact quotient \(a/n\) is
-- less than \(2^{-54}\) from an integer. We deal with this rare case by
-- subtracting 1 from the quotient. Then the quotient we have computed is
-- either exactly what we are after, or one too small.
foreign import ccall "ulong_extras.h n_mod_precomp"
  n_mod_precomp :: CULong -> CULong -> CDouble -> IO CULong

-- | /n_mod2_precomp/ /a/ /n/ /ninv/ 
--
-- Returns \(a \bmod{n}\) given a precomputed inverse of \(n\) computed by
-- @n_precompute_inverse@. There are no restrictions on \(a\) or on \(n\).
-- 
-- As for @n_mod_precomp@ for \(n < 2^{53}\) and \(a < n^2\) the computed
-- quotient is either what we are after or one too large or small. We deal
-- with these cases. Otherwise we can be sure that the top \(52\) bits of
-- the quotient are computed correctly. We take the remainder and adjust
-- the quotient by multiplying the remainder by @ninv@ to compute another
-- approximate quotient as per @mod_precomp@. Now the remainder may be
-- either negative or positive, so the quotient we compute may be one out
-- in either direction.
foreign import ccall "ulong_extras.h n_mod2_precomp"
  n_mod2_precomp :: CULong -> CULong -> CDouble -> IO CULong

-- | /n_divrem2_preinv/ /q/ /a/ /n/ /ninv/ 
--
-- Returns \(a \bmod{n}\) and sets \(q\) to the quotient of \(a\) by \(n\),
-- given a precomputed inverse of \(n\) computed by @n_preinvert_limb()@.
-- There are no restrictions on \(a\) and the only restriction on \(n\) is
-- that it be nonzero.
-- 
-- This uses the algorithm of Granlund and Möller < [GraMol2010]>. First
-- \(n\) is normalised and \(a\) is shifted into two limbs to compensate.
-- Then their algorithm is applied verbatim and the remainder shifted back.
foreign import ccall "ulong_extras.h n_divrem2_preinv"
  n_divrem2_preinv :: Ptr CULong -> CULong -> CULong -> CULong -> IO CULong

-- | /n_div2_preinv/ /a/ /n/ /ninv/ 
--
-- Returns the Euclidean quotient of \(a\) by \(n\) given a precomputed
-- inverse of \(n\) computed by @n_preinvert_limb@. There are no
-- restrictions on \(a\) and the only restriction on \(n\) is that it be
-- nonzero.
-- 
-- This uses the algorithm of Granlund and Möller < [GraMol2010]>. First
-- \(n\) is normalised and \(a\) is shifted into two limbs to compensate.
-- Then their algorithm is applied verbatim.
foreign import ccall "ulong_extras.h n_div2_preinv"
  n_div2_preinv :: CULong -> CULong -> CULong -> IO CULong

-- | /n_mod2_preinv/ /a/ /n/ /ninv/ 
--
-- Returns \(a \bmod{n}\) given a precomputed inverse of \(n\) computed by
-- @n_preinvert_limb()@. There are no restrictions on \(a\) and the only
-- restriction on \(n\) is that it be nonzero.
-- 
-- This uses the algorithm of Granlund and Möller < [GraMol2010]>. First
-- \(n\) is normalised and \(a\) is shifted into two limbs to compensate.
-- Then their algorithm is applied verbatim and the result shifted back.
foreign import ccall "ulong_extras.h n_mod2_preinv"
  n_mod2_preinv :: CULong -> CULong -> CULong -> IO CULong

-- | /n_divrem2_precomp/ /q/ /a/ /n/ /npre/ 
--
-- Returns \(a \bmod{n}\) given a precomputed inverse of \(n\) computed by
-- @n_precompute_inverse@ and sets \(q\) to the quotient. There are no
-- restrictions on \(a\) or on \(n\).
-- 
-- This is as for @n_mod2_precomp@ with some additional care taken to
-- retain the quotient information. There are also special cases to deal
-- with the case where \(a\) is already reduced modulo \(n\) and where
-- \(n\) is \(64\) bits and \(a\) is not reduced modulo \(n\).
foreign import ccall "ulong_extras.h n_divrem2_precomp"
  n_divrem2_precomp :: Ptr CULong -> CULong -> CULong -> CDouble -> IO CULong

-- | /n_ll_mod_preinv/ /a_hi/ /a_lo/ /n/ /ninv/ 
--
-- Returns \(a \bmod{n}\) given a precomputed inverse of \(n\) computed by
-- @n_preinvert_limb@. There are no restrictions on \(a\), which will be
-- two limbs @(a_hi, a_lo)@, or on \(n\).
-- 
-- The old version of this function merely reduced the top limb @a_hi@
-- modulo \(n\) so that @udiv_qrnnd_preinv()@ could be used.
-- 
-- The new version reduces the top limb modulo \(n\) as per @n_mod2_preinv@
-- and then the algorithm of Granlund and Möller < [GraMol2010]> is used
-- again to reduce modulo \(n\).
foreign import ccall "ulong_extras.h n_ll_mod_preinv"
  n_ll_mod_preinv :: CULong -> CULong -> CULong -> CULong -> IO CULong

-- | /n_lll_mod_preinv/ /a_hi/ /a_mi/ /a_lo/ /n/ /ninv/ 
--
-- Returns \(a \bmod{n}\), where \(a\) has three limbs
-- @(a_hi, a_mi, a_lo)@, given a precomputed inverse of \(n\) computed by
-- @n_preinvert_limb@. It is assumed that @a_hi@ is reduced modulo \(n\).
-- There are no restrictions on \(n\).
-- 
-- This function uses the algorithm of Granlund and Möller < [GraMol2010]>
-- to first reduce the top two limbs modulo \(n\), then does the same on
-- the bottom two limbs.
foreign import ccall "ulong_extras.h n_lll_mod_preinv"
  n_lll_mod_preinv :: CULong -> CULong -> CULong -> CULong -> CULong -> IO CULong

-- | /n_mulmod_precomp/ /a/ /b/ /n/ /ninv/ 
--
-- Returns \(a b \bmod{n}\) given a precomputed inverse of \(n\) computed
-- by @n_precompute_inverse@. We require @n \< 2^FLINT_D_BITS@ and
-- \(0 \leq a, b < n\).
-- 
-- We assume the processor is in the standard round to nearest mode. Thus
-- @ninv@ is correct to \(53\) binary bits, the least significant bit of
-- which we shall call a place, and can be at most half a place out. The
-- product of \(a\) and \(b\) is computed with error at most half a place.
-- When @a * b@ is multiplied by \(ninv\) we find that the exact quotient
-- and computed quotient differ by less than two places. As the quotient is
-- less than \(n\) this means that the exact quotient is at most \(1\) away
-- from the computed quotient. We truncate this quotient to an integer
-- which reduces the value by less than \(1\). We end up with a value which
-- can be no more than two above the quotient we are after and no less than
-- two below. However an argument similar to that for @n_mod_precomp@ shows
-- that the truncated computed quotient cannot be two smaller than the
-- truncated exact quotient. In other words the computed integer quotient
-- is at most two above and one below the quotient we are after.
foreign import ccall "ulong_extras.h n_mulmod_precomp"
  n_mulmod_precomp :: CULong -> CULong -> CULong -> CDouble -> IO CULong

-- | /n_mulmod2_preinv/ /a/ /b/ /n/ /ninv/ 
--
-- Returns \(a b \bmod{n}\) given a precomputed inverse of \(n\) computed
-- by @n_preinvert_limb@. There are no restrictions on \(a\), \(b\) or on
-- \(n\). This is implemented by multiplying using @umul_ppmm@ and then
-- reducing using @n_ll_mod_preinv@.
foreign import ccall "ulong_extras.h n_mulmod2_preinv"
  n_mulmod2_preinv :: CULong -> CULong -> CULong -> CULong -> IO CULong

-- | /n_mulmod2/ /a/ /b/ /n/ 
--
-- Returns \(a b \bmod{n}\). There are no restrictions on \(a\), \(b\) or
-- on \(n\). This is implemented by multiplying using @umul_ppmm@ and then
-- reducing using @n_ll_mod_preinv@ after computing a precomputed inverse.
foreign import ccall "ulong_extras.h n_mulmod2"
  n_mulmod2 :: CULong -> CULong -> CULong -> IO CULong

-- | /n_mulmod_preinv/ /a/ /b/ /n/ /ninv/ /norm/ 
--
-- Returns \(a b \pmod{n}\) given a precomputed inverse of \(n\) computed
-- by @n_preinvert_limb@, assuming \(a\) and \(b\) are reduced modulo \(n\)
-- and \(n\) is normalised, i.e. with most significant bit set. There are
-- no other restrictions on \(a\), \(b\) or \(n\).
-- 
-- The value @norm@ is provided for convenience. As \(n\) is required to be
-- normalised, it may be that \(a\) and \(b\) have been shifted to the left
-- by @norm@ bits before calling the function. Their product then has an
-- extra factor of \(2^\text{norm}\). Specifying a nonzero @norm@ will
-- shift the product right by this many bits before reducing it.
-- 
-- The algorithm used is that of Granlund and Möller < [GraMol2010]>.
foreign import ccall "ulong_extras.h n_mulmod_preinv"
  n_mulmod_preinv :: CULong -> CULong -> CULong -> CULong -> CULong -> IO CULong

-- Greatest common divisor -----------------------------------------------------

-- | /n_gcd/ /x/ /y/ 
--
-- Returns the greatest common divisor \(g\) of \(x\) and \(y\). No
-- assumptions are made about the values \(x\) and \(y\).
-- 
-- This function wraps GMP\'s @mpn_gcd_1@.
foreign import ccall "ulong_extras.h n_gcd"
  n_gcd :: CULong -> CULong -> IO CULong

-- | /n_gcdinv/ /a/ /x/ /y/ 
--
-- Returns the greatest common divisor \(g\) of \(x\) and \(y\) and
-- computes \(a\) such that \(0 \leq a < y\) and
-- \(a x = \gcd(x, y) \bmod{y}\), when this is defined. We require
-- \(x < y\).
-- 
-- When \(y = 1\) the greatest common divisor is set to \(1\) and \(a\) is
-- set to \(0\).
-- 
-- This is merely an adaption of the extended Euclidean algorithm computing
-- just one cofactor and reducing it modulo \(y\).
foreign import ccall "ulong_extras.h n_gcdinv"
  n_gcdinv :: Ptr CULong -> CULong -> CULong -> IO CULong

-- | /n_xgcd/ /a/ /b/ /x/ /y/ 
--
-- Returns the greatest common divisor \(g\) of \(x\) and \(y\) and
-- unsigned values \(a\) and \(b\) such that \(a x - b y = g\). We require
-- \(x \geq y\).
-- 
-- We claim that computing the extended greatest common divisor via the
-- Euclidean algorithm always results in cofactor
-- \(\lvert a \rvert < x/2\), \(\lvert b\rvert < x/2\), with perhaps some
-- small degenerate exceptions.
-- 
-- We proceed by induction.
-- 
-- Suppose we are at some step of the algorithm, with \(x_n = q y_n + r\)
-- with \(r \geq 1\), and suppose \(1 = s y_n - t r\) with \(s < y_n / 2\),
-- \(t < y_n / 2\) by hypothesis.
-- 
-- Write \(1 = s y_n - t (x_n - q y_n) = (s + t q) y_n - t x_n\).
-- 
-- It suffices to show that \((s + t q) < x_n / 2\) as
-- \(t < y_n / 2 < x_n / 2\), which will complete the induction step.
-- 
-- But at the previous step in the backsubstitution we would have had
-- \(1 = s r - c d\) with \(s < r/2\) and \(c < r/2\).
-- 
-- Then \(s + t q < r/2 + y_n / 2 q = (r + q y_n)/2 = x_n / 2\).
-- 
-- See the documentation of @n_gcd@ for a description of the branching in
-- the algorithm, which is faster than using division.
foreign import ccall "ulong_extras.h n_xgcd"
  n_xgcd :: Ptr CULong -> Ptr CULong -> CULong -> CULong -> IO CULong

-- Jacobi and Kronecker symbols ------------------------------------------------

-- | /n_jacobi/ /x/ /y/ 
--
-- Computes the Jacobi symbol \(\left(\frac{x}{y}\right)\) for any \(x\)
-- and odd \(y\).
foreign import ccall "ulong_extras.h n_jacobi"
  n_jacobi :: CLong -> CULong -> IO CInt

-- | /n_jacobi_unsigned/ /x/ /y/ 
--
-- Computes the Jacobi symbol, allowing \(x\) to go up to a full limb.
foreign import ccall "ulong_extras.h n_jacobi_unsigned"
  n_jacobi_unsigned :: CULong -> CULong -> IO CInt

-- Modular Arithmetic ----------------------------------------------------------

-- | /n_addmod/ /a/ /b/ /n/ 
--
-- Returns \((a + b) \bmod{n}\).
foreign import ccall "ulong_extras.h n_addmod"
  n_addmod :: CULong -> CULong -> CULong -> IO CULong

-- | /n_submod/ /a/ /b/ /n/ 
--
-- Returns \((a - b) \bmod{n}\).
foreign import ccall "ulong_extras.h n_submod"
  n_submod :: CULong -> CULong -> CULong -> IO CULong

-- | /n_invmod/ /x/ /y/ 
--
-- Returns the inverse of \(x\) modulo \(y\), if it exists. Otherwise an
-- exception is thrown.
-- 
-- This is merely an adaption of the extended Euclidean algorithm with
-- appropriate normalisation.
foreign import ccall "ulong_extras.h n_invmod"
  n_invmod :: CULong -> CULong -> IO CULong

-- | /n_powmod_precomp/ /a/ /exp/ /n/ /npre/ 
--
-- Returns @a^exp@ modulo \(n\) given a precomputed inverse of \(n\)
-- computed by @n_precompute_inverse@. We require \(n < 2^{53}\) and
-- \(0 \leq a < n\). There are no restrictions on @exp@, i.e. it can be
-- negative.
-- 
-- This is implemented as a standard binary powering algorithm using
-- repeated squaring and reducing modulo \(n\) at each step.
foreign import ccall "ulong_extras.h n_powmod_precomp"
  n_powmod_precomp :: CULong -> CLong -> CULong -> CDouble -> IO CULong

-- | /n_powmod_ui_precomp/ /a/ /exp/ /n/ /npre/ 
--
-- Returns @a^exp@ modulo \(n\) given a precomputed inverse of \(n\)
-- computed by @n_precompute_inverse@. We require \(n < 2^{53}\) and
-- \(0 \leq a < n\). The exponent @exp@ is unsigned and so can be larger
-- than allowed by @n_powmod_precomp@.
-- 
-- This is implemented as a standard binary powering algorithm using
-- repeated squaring and reducing modulo \(n\) at each step.
foreign import ccall "ulong_extras.h n_powmod_ui_precomp"
  n_powmod_ui_precomp :: CULong -> CULong -> CULong -> CDouble -> IO CULong

-- | /n_powmod/ /a/ /exp/ /n/ 
--
-- Returns @a^exp@ modulo \(n\). We require @n \< 2^FLINT_D_BITS@ and
-- \(0 \leq a < n\). There are no restrictions on @exp@, i.e. it can be
-- negative.
-- 
-- This is implemented by precomputing an inverse and calling the @precomp@
-- version of this function.
foreign import ccall "ulong_extras.h n_powmod"
  n_powmod :: CULong -> CLong -> CULong -> IO CULong

-- | /n_powmod2_preinv/ /a/ /exp/ /n/ /ninv/ 
--
-- Returns @(a^exp) % n@ given a precomputed inverse of \(n\) computed by
-- @n_preinvert_limb@. We require \(0 \leq a < n\), but there are no
-- restrictions on \(n\) or on @exp@, i.e. it can be negative.
-- 
-- This is implemented as a standard binary powering algorithm using
-- repeated squaring and reducing modulo \(n\) at each step.
-- 
-- If @exp@ is negative but \(a\) is not invertible modulo \(n\), an
-- exception is raised.
foreign import ccall "ulong_extras.h n_powmod2_preinv"
  n_powmod2_preinv :: CULong -> CLong -> CULong -> CULong -> IO CULong

-- | /n_powmod2/ /a/ /exp/ /n/ 
--
-- Returns @(a^exp) % n@. We require \(0 \leq a < n\), but there are no
-- restrictions on \(n\) or on @exp@, i.e. it can be negative.
-- 
-- This is implemented by precomputing an inverse limb and calling the
-- @preinv@ version of this function.
-- 
-- If @exp@ is negative but \(a\) is not invertible modulo \(n\), an
-- exception is raised.
foreign import ccall "ulong_extras.h n_powmod2"
  n_powmod2 :: CULong -> CLong -> CULong -> IO CULong

-- | /n_powmod2_ui_preinv/ /a/ /exp/ /n/ /ninv/ 
--
-- Returns @(a^exp) % n@ given a precomputed inverse of \(n\) computed by
-- @n_preinvert_limb@. We require \(0 \leq a < n\), but there are no
-- restrictions on \(n\). The exponent @exp@ is unsigned and so can be
-- larger than allowed by @n_powmod2_preinv@.
-- 
-- This is implemented as a standard binary powering algorithm using
-- repeated squaring and reducing modulo \(n\) at each step.
foreign import ccall "ulong_extras.h n_powmod2_ui_preinv"
  n_powmod2_ui_preinv :: CULong -> CULong -> CULong -> CULong -> IO CULong

-- | /n_powmod2_fmpz_preinv/ /a/ /exp/ /n/ /ninv/ 
--
-- Returns @(a^exp) % n@ given a precomputed inverse of \(n\) computed by
-- @n_preinvert_limb@. We require \(0 \leq a < n\), but there are no
-- restrictions on \(n\). The exponent @exp@ must not be negative.
-- 
-- This is implemented as a standard binary powering algorithm using
-- repeated squaring and reducing modulo \(n\) at each step.
foreign import ccall "ulong_extras.h n_powmod2_fmpz_preinv"
  n_powmod2_fmpz_preinv :: CULong -> Ptr CFmpz -> CULong -> CULong -> IO CULong

-- | /n_sqrtmod/ /a/ /p/ 
--
-- If \(p\) is prime, compute a square root of \(a\) modulo \(p\) if \(a\)
-- is a quadratic residue modulo \(p\), otherwise return \(0\).
-- 
-- If \(p\) is not prime the result is with high probability \(0\),
-- indicating that \(p\) is not prime, or \(a\) is not a square modulo
-- \(p\). Otherwise the result is meaningless.
-- 
-- Assumes that \(a\) is reduced modulo \(p\).
foreign import ccall "ulong_extras.h n_sqrtmod"
  n_sqrtmod :: CULong -> CULong -> IO CULong

-- | /n_sqrtmod_2pow/ /sqrt/ /a/ /exp/ 
--
-- Computes all the square roots of @a@ modulo @2^exp@. The roots are
-- stored in an array which is created and whose address is stored in the
-- location pointed to by @sqrt@. The array of roots is allocated by the
-- function but must be cleaned up by the user by calling @flint_free@. The
-- number of roots is returned by the function. If @a@ is not a quadratic
-- residue modulo @2^exp@ then 0 is returned by the function and the
-- location @sqrt@ points to is set to NULL.
foreign import ccall "ulong_extras.h n_sqrtmod_2pow"
  n_sqrtmod_2pow :: Ptr (Ptr CULong) -> CULong -> CLong -> IO CLong

-- | /n_sqrtmod_primepow/ /sqrt/ /a/ /p/ /exp/ 
--
-- Computes all the square roots of @a@ modulo @p^exp@. The roots are
-- stored in an array which is created and whose address is stored in the
-- location pointed to by @sqrt@. The array of roots is allocated by the
-- function but must be cleaned up by the user by calling @flint_free@. The
-- number of roots is returned by the function. If @a@ is not a quadratic
-- residue modulo @p^exp@ then 0 is returned by the function and the
-- location @sqrt@ points to is set to NULL.
foreign import ccall "ulong_extras.h n_sqrtmod_primepow"
  n_sqrtmod_primepow :: Ptr (Ptr CULong) -> CULong -> CULong -> CLong -> IO CLong

-- | /n_sqrtmodn/ /sqrt/ /a/ /fac/ 
--
-- Computes all the square roots of @a@ modulo @m@ given the factorisation
-- of @m@ in @fac@. The roots are stored in an array which is created and
-- whose address is stored in the location pointed to by @sqrt@. The array
-- of roots is allocated by the function but must be cleaned up by the user
-- by calling @flint_free@. The number of roots is returned by the
-- function. If @a@ is not a quadratic residue modulo @m@ then 0 is
-- returned by the function and the location @sqrt@ points to is set to
-- NULL.
foreign import ccall "ulong_extras.h n_sqrtmodn"
  n_sqrtmodn :: Ptr (Ptr CULong) -> CULong -> Ptr (Ptr CNFactor) -> IO CLong

-- | /n_mulmod_shoup/ /w/ /t/ /w_precomp/ /p/ 
--
-- Returns \(w t \bmod{p}\) given a precomputed scaled approximation of
-- \(w / p\) computed by @n_mulmod_precomp_shoup@. The value of \(p\)
-- should be less than \(2^{\mathtt{FLINT\_BITS} - 1}\). \(w\) and \(t\)
-- should be less than \(p\). Works faster than @n_mulmod2_preinv@ if \(w\)
-- fixed and \(t\) from array (for example, scalar multiplication of
-- vector).
foreign import ccall "ulong_extras.h n_mulmod_shoup"
  n_mulmod_shoup :: CMpLimb -> CMpLimb -> CMpLimb -> CMpLimb -> IO CMpLimb

-- | /n_mulmod_precomp_shoup/ /w/ /p/ 
--
-- Returns \(w'\), scaled approximation of \(w / p\). \(w'\) is equal to
-- the integer part of \(w \cdot 2^{\mathtt{FLINT\_BITS}} / p\).
foreign import ccall "ulong_extras.h n_mulmod_precomp_shoup"
  n_mulmod_precomp_shoup :: CMpLimb -> CMpLimb -> IO CMpLimb

-- Divisibility testing --------------------------------------------------------

-- | /n_divides/ /q/ /n/ /p/ 
--
-- Returns @1@ if @p@ divides @n@ and sets @q@ to the quotient, otherwise
-- returns @0@ and sets @q@ to @0@.
foreign import ccall "ulong_extras.h n_divides"
  n_divides :: Ptr CMpLimb -> CMpLimb -> CMpLimb -> IO CInt

-- Prime number generation and counting ----------------------------------------

-- | /n_primes_init/ /iter/ 
--
-- Initialises the prime number iterator @iter@ for use.
foreign import ccall "ulong_extras.h n_primes_init"
  n_primes_init :: Ptr CNPrimes -> IO ()

-- | /n_primes_clear/ /iter/ 
--
-- Clears memory allocated by the prime number iterator @iter@.
foreign import ccall "ulong_extras.h n_primes_clear"
  n_primes_clear :: Ptr CNPrimes -> IO ()

foreign import ccall "ulong_extras.h &n_primes_clear"
  p_n_primes_clear :: FunPtr (Ptr CNPrimes -> IO ())

-- | /n_primes_next/ /iter/ 
--
-- Returns the next prime number and advances the state of @iter@. The
-- first call returns 2.
-- 
-- Small primes are looked up from @flint_small_primes@. When this table is
-- exhausted, primes are generated in blocks by calling
-- @n_primes_sieve_range@.
foreign import ccall "ulong_extras.h n_primes_next"
  n_primes_next :: Ptr CNPrimes -> IO CULong

-- | /n_primes_jump_after/ /iter/ /n/ 
--
-- Changes the state of @iter@ to start generating primes after \(n\)
-- (excluding \(n\) itself).
foreign import ccall "ulong_extras.h n_primes_jump_after"
  n_primes_jump_after :: Ptr CNPrimes -> CULong -> IO ()

-- | /n_primes_extend_small/ /iter/ /bound/ 
--
-- Extends the table of small primes in @iter@ to contain at least two
-- primes larger than or equal to @bound@.
foreign import ccall "ulong_extras.h n_primes_extend_small"
  n_primes_extend_small :: Ptr CNPrimes -> CULong -> IO ()

-- | /n_primes_sieve_range/ /iter/ /a/ /b/ 
--
-- Sets the block endpoints of @iter@ to the smallest and largest odd
-- numbers between \(a\) and \(b\) inclusive, and sieves to mark all odd
-- primes in this range. The iterator state is changed to point to the
-- first number in the sieved range.
foreign import ccall "ulong_extras.h n_primes_sieve_range"
  n_primes_sieve_range :: Ptr CNPrimes -> CULong -> CULong -> IO ()

-- | /n_compute_primes/ /num_primes/ 
--
-- Precomputes at least @num_primes@ primes and their @double@ precomputed
-- inverses and stores them in an internal cache. Assuming that FLINT has
-- been built with support for thread-local storage, each thread has its
-- own cache.
foreign import ccall "ulong_extras.h n_compute_primes"
  n_compute_primes :: CULong -> IO ()

-- | /n_primes_arr_readonly/ /num_primes/ 
--
-- Returns a pointer to a read-only array of the first @num_primes@ prime
-- numbers. The computed primes are cached for repeated calls. The pointer
-- is valid until the user calls @n_cleanup_primes@ in the same thread.
foreign import ccall "ulong_extras.h n_primes_arr_readonly"
  n_primes_arr_readonly :: CULong -> IO (Ptr CULong)

-- | /n_prime_inverses_arr_readonly/ /n/ 
--
-- Returns a pointer to a read-only array of inverses of the first
-- @num_primes@ prime numbers. The computed primes are cached for repeated
-- calls. The pointer is valid until the user calls @n_cleanup_primes@ in
-- the same thread.
foreign import ccall "ulong_extras.h n_prime_inverses_arr_readonly"
  n_prime_inverses_arr_readonly :: CULong -> IO (Ptr CDouble)

-- | /n_cleanup_primes/ 
--
-- Frees the internal cache of prime numbers used by the current thread.
-- This will invalidate any pointers returned by @n_primes_arr_readonly@ or
-- @n_prime_inverses_arr_readonly@.
foreign import ccall "ulong_extras.h n_cleanup_primes"
  n_cleanup_primes :: IO ()

-- | /n_nextprime/ /n/ /proved/ 
--
-- Returns the next prime after \(n\). Assumes the result will fit in an
-- @ulong@. If proved is \(0\), i.e. false, the prime is not proven prime,
-- otherwise it is.
foreign import ccall "ulong_extras.h n_nextprime"
  n_nextprime :: CULong -> CInt -> IO CULong

-- | /n_prime_pi/ /n/ 
--
-- Returns the value of the prime counting function \(\pi(n)\), i.e. the
-- number of primes less than or equal to \(n\). The invariant
-- @n_prime_pi(n_nth_prime(n)) == n@.
-- 
-- Currently, this function simply extends the table of cached primes up to
-- an upper limit and then performs a binary search.
foreign import ccall "ulong_extras.h n_prime_pi"
  n_prime_pi :: CULong -> IO CULong

-- | /n_prime_pi_bounds/ /lo/ /hi/ /n/ 
--
-- Calculates lower and upper bounds for the value of the prime counting
-- function @lo \<= pi(n) \<= hi@. If @lo@ and @hi@ point to the same
-- location, the high value will be stored.
-- 
-- This does a table lookup for small values, then switches over to some
-- proven bounds.
-- 
-- The upper approximation is \(1.25506 n / \ln n\), and the lower is
-- \(n / \ln n\). These bounds are due to Rosser and Schoenfeld
-- < [RosSch1962]> and valid for \(n \geq 17\).
-- 
-- We use the number of bits in \(n\) (or one less) to form an
-- approximation to \(\ln n\), taking care to use a value too small or too
-- large to maintain the inequality.
foreign import ccall "ulong_extras.h n_prime_pi_bounds"
  n_prime_pi_bounds :: Ptr CULong -> Ptr CULong -> CULong -> IO ()

-- | /n_nth_prime/ /n/ 
--
-- Returns the \(n\)th prime number \(p_n\), using the mathematical
-- indexing convention \(p_1 = 2, p_2 = 3, \dotsc\).
-- 
-- This function simply ensures that the table of cached primes is large
-- enough and then looks up the entry.
foreign import ccall "ulong_extras.h n_nth_prime"
  n_nth_prime :: CULong -> IO CULong

-- | /n_nth_prime_bounds/ /lo/ /hi/ /n/ 
--
-- Calculates lower and upper bounds for the \(n\)th prime number \(p_n\) ,
-- @lo \<= p_n \<= hi@. If @lo@ and @hi@ point to the same location, the
-- high value will be stored. Note that this function will overflow for
-- sufficiently large \(n\).
-- 
-- We use the following estimates, valid for \(n > 5\) :
-- 
-- \[`\]
-- \[\begin{aligned}
-- p_n  & >  n (\ln n + \ln \ln n - 1) \\
-- p_n  & <  n (\ln n + \ln \ln n) \\
-- p_n  & <  n (\ln n + \ln \ln n - 0.9427) \quad (n \geq 15985)
-- \end{aligned}\]
-- 
-- The first inequality was proved by Dusart < [Dus1999]>, and the last is
-- due to Massias and Robin < [MasRob1996]>. For a further overview, see
-- <http://primes.utm.edu/howmany.shtml> .
-- 
-- We bound \(\ln n\) using the number of bits in \(n\) as in
-- @n_prime_pi_bounds()@, and estimate \(\ln \ln n\) to the nearest
-- integer; this function is nearly constant.
foreign import ccall "ulong_extras.h n_nth_prime_bounds"
  n_nth_prime_bounds :: Ptr CULong -> Ptr CULong -> CULong -> IO ()

-- Primality testing -----------------------------------------------------------

-- | /n_is_oddprime_small/ /n/ 
--
-- Returns \(1\) if \(n\) is an odd prime smaller than
-- @FLINT_ODDPRIME_SMALL_CUTOFF@. Expects \(n\) to be odd and smaller than
-- the cutoff.
-- 
-- This function merely uses a lookup table with one bit allocated for each
-- odd number up to the cutoff.
foreign import ccall "ulong_extras.h n_is_oddprime_small"
  n_is_oddprime_small :: CULong -> IO CInt

-- | /n_is_oddprime_binary/ /n/ 
--
-- This function performs a simple binary search through the table of
-- cached primes for \(n\). If it exists in the array it returns \(1\),
-- otherwise \(0\). For the algorithm to operate correctly \(n\) should be
-- odd and at least \(17\).
-- 
-- Lower and upper bounds are computed with @n_prime_pi_bounds@. Once we
-- have bounds on where to look in the table, we refine our search with a
-- simple binary algorithm, taking the top or bottom of the current
-- interval as necessary.
foreign import ccall "ulong_extras.h n_is_oddprime_binary"
  n_is_oddprime_binary :: CULong -> IO CInt

-- | /n_is_prime_pocklington/ /n/ /iterations/ 
--
-- Tests if \(n\) is a prime using the Pocklington--Lehmer primality test.
-- If \(1\) is returned \(n\) has been proved prime. If \(0\) is returned
-- \(n\) is composite. However \(-1\) may be returned if nothing was proved
-- either way due to the number of iterations being too small.
-- 
-- The most time consuming part of the algorithm is factoring \(n - 1\).
-- For this reason @n_factor_partial@ is used, which uses a combination of
-- trial factoring and Hart\'s one line factor algorithm < [Har2012]> to
-- try to quickly factor \(n - 1\). Additionally if the cofactor is less
-- than the square root of \(n - 1\) the algorithm can still proceed.
-- 
-- One can also specify a number of iterations if less time should be
-- taken. Simply set this to @WORD(0)@ if this is irrelevant. In most cases
-- a greater number of iterations will not significantly affect timings as
-- most of the time is spent factoring.
-- 
-- See <https://mathworld.wolfram.com/PocklingtonsTheorem.html> for a
-- description of the algorithm.
foreign import ccall "ulong_extras.h n_is_prime_pocklington"
  n_is_prime_pocklington :: CULong -> CULong -> IO CInt

-- | /n_is_prime_pseudosquare/ /n/ 
--
-- Tests if \(n\) is a prime according to Theorem 2.7 < [LukPatWil1996]>.
-- 
-- We first factor \(N\) using trial division up to some limit \(B\). In
-- fact, the number of primes used in the trial factoring is at most
-- @FLINT_PSEUDOSQUARES_CUTOFF@.
-- 
-- Next we compute \(N/B\) and find the next pseudosquare \(L_p\) above
-- this value, using a static table as per
-- <https://oeis.org/A002189/b002189.txt> .
-- 
-- As noted in the text, if \(p\) is prime then Step 3 will pass. This test
-- rejects many composites, and so by this time we suspect that \(p\) is
-- prime. If \(N\) is \(3\) or \(7\) modulo \(8\), we are done, and \(N\)
-- is prime.
-- 
-- We now run a probable prime test, for which no known counterexamples are
-- known, to reject any composites. We then proceed to prove \(N\) prime by
-- executing Step 4. In the case that \(N\) is \(1\) modulo \(8\), if Step
-- 4 fails, we extend the number of primes \(p_i\) at Step 3 and hope to
-- find one which passes Step 4. We take the test one past the largest
-- \(p\) for which we have pseudosquares \(L_p\) tabulated, as this already
-- corresponds to the next \(L_p\) which is bigger than \(2^{64}\) and
-- hence larger than any prime we might be testing.
-- 
-- As explained in the text, Condition 4 cannot fail if \(N\) is prime.
-- 
-- The possibility exists that the probable prime test declares a composite
-- prime. However in that case an error is printed, as that would be of
-- independent interest.
foreign import ccall "ulong_extras.h n_is_prime_pseudosquare"
  n_is_prime_pseudosquare :: CULong -> IO CInt

-- | /n_is_prime/ /n/ 
--
-- Tests if \(n\) is a prime. This first sieves for small prime factors,
-- then simply calls @n_is_probabprime@. This has been checked against the
-- tables of Feitsma and Galway
-- <http://www.cecm.sfu.ca/Pseudoprimes/index-2-to-64.html> and thus
-- constitutes a check for primality (rather than just pseudoprimality) up
-- to \(2^{64}\).
-- 
-- In future, this test may produce and check a certificate of primality.
-- This is likely to be significantly slower for prime inputs.
foreign import ccall "ulong_extras.h n_is_prime"
  n_is_prime :: CULong -> IO CInt

-- | /n_is_strong_probabprime_precomp/ /n/ /npre/ /a/ /d/ 
--
-- Tests if \(n\) is a strong probable prime to the base \(a\). We require
-- that \(d\) is set to the largest odd factor of \(n - 1\) and @npre@ is a
-- precomputed inverse of \(n\) computed with @n_precompute_inverse@. We
-- also require that \(n < 2^{53}\), \(a\) to be reduced modulo \(n\) and
-- not \(0\) and \(n\) to be odd.
-- 
-- If we write \(n - 1 = 2^s d\) where \(d\) is odd then \(n\) is a strong
-- probable prime to the base \(a\), i.e. an \(a\)-SPRP, if either
-- \(a^d = 1 \pmod n\) or \((a^d)^{2^r} = -1 \pmod n\) for some \(r\) less
-- than \(s\).
-- 
-- A description of strong probable primes is given here:
-- <https://mathworld.wolfram.com/StrongPseudoprime.html>
foreign import ccall "ulong_extras.h n_is_strong_probabprime_precomp"
  n_is_strong_probabprime_precomp :: CULong -> CDouble -> CULong -> CULong -> IO CInt

-- | /n_is_strong_probabprime2_preinv/ /n/ /ninv/ /a/ /d/ 
--
-- Tests if \(n\) is a strong probable prime to the base \(a\). We require
-- that \(d\) is set to the largest odd factor of \(n - 1\) and @npre@ is a
-- precomputed inverse of \(n\) computed with @n_preinvert_limb@. We
-- require a to be reduced modulo \(n\) and not \(0\) and \(n\) to be odd.
-- 
-- If we write \(n - 1 = 2^s d\) where \(d\) is odd then \(n\) is a strong
-- probable prime to the base \(a\) (an \(a\)-SPRP) if either
-- \(a^d = 1 \pmod n\) or \((a^d)^{2^r} = -1 \pmod n\) for some \(r\) less
-- than \(s\).
-- 
-- A description of strong probable primes is given here:
-- <https://mathworld.wolfram.com/StrongPseudoprime.html>
foreign import ccall "ulong_extras.h n_is_strong_probabprime2_preinv"
  n_is_strong_probabprime2_preinv :: CULong -> CULong -> CULong -> CULong -> IO CInt

-- | /n_is_probabprime_fermat/ /n/ /i/ 
--
-- Returns \(1\) if \(n\) is a base \(i\) Fermat probable prime. Requires
-- \(1 < i < n\) and that \(i\) does not divide \(n\).
-- 
-- By Fermat\'s Little Theorem if \(i^{n-1}\) is not congruent to \(1\)
-- then \(n\) is not prime.
foreign import ccall "ulong_extras.h n_is_probabprime_fermat"
  n_is_probabprime_fermat :: CULong -> CULong -> IO CInt

-- | /n_is_probabprime_fibonacci/ /n/ 
--
-- Let \(F_j\) be the \(j\)th element of the Fibonacci sequence
-- \(0, 1, 1, 2, 3, 5, \dotsc\), starting at \(j = 0\). Then if \(n\) is
-- prime we have \(F_{n - (n/5)} = 0 \pmod n\), where \((n/5)\) is the
-- Jacobi symbol.
-- 
-- For further details, see pp. 142 < [CraPom2005]>.
-- 
-- We require that \(n\) is not divisible by \(2\) or \(5\).
foreign import ccall "ulong_extras.h n_is_probabprime_fibonacci"
  n_is_probabprime_fibonacci :: CULong -> IO CInt

-- | /n_is_probabprime_BPSW/ /n/ 
--
-- Implements a Baillie--Pomerance--Selfridge--Wagstaff probable primality
-- test. This is a variant of the usual BPSW test (which only uses strong
-- base-2 probable prime and Lucas-Selfridge tests, see Baillie and
-- Wagstaff < [BaiWag1980]>).
-- 
-- This implementation makes use of a weakening of the usual Baillie-PSW
-- test given in < [Chen2003]>, namely replacing the Lucas test with a
-- Fibonacci test when \(n \equiv 2, 3 \pmod{5}\) (see also the comment on
-- page 143 of < [CraPom2005]>), regarding Fibonacci pseudoprimes.
-- 
-- There are no known counterexamples to this being a primality test.
-- 
-- Up to \(2^{64}\) the test we use has been checked against tables of
-- pseudoprimes. Thus it is a primality test up to this limit.
foreign import ccall "ulong_extras.h n_is_probabprime_BPSW"
  n_is_probabprime_BPSW :: CULong -> IO CInt

-- | /n_is_probabprime_lucas/ /n/ 
--
-- For details on Lucas pseudoprimes, see [pp. 143] < [CraPom2005]>.
-- 
-- We implement a variant of the Lucas pseudoprime test similar to that
-- described by Baillie and Wagstaff < [BaiWag1980]>.
foreign import ccall "ulong_extras.h n_is_probabprime_lucas"
  n_is_probabprime_lucas :: CULong -> IO CInt

-- | /n_is_probabprime/ /n/ 
--
-- Tests if \(n\) is a probable prime. Up to @FLINT_ODDPRIME_SMALL_CUTOFF@
-- this algorithm uses @n_is_oddprime_small@ which uses a lookup table.
-- 
-- Next it calls @n_compute_primes@ with the maximum table size and uses
-- this table to perform a binary search for \(n\) up to the table limit.
-- 
-- Then up to \(1050535501\) it uses a number of strong probable prime
-- tests, @n_is_strong_probabprime_preinv@, etc., for various bases. The
-- output of the algorithm is guaranteed to be correct up to this bound due
-- to exhaustive tables, described at
-- <http://uucode.com/obf/dalbec/alg.html> .
-- 
-- Beyond that point the BPSW probabilistic primality test is used, by
-- calling the function @n_is_probabprime_BPSW@. There are no known
-- counterexamples, and it has been checked against the tables of Feitsma
-- and Galway and up to the accuracy of those tables, this is an exhaustive
-- check up to \(2^{64}\), i.e. there are no counterexamples.
foreign import ccall "ulong_extras.h n_is_probabprime"
  n_is_probabprime :: CULong -> IO CInt

-- Chinese remaindering --------------------------------------------------------

-- | /n_CRT/ /r1/ /m1/ /r2/ /m2/ 
--
-- Use the Chinese Remainder Theorem to return the unique value
-- \(0 \le x < M\) congruent to \(r_1\) modulo \(m_1\) and \(r_2\) modulo
-- \(m_2\), where \(M = m_1 \times m_2\) is assumed to fit a ulong.
-- 
-- It is assumed that \(m_1\) and \(m_2\) are positive integers greater
-- than \(1\) and coprime. It is assumed that \(0 \le r_1 < m_1\) and
-- \(0 \le r_2 < m_2\).
foreign import ccall "ulong_extras.h n_CRT"
  n_CRT :: CULong -> CULong -> CULong -> CULong -> IO CULong

-- Square root and perfect power testing ---------------------------------------

-- | /n_sqrt/ /a/ 
--
-- Computes the integer truncation of the square root of \(a\).
-- 
-- The implementation uses a call to the IEEE floating point sqrt function.
-- The integer itself is represented by the nearest double and its square
-- root is computed to the nearest place. If \(a\) is one below a square,
-- the rounding may be up, whereas if it is one above a square, the
-- rounding will be down. Thus the square root may be one too large in some
-- instances which we then adjust by checking if we have the right value.
-- We also have to be careful when the square of this too large value
-- causes an overflow. The same assumptions hold for a single precision
-- float provided the square root itself can be represented in a single
-- float, i.e. for \(a < 281474976710656 = 2^{46}\).
foreign import ccall "ulong_extras.h n_sqrt"
  n_sqrt :: CULong -> IO CULong

-- | /n_sqrtrem/ /r/ /a/ 
--
-- Computes the integer truncation of the square root of \(a\).
-- 
-- The integer itself is represented by the nearest double and its square
-- root is computed to the nearest place. If \(a\) is one below a square,
-- the rounding may be up, whereas if it is one above a square, the
-- rounding will be down. Thus the square root may be one too large in some
-- instances which we then adjust by checking if we have the right value.
-- We also have to be careful when the square of this too large value
-- causes an overflow. The same assumptions hold for a single precision
-- float provided the square root itself can be represented in a single
-- float, i.e. for \(a < 281474976710656 = 2^{46}\).
-- 
-- The remainder is computed by subtracting the square of the computed
-- square root from \(a\).
foreign import ccall "ulong_extras.h n_sqrtrem"
  n_sqrtrem :: Ptr CULong -> CULong -> IO CULong

-- | /n_is_square/ /x/ 
--
-- Returns \(1\) if \(x\) is a square, otherwise \(0\).
-- 
-- This code first checks if \(x\) is a square modulo \(64\),
-- \(63 = 3 \times 3 \times 7\) and \(65 = 5 \times 13\), using lookup
-- tables, and if so it then takes a square root and checks that the square
-- of this equals the original value.
foreign import ccall "ulong_extras.h n_is_square"
  n_is_square :: CULong -> IO CInt

-- | /n_is_perfect_power235/ /n/ 
--
-- Returns \(1\) if \(n\) is a perfect square, cube or fifth power.
-- 
-- This function uses a series of modular tests to reject most non
-- 235-powers. Each modular test returns a value from 0 to 7 whose bits
-- respectively indicate whether the value is a square, cube or fifth power
-- modulo the given modulus. When these are logically @AND@-ed together,
-- this gives a powerful test which will reject most non-235 powers.
-- 
-- If a bit remains set indicating it may be a square, a standard square
-- root test is performed. Similarly a cube root or fifth root can be
-- taken, if indicated, to determine whether the power of that root is
-- exactly equal to \(n\).
foreign import ccall "ulong_extras.h n_is_perfect_power235"
  n_is_perfect_power235 :: CULong -> IO CInt

-- | /n_is_perfect_power/ /root/ /n/ 
--
-- If \(n = r^k\), return \(k\) and set @root@ to \(r\). Note that \(0\)
-- and \(1\) are considered squares. No guarantees are made about \(r\) or
-- \(k\) being the minimum possible value.
foreign import ccall "ulong_extras.h n_is_perfect_power"
  n_is_perfect_power :: Ptr CULong -> CULong -> IO CInt

-- | /n_rootrem/ /remainder/ /n/ /root/ 
--
-- This function uses the Newton iteration method to calculate the nth root
-- of a number. First approximation is calculated by an algorithm mentioned
-- in this article:
-- <https://en.wikipedia.org/wiki/Fast_inverse_square_root> . Instead of
-- the inverse square root, the nth root is calculated.
-- 
-- Returns the integer part of @n ^ 1\/root@. Remainder is set as
-- @n - base^root@. In case \(n < 1\) or @root \< 1@, \(0\) is returned.
foreign import ccall "ulong_extras.h n_rootrem"
  n_rootrem :: Ptr CULong -> CULong -> CULong -> IO CULong

-- | /n_cbrt/ /n/ 
--
-- This function returns the integer truncation of the cube root of \(n\).
-- First approximation is calculated by an algorithm mentioned in this
-- article: <https://en.wikipedia.org/wiki/Fast_inverse_square_root> .
-- Instead of the inverse square root, the cube root is calculated. This
-- functions uses different algorithms to calculate the cube root,
-- depending upon the size of \(n\). For numbers greater than \(2^{46}\),
-- it uses @n_cbrt_chebyshev_approx@. Otherwise, it makes use of the
-- iteration,
-- \(x \leftarrow x - (x\cdot x\cdot x - a)\cdot x/(2\cdot x\cdot x\cdot x + a)\)
-- for getting a good estimate, as mentioned in the paper by W. Kahan
-- < [Kahan1991]> .
foreign import ccall "ulong_extras.h n_cbrt"
  n_cbrt :: CULong -> IO CULong

-- | /n_cbrt_newton_iteration/ /n/ 
--
-- This function returns the integer truncation of the cube root of \(n\).
-- Makes use of Newton iterations to get a close value, and then adjusts
-- the estimate so as to get the correct value.
foreign import ccall "ulong_extras.h n_cbrt_newton_iteration"
  n_cbrt_newton_iteration :: CULong -> IO CULong

-- | /n_cbrt_binary_search/ /n/ 
--
-- This function returns the integer truncation of the cube root of \(n\).
-- Uses binary search to get the correct value.
foreign import ccall "ulong_extras.h n_cbrt_binary_search"
  n_cbrt_binary_search :: CULong -> IO CULong

-- | /n_cbrt_chebyshev_approx/ /n/ 
--
-- This function returns the integer truncation of the cube root of \(n\).
-- The number is first expressed in the form @x * 2^exp@. This ensures
-- \(x\) is in the range [0.5, 1]. Cube root of x is calculated using
-- Chebyshev\'s approximation polynomial for the function \(y = x^{1/3}\).
-- The values of the coefficient are calculated from the Python module
-- mpmath, <https://mpmath.org>, using the function chebyfit. x is
-- multiplied by @2^exp@ and the cube root of 1, 2 or 4 (according to
-- @exp%3@).
foreign import ccall "ulong_extras.h n_cbrt_chebyshev_approx"
  n_cbrt_chebyshev_approx :: CULong -> IO CULong

-- | /n_cbrtrem/ /remainder/ /n/ 
--
-- This function returns the integer truncation of the cube root of \(n\).
-- Remainder is set as \(n\) minus the cube of the value returned.
foreign import ccall "ulong_extras.h n_cbrtrem"
  n_cbrtrem :: Ptr CULong -> CULong -> IO CULong

-- Factorisation ---------------------------------------------------------------

-- | /n_remove/ /n/ /p/ 
--
-- Removes the highest possible power of \(p\) from \(n\), replacing \(n\)
-- with the quotient. The return value is the highest power of \(p\) that
-- divided \(n\). Assumes \(n\) is not \(0\).
-- 
-- For \(p = 2\) trailing zeroes are counted. For other primes \(p\) is
-- repeatedly squared and stored in a table of powers with the current
-- highest power of \(p\) removed at each step until no higher power can be
-- removed. The algorithm then proceeds down the power tree again removing
-- powers of \(p\) until none remain.
foreign import ccall "ulong_extras.h n_remove"
  n_remove :: Ptr CULong -> CULong -> IO CInt

-- | /n_remove2_precomp/ /n/ /p/ /ppre/ 
--
-- Removes the highest possible power of \(p\) from \(n\), replacing \(n\)
-- with the quotient. The return value is the highest power of \(p\) that
-- divided \(n\). Assumes \(n\) is not \(0\). We require @ppre@ to be set
-- to a precomputed inverse of \(p\) computed with @n_precompute_inverse@.
-- 
-- For \(p = 2\) trailing zeroes are counted. For other primes \(p\) we
-- make repeated use of @n_divrem2_precomp@ until division by \(p\) is no
-- longer possible.
foreign import ccall "ulong_extras.h n_remove2_precomp"
  n_remove2_precomp :: Ptr CULong -> CULong -> CDouble -> IO CInt

foreign import ccall "ulong_extras.h n_factor_init"
  n_factor_init :: Ptr CNFactor -> IO ()

-- | /n_factor_insert/ /factors/ /p/ /exp/ 
--
-- Inserts the given prime power factor @p^exp@ into the @n_factor_t@
-- @factors@. See the documentation for @n_factor_trial@ for a description
-- of the @n_factor_t@ type.
-- 
-- The algorithm performs a simple search to see if \(p\) already exists as
-- a prime factor in the structure. If so the exponent there is increased
-- by the supplied exponent. Otherwise a new factor @p^exp@ is added to the
-- end of the structure.
-- 
-- There is no test code for this function other than its use by the
-- various factoring functions, which have test code.
foreign import ccall "ulong_extras.h n_factor_insert"
  n_factor_insert :: Ptr (Ptr CNFactor) -> CULong -> CULong -> IO ()

-- | /n_factor_trial_range/ /factors/ /n/ /start/ /num_primes/ 
--
-- Trial factor \(n\) with the first @num_primes@ primes, but starting at
-- the prime with index start (counting from zero).
-- 
-- One requires an initialised @n_factor_t@ structure, but factors will be
-- added by default to an already used @n_factor_t@. Use the function
-- @n_factor_init@ defined in @ulong_extras@ if initialisation has not
-- already been completed on factors.
-- 
-- Once completed, @num@ will contain the number of distinct prime factors
-- found. The field \(p\) is an array of @ulong@s containing the distinct
-- prime factors, @exp@ an array containing the corresponding exponents.
-- 
-- The return value is the unfactored cofactor after trial factoring is
-- done.
-- 
-- The function calls @n_compute_primes@ automatically. See the
-- documentation for that function regarding limits.
-- 
-- The algorithm stops when the current prime has a square exceeding \(n\),
-- as no prime factor of \(n\) can exceed this unless \(n\) is prime.
-- 
-- The precomputed inverses of all the primes computed by
-- @n_compute_primes@ are utilised with the @n_remove2_precomp@ function.
foreign import ccall "ulong_extras.h n_factor_trial_range"
  n_factor_trial_range :: Ptr (Ptr CNFactor) -> CULong -> CULong -> CULong -> IO CULong

-- | /n_factor_trial/ /factors/ /n/ /num_primes/ 
--
-- This function calls @n_factor_trial_range@, with the value of \(0\) for
-- @start@. By default this adds factors to an already existing
-- @n_factor_t@ or to a newly initialised one.
foreign import ccall "ulong_extras.h n_factor_trial"
  n_factor_trial :: Ptr (Ptr CNFactor) -> CULong -> CULong -> IO CULong

-- | /n_factor_power235/ /exp/ /n/ 
--
-- Returns \(0\) if \(n\) is not a perfect square, cube or fifth power.
-- Otherwise it returns the root and sets @exp@ to either \(2\), \(3\) or
-- \(5\) appropriately.
-- 
-- This function uses a series of modular tests to reject most non
-- 235-powers. Each modular test returns a value from 0 to 7 whose bits
-- respectively indicate whether the value is a square, cube or fifth power
-- modulo the given modulus. When these are logically @AND@-ed together,
-- this gives a powerful test which will reject most non-235 powers.
-- 
-- If a bit remains set indicating it may be a square, a standard square
-- root test is performed. Similarly a cube root or fifth root can be
-- taken, if indicated, to determine whether the power of that root is
-- exactly equal to \(n\).
foreign import ccall "ulong_extras.h n_factor_power235"
  n_factor_power235 :: Ptr CULong -> CULong -> IO CULong

-- | /n_factor_one_line/ /n/ /iters/ 
--
-- This implements Bill Hart\'s one line factoring algorithm < [Har2012]>.
-- It is a variant of Fermat\'s algorithm which cycles through a large
-- number of multipliers instead of incrementing the square root. It is
-- faster than SQUFOF for \(n\) less than about \(2^{40}\).
foreign import ccall "ulong_extras.h n_factor_one_line"
  n_factor_one_line :: CULong -> CULong -> IO CULong

-- | /n_factor_lehman/ /n/ 
--
-- Lehman\'s factoring algorithm. Currently works up to \(10^{16}\), but is
-- not particularly efficient and so is not used in the general factor
-- function. Always returns a factor of \(n\).
foreign import ccall "ulong_extras.h n_factor_lehman"
  n_factor_lehman :: CULong -> IO CULong

-- | /n_factor_SQUFOF/ /n/ /iters/ 
--
-- Attempts to split \(n\) using the given number of iterations of SQUFOF.
-- Simply set @iters@ to @WORD(0)@ for maximum persistence.
-- 
-- The version of SQUFOF implemented here is as described by Gower and
-- Wagstaff < [GowWag2008]>.
-- 
-- We start by trying SQUFOF directly on \(n\). If that fails we multiply
-- it by each of the primes in @flint_primes_small@ in turn. As this
-- multiplication may result in a two limb value we allow this in our
-- implementation of SQUFOF. As SQUFOF works with values about half the
-- size of \(n\) it only needs single limb arithmetic internally.
-- 
-- If SQUFOF fails to factor \(n\) we return \(0\), however with @iters@
-- large enough this should never happen.
foreign import ccall "ulong_extras.h n_factor_SQUFOF"
  n_factor_SQUFOF :: CULong -> CULong -> IO CULong

-- | /n_factor/ /factors/ /n/ /proved/ 
--
-- Factors \(n\) with no restrictions on \(n\). If the prime factors are
-- required to be checked with a primality test, one may set @proved@ to
-- \(1\), otherwise set it to \(0\), and they will only be probable primes.
-- NB: at the present there is no difference because the probable prime
-- tests have been exhaustively tested up to \(2^{64}\).
-- 
-- However, in future, this flag may produce and separately check a
-- primality certificate. This may be quite slow (and probably no less
-- reliable in practice).
-- 
-- For details on the @n_factor_t@ structure, see @n_factor_trial@.
-- 
-- This function first tries trial factoring with a number of primes
-- specified by the constant @FLINT_FACTOR_TRIAL_PRIMES@. If the cofactor
-- is \(1\) or prime the function returns with all the factors.
-- 
-- Otherwise, the cofactor is placed in the array @factor_arr@. Whilst
-- there are factors remaining in there which have not been split, the
-- algorithm continues. At each step each factor is first checked to
-- determine if it is a perfect power. If so it is replaced by the power
-- that has been found. Next if the factor is small enough and composite,
-- in particular, less than @FLINT_FACTOR_ONE_LINE_MAX@ then
-- @n_factor_one_line@ is called with @FLINT_FACTOR_ONE_LINE_ITERS@ to try
-- and split the factor. If that fails or the factor is too large for
-- @n_factor_one_line@ then @n_factor_SQUFOF@ is called, with
-- @FLINT_FACTOR_SQUFOF_ITERS@. If that fails an error results and the
-- program aborts. However this should not happen in practice.
foreign import ccall "ulong_extras.h n_factor"
  n_factor :: Ptr (Ptr CNFactor) -> CULong -> CInt -> IO ()

-- | /n_factor_trial_partial/ /factors/ /n/ /prod/ /num_primes/ /limit/ 
--
-- Attempts trial factoring of \(n\) with the first @num_primes primes@,
-- but stops when the product of prime factors so far exceeds @limit@.
-- 
-- One requires an initialised @n_factor_t@ structure, but factors will be
-- added by default to an already used @n_factor_t@. Use the function
-- @n_factor_init@ defined in @ulong_extras@ if initialisation has not
-- already been completed on @factors@.
-- 
-- Once completed, @num@ will contain the number of distinct prime factors
-- found. The field \(p\) is an array of @ulong@s containing the distinct
-- prime factors, @exp@ an array containing the corresponding exponents.
-- 
-- The return value is the unfactored cofactor after trial factoring is
-- done. The value @prod@ will be set to the product of the factors found.
-- 
-- The function calls @n_compute_primes@ automatically. See the
-- documentation for that function regarding limits.
-- 
-- The algorithm stops when the current prime has a square exceeding \(n\),
-- as no prime factor of \(n\) can exceed this unless \(n\) is prime.
-- 
-- The precomputed inverses of all the primes computed by
-- @n_compute_primes@ are utilised with the @n_remove2_precomp@ function.
foreign import ccall "ulong_extras.h n_factor_trial_partial"
  n_factor_trial_partial :: Ptr (Ptr CNFactor) -> CULong -> Ptr CULong -> CULong -> CULong -> IO CULong

-- | /n_factor_partial/ /factors/ /n/ /limit/ /proved/ 
--
-- Factors \(n\), but stops when the product of prime factors so far
-- exceeds @limit@.
-- 
-- One requires an initialised @n_factor_t@ structure, but factors will be
-- added by default to an already used @n_factor_t@. Use the function
-- @n_factor_init()@ defined in @ulong_extras@ if initialisation has not
-- already been completed on @factors@.
-- 
-- On exit, @num@ will contain the number of distinct prime factors found.
-- The field \(p\) is an array of @ulong@s containing the distinct prime
-- factors, @exp@ an array containing the corresponding exponents.
-- 
-- The return value is the unfactored cofactor after factoring is done.
-- 
-- The factors are proved prime if @proved@ is \(1\), otherwise they are
-- merely probably prime.
foreign import ccall "ulong_extras.h n_factor_partial"
  n_factor_partial :: Ptr (Ptr CNFactor) -> CULong -> CULong -> CInt -> IO CULong

-- | /n_factor_pp1/ /n/ /B1/ /c/ 
--
-- Factors \(n\) using Williams\' \(p + 1\) factoring algorithm, with prime
-- limit set to \(B1\). We require \(c\) to be set to a random value. Each
-- trial of the algorithm with a different value of \(c\) gives another
-- chance to factor \(n\), with roughly exponentially decreasing chance of
-- finding a missing factor. If \(p + 1\) (or \(p - 1\)) is not smooth for
-- any factor \(p\) of \(n\), the algorithm will never succeed. The value
-- \(c\) should be less than \(n\) and greater than \(2\).
-- 
-- If the algorithm succeeds, it returns the factor, otherwise it returns
-- \(0\) or \(1\) (the trivial factors modulo \(n\)).
foreign import ccall "ulong_extras.h n_factor_pp1"
  n_factor_pp1 :: CULong -> CULong -> CULong -> IO CULong

-- | /n_factor_pp1_wrapper/ /n/ 
--
-- A simple wrapper around @n_factor_pp1@ which works in the range
-- \(31\)-64 bits. Below this point, trial factoring will always succeed.
-- This function mainly exists for @n_factor@ and is tuned to minimise the
-- time for @n_factor@ on numbers that reach the @n_factor_pp1@ stage, i.e.
-- after trial factoring and one line factoring.
foreign import ccall "ulong_extras.h n_factor_pp1_wrapper"
  n_factor_pp1_wrapper :: CULong -> IO CULong

-- | /n_factor_pollard_brent_single/ /factor/ /n/ /ninv/ /ai/ /xi/ /normbits/ /max_iters/ 
--
-- Pollard Rho algorithm (with Brent modification) for integer
-- factorization. Assumes that the \(n\) is not prime. \(factor\) is set as
-- the factor if found. It is not assured that the factor found will be
-- prime. Does not compute the complete factorization, just one factor.
-- Returns 1 if factorization is successful (non trivial factor is found),
-- else returns 0. Assumes \(n\) is normalized (shifted by normbits bits),
-- and takes as input a precomputed inverse of \(n\) as computed by
-- @n_preinvert_limb@. \(ai\) and \(xi\) should also be shifted left by
-- \(normbits\).
-- 
-- \(ai\) is the constant of the polynomial used, \(xi\) is the initial
-- value. \(max\_iters\) is the number of iterations tried in process of
-- finding the cycle.
-- 
-- The algorithm used is a modification of the original Pollard Rho
-- algorithm, suggested by Richard Brent in the paper, available at
-- <https://maths-people.anu.edu.au/~brent/pd/rpb051i.pdf>
foreign import ccall "ulong_extras.h n_factor_pollard_brent_single"
  n_factor_pollard_brent_single :: Ptr CMpLimb -> CMpLimb -> CMpLimb -> CMpLimb -> CMpLimb -> CMpLimb -> CMpLimb -> IO CInt

-- | /n_factor_pollard_brent/ /factor/ /state/ /n_in/ /max_tries/ /max_iters/ 
--
-- Pollard Rho algorithm, modified as suggested by Richard Brent. Makes a
-- call to @n_factor_pollard_brent_single@. The input parameters ai and xi
-- for @n_factor_pollard_brent_single@ are selected at random.
-- 
-- If the algorithm fails to find a non trivial factor in one call, it
-- tries again (this time with a different set of random values). This
-- process is repeated a maximum of \(max\_tries\) times.
-- 
-- Assumes \(n\) is not prime. \(factor\) is set as the factor found, if
-- factorization is successful. In such a case, 1 is returned. Otherwise, 0
-- is returned. Factor discovered is not necessarily prime.
foreign import ccall "ulong_extras.h n_factor_pollard_brent"
  n_factor_pollard_brent :: Ptr CMpLimb -> Ptr CFRandState -> CMpLimb -> CMpLimb -> CMpLimb -> IO CInt

-- Arithmetic functions --------------------------------------------------------

-- | /n_moebius_mu/ /n/ 
--
-- Computes the Moebius function \(\mu(n)\), which is defined as
-- \(\mu(n) = 0\) if \(n\) has a prime factor of multiplicity greater than
-- \(1\), \(\mu(n) = -1\) if \(n\) has an odd number of distinct prime
-- factors, and \(\mu(n) = 1\) if \(n\) has an even number of distinct
-- prime factors. By convention, \(\mu(0) = 0\).
-- 
-- For even numbers, we use the identities \(\mu(4n) = 0\) and
-- \(\mu(2n) = - \mu(n)\). Odd numbers up to a cutoff are then looked up
-- from a precomputed table storing \(\mu(n) + 1\) in groups of two bits.
-- 
-- For larger \(n\), we first check if \(n\) is divisible by a small odd
-- square and otherwise call @n_factor()@ and count the factors.
foreign import ccall "ulong_extras.h n_moebius_mu"
  n_moebius_mu :: CULong -> IO CInt

-- | /n_moebius_mu_vec/ /mu/ /len/ 
--
-- Computes \(\mu(n)\) for @n = 0, 1, ..., len - 1@. This is done by
-- sieving over each prime in the range, flipping the sign of \(\mu(n)\)
-- for every multiple of a prime \(p\) and setting \(\mu(n) = 0\) for every
-- multiple of \(p^2\).
foreign import ccall "ulong_extras.h n_moebius_mu_vec"
  n_moebius_mu_vec :: Ptr CInt -> CULong -> IO ()

-- | /n_is_squarefree/ /n/ 
--
-- Returns \(0\) if \(n\) is divisible by some perfect square, and \(1\)
-- otherwise. This simply amounts to testing whether \(\mu(n) \neq 0\). As
-- special cases, \(1\) is considered squarefree and \(0\) is not
-- considered squarefree.
foreign import ccall "ulong_extras.h n_is_squarefree"
  n_is_squarefree :: CULong -> IO CInt

-- | /n_euler_phi/ /n/ 
--
-- Computes the Euler totient function \(\phi(n)\), counting the number of
-- positive integers less than or equal to \(n\) that are coprime to \(n\).
foreign import ccall "ulong_extras.h n_euler_phi"
  n_euler_phi :: CULong -> IO CULong

-- Factorials ------------------------------------------------------------------

-- | /n_factorial_fast_mod2_preinv/ /n/ /p/ /pinv/ 
--
-- Returns \(n! \bmod p\) given a precomputed inverse of \(p\) as computed
-- by @n_preinvert_limb@. \(p\) is not required to be a prime, but no
-- special optimisations are made for composite \(p\). Uses fast multipoint
-- evaluation, running in about \(O(n^{1/2})\) time.
foreign import ccall "ulong_extras.h n_factorial_fast_mod2_preinv"
  n_factorial_fast_mod2_preinv :: CULong -> CULong -> CULong -> IO CULong

-- | /n_factorial_mod2_preinv/ /n/ /p/ /pinv/ 
--
-- Returns \(n! \bmod p\) given a precomputed inverse of \(p\) as computed
-- by @n_preinvert_limb@. \(p\) is not required to be a prime, but no
-- special optimisations are made for composite \(p\).
-- 
-- Uses a lookup table for small \(n\), otherwise computes the product if
-- \(n\) is not too large, and calls the fast algorithm for extremely large
-- \(n\).
foreign import ccall "ulong_extras.h n_factorial_mod2_preinv"
  n_factorial_mod2_preinv :: CULong -> CULong -> CULong -> IO CULong

-- Primitive Roots and Discrete Logarithms -------------------------------------

-- | /n_primitive_root_prime_prefactor/ /p/ /factors/ 
--
-- Returns a primitive root for the multiplicative subgroup of
-- \(\mathbb{Z}/p\mathbb{Z}\) where \(p\) is prime given the factorisation
-- (@factors@) of \(p - 1\).
foreign import ccall "ulong_extras.h n_primitive_root_prime_prefactor"
  n_primitive_root_prime_prefactor :: CULong -> Ptr (Ptr CNFactor) -> IO CULong

-- | /n_primitive_root_prime/ /p/ 
--
-- Returns a primitive root for the multiplicative subgroup of
-- \(\mathbb{Z}/p\mathbb{Z}\) where \(p\) is prime.
foreign import ccall "ulong_extras.h n_primitive_root_prime"
  n_primitive_root_prime :: CULong -> IO CULong

-- | /n_discrete_log_bsgs/ /b/ /a/ /n/ 
--
-- Returns the discrete logarithm of \(b\) with respect to \(a\) in the
-- multiplicative subgroup of \(\mathbb{Z}/n\mathbb{Z}\) when
-- \(\mathbb{Z}/n\mathbb{Z}\) is cyclic. That is, it returns a number \(x\)
-- such that \(a^x = b \bmod n\). The multiplicative subgroup is only
-- cyclic when \(n\) is \(2\), \(4\), \(p^k\), or \(2p^k\) where \(p\) is
-- an odd prime and \(k\) is a positive integer.
foreign import ccall "ulong_extras.h n_discrete_log_bsgs"
  n_discrete_log_bsgs :: CULong -> CULong -> CULong -> IO CULong

-- Elliptic curve method for factorization of @mp_limb_t@ ----------------------
  
-- | /n_factor_ecm_double/ /x/ /z/ /x0/ /z0/ /n/ /n_ecm_inf/ 
--
-- Sets the point \((x : z)\) to two times \((x_0 : z_0)\) modulo \(n\)
-- according to the formula
-- 
-- \(x = (x_0 + z_0)^2 \cdot (x_0 - z_0)^2 \mod n,\)
-- 
-- \(z = 4 x_0 z_0 \left((x_0 - z_0)^2 + 4a_{24}x_0z_0\right) \mod n.\)
-- 
-- This group doubling is valid only for points expressed in Montgomery
-- projective coordinates.
foreign import ccall "ulong_extras.h n_factor_ecm_double"
  n_factor_ecm_double :: Ptr CMpLimb -> Ptr CMpLimb -> CMpLimb -> CMpLimb -> CMpLimb -> Ptr CNEcm -> IO ()

-- | /n_factor_ecm_add/ /x/ /z/ /x1/ /z1/ /x2/ /z2/ /x0/ /z0/ /n/ /n_ecm_inf/ 
--
-- Sets the point \((x : z)\) to the sum of \((x_1 : z_1)\) and
-- \((x_2 : z_2)\) modulo \(n\), given the difference \((x_0 : z_0)\)
-- according to the formula
-- 
-- This group doubling is valid only for points expressed in Montgomery
-- projective coordinates.
foreign import ccall "ulong_extras.h n_factor_ecm_add"
  n_factor_ecm_add :: Ptr CMpLimb -> Ptr CMpLimb -> CMpLimb -> CMpLimb -> CMpLimb -> CMpLimb -> CMpLimb -> CMpLimb -> CMpLimb -> Ptr CNEcm -> IO ()

-- | /n_factor_ecm_mul_montgomery_ladder/ /x/ /z/ /x0/ /z0/ /k/ /n/ /n_ecm_inf/ 
--
-- Montgomery ladder algorithm for scalar multiplication of elliptic
-- points.
-- 
-- Sets the point \((x : z)\) to \(k(x_0 : z_0)\) modulo \(n\).
-- 
-- Valid only for points expressed in Montgomery projective coordinates.
foreign import ccall "ulong_extras.h n_factor_ecm_mul_montgomery_ladder"
  n_factor_ecm_mul_montgomery_ladder :: Ptr CMpLimb -> Ptr CMpLimb -> CMpLimb -> CMpLimb -> CMpLimb -> CMpLimb -> Ptr CNEcm -> IO ()

-- | /n_factor_ecm_select_curve/ /f/ /sigma/ /n/ /n_ecm_inf/ 
--
-- Selects a random elliptic curve given a random integer @sigma@,
-- according to Suyama\'s parameterization. If the factor is found while
-- selecting the curve, \(1\) is returned. In case the curve found is not
-- suitable, \(0\) is returned.
-- 
-- Also selects the initial point \(x_0\), and the value of \((a + 2)/4\),
-- where \(a\) is a curve parameter. Sets \(z_0\) as \(1\) (shifted left by
-- @n_ecm_inf->normbits@). All these are stored in the @n_ecm_t@ struct.
-- 
-- The curve selected is of Montgomery form, the points selected satisfy
-- the curve and are projective coordinates.
foreign import ccall "ulong_extras.h n_factor_ecm_select_curve"
  n_factor_ecm_select_curve :: Ptr CMpLimb -> CMpLimb -> CMpLimb -> Ptr CNEcm -> IO CInt

-- | /n_factor_ecm_stage_I/ /f/ /prime_array/ /num/ /B1/ /n/ /n_ecm_inf/ 
--
-- Stage I implementation of the ECM algorithm.
-- 
-- @f@ is set as the factor if found. @num@ is number of prime numbers
-- \(<=\) the bound @B1@. @prime_array@ is an array of first @B1@ primes.
-- \(n\) is the number being factored.
-- 
-- If the factor is found, \(1\) is returned, otherwise \(0\).
foreign import ccall "ulong_extras.h n_factor_ecm_stage_I"
  n_factor_ecm_stage_I :: Ptr CMpLimb -> Ptr CMpLimb -> CMpLimb -> CMpLimb -> CMpLimb -> Ptr CNEcm -> IO CInt

-- | /n_factor_ecm_stage_II/ /f/ /B1/ /B2/ /P/ /n/ /n_ecm_inf/ 
--
-- Stage II implementation of the ECM algorithm.
-- 
-- @f@ is set as the factor if found. @B1@, @B2@ are the two bounds. @P@ is
-- the primorial (approximately equal to \(\sqrt{B2}\)). \(n\) is the
-- number being factored.
-- 
-- If the factor is found, \(1\) is returned, otherwise \(0\).
foreign import ccall "ulong_extras.h n_factor_ecm_stage_II"
  n_factor_ecm_stage_II :: Ptr CMpLimb -> CMpLimb -> CMpLimb -> CMpLimb -> CMpLimb -> Ptr CNEcm -> IO CInt

-- | /n_factor_ecm/ /f/ /curves/ /B1/ /B2/ /state/ /n/ 
--
-- Outer wrapper function for the ECM algorithm. It factors \(n\) which
-- must fit into a @mp_limb_t@.
-- 
-- The function calls stage I and II, and the precomputations (builds
-- @prime_array@ for stage I, @GCD_table@ and @prime_table@ for stage II).
-- 
-- @f@ is set as the factor if found. @curves@ is the number of random
-- curves being tried. @B1@, @B2@ are the two bounds or stage I and stage
-- II. \(n\) is the number being factored.
-- 
-- If a factor is found in stage I, \(1\) is returned. If a factor is found
-- in stage II, \(2\) is returned. If a factor is found while selecting the
-- curve, \(-1\) is returned. Otherwise \(0\) is returned.
foreign import ccall "ulong_extras.h n_factor_ecm"
  n_factor_ecm :: Ptr CMpLimb -> CMpLimb -> CMpLimb -> CMpLimb -> Ptr CFRandState -> CMpLimb -> IO CInt

