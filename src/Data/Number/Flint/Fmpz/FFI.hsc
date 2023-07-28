{-|
module      :  Data.Number.Flint.Fmpz.FFI
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de
-}
module Data.Number.Flint.Fmpz.FFI (
  -- * Integers @Fmpz@
    Fmpz
  , CFmpz
  -- * Constructors
  , newFmpz
  , withFmpz
  , withNewFmpz
  -- * Precomputed inverse
  , FmpzPreInvN (..)
  , CFmpzPreInvN (..)
  -- * Factorization structure @FmpzFactor@
  , FmpzFactor (..)
  , CFmpzFactor (..)
  -- * Memory management mpz
  , _fmpz_new_mpz
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
  -- * Random generation
  , fmpz_randbits
  , fmpz_randtest
  , fmpz_randtest_unsigned
  , fmpz_randtest_not_zero
  , fmpz_randm
  , fmpz_randtest_mod
  , fmpz_randtest_mod_signed
  , fmpz_randprime
  -- * Conversion
  , fmpz_get_si
  , fmpz_get_ui
  , fmpz_get_uiui
  , fmpz_get_nmod
  , fmpz_get_d
  , fmpz_set_mpf
  , fmpz_get_mpf
  , fmpz_get_mpfr
  , fmpz_get_d_2exp
  , fmpz_get_mpz
  , fmpz_get_mpn
  , fmpz_get_str
  , fmpz_set_si
  , fmpz_set_ui
  , fmpz_set_d
  , fmpz_set_d_2exp
  , fmpz_neg_ui
  , fmpz_set_uiui
  , fmpz_neg_uiui
  , fmpz_set_signed_uiui
  , fmpz_set_signed_uiuiui
  , fmpz_set_ui_array
  , fmpz_set_signed_ui_array
  , fmpz_get_ui_array
  , fmpz_get_signed_ui_array
  , fmpz_get_signed_uiui
  , fmpz_set_mpz
  , fmpz_set_str
  , fmpz_set_ui_smod
  , flint_mpz_init_set_readonly
  , flint_mpz_clear_readonly
  , fmpz_init_set_readonly
  , fmpz_clear_readonly
  -- * Input and output
  , fmpz_read
  , fmpz_fread
  , fmpz_inp_raw
  , fmpz_print
  , fmpz_fprint
  , fmpz_out_raw
  -- * Basic properties and manipulation
  , fmpz_sizeinbase
  , fmpz_bits
  , fmpz_size
  , fmpz_sgn
  , fmpz_val2
  , fmpz_swap
  , fmpz_set
  , fmpz_zero
  , fmpz_one
  , fmpz_abs_fits_ui
  , fmpz_fits_si
  , fmpz_setbit
  , fmpz_tstbit
  , fmpz_abs_lbound_ui_2exp
  , fmpz_abs_ubound_ui_2exp
  -- * Comparison
  , fmpz_cmp
  , fmpz_cmp_ui
  , fmpz_cmp_si
  , fmpz_cmpabs
  , fmpz_cmp2abs
  , fmpz_equal
  , fmpz_equal_ui
  , fmpz_equal_si
  , fmpz_is_zero
  , fmpz_is_one
  , fmpz_is_pm1
  , fmpz_is_even
  , fmpz_is_odd
  -- * Basic arithmetic
  , fmpz_neg
  , fmpz_abs
  , fmpz_add
  , fmpz_add_ui         
  , fmpz_add_si       
  , fmpz_sub
  , fmpz_sub_ui
  , fmpz_sub_si
  , fmpz_mul
  , fmpz_mul_ui
  , fmpz_mul_si
  , fmpz_mul2_uiui
  , fmpz_mul_2exp
  , fmpz_one_2exp
  , fmpz_addmul
  , fmpz_addmul_ui
  , fmpz_addmul_si
  , fmpz_submul
  , fmpz_submul_ui
  , fmpz_submul_si
  , fmpz_fmma
  , fmpz_fmms
  , fmpz_cdiv_qr
  , fmpz_fdiv_qr
  , fmpz_tdiv_qr
  , fmpz_ndiv_qr
  , fmpz_cdiv_q
  , fmpz_fdiv_q
  , fmpz_tdiv_q
  , fmpz_cdiv_q_si
  , fmpz_fdiv_q_si
  , fmpz_tdiv_q_si
  , fmpz_cdiv_q_ui
  , fmpz_fdiv_q_ui
  , fmpz_tdiv_q_ui
  , fmpz_cdiv_q_2exp
  , fmpz_fdiv_q_2exp
  , fmpz_tdiv_q_2exp
  , fmpz_fdiv_r
  , fmpz_cdiv_r_2exp
  , fmpz_fdiv_r_2exp
  , fmpz_tdiv_r_2exp
  , fmpz_cdiv_ui
  , fmpz_fdiv_ui
  , fmpz_tdiv_ui
  , fmpz_divexact
  , fmpz_divexact_si
  , fmpz_divexact_ui
  , fmpz_divexact2_uiui
  , fmpz_divisible
  , fmpz_divisible_si
  , fmpz_divides
  , fmpz_mod
  , fmpz_mod_ui
  , fmpz_smod
  , fmpz_preinvn_init
  , fmpz_preinvn_clear
  , fmpz_fdiv_qr_preinvn
  , fmpz_pow_ui
  , fmpz_pow_fmpz
  , fmpz_powm_ui
  , fmpz_powm
  , fmpz_clog
  , fmpz_flog
  , fmpz_dlog
  , fmpz_sqrtmod
  , fmpz_sqrt
  , fmpz_sqrtrem
  , fmpz_is_square
  , fmpz_root
  , fmpz_is_perfect_power
  , fmpz_fac_ui
  , fmpz_fib_ui
  , fmpz_bin_uiui
  , _fmpz_rfac_ui
  , fmpz_rfac_ui
  , fmpz_rfac_uiui
  , fmpz_mul_tdiv_q_2exp
  , fmpz_mul_si_tdiv_q_2exp
  -- * Greatest common divisor
  , fmpz_gcd_ui
  , fmpz_gcd
  , fmpz_gcd3
  , fmpz_lcm
  , fmpz_gcdinv
  , fmpz_xgcd
  , fmpz_xgcd_canonical_bezout
  , fmpz_xgcd_partial
  -- * Modular arithmetic
  , _fmpz_remove
  , fmpz_remove
  , fmpz_invmod
  , fmpz_negmod
  , fmpz_jacobi
  , fmpz_kronecker
  , fmpz_divides_mod_list
  -- * Bit packing and unpacking
  , fmpz_bit_pack
  , fmpz_bit_unpack
  , fmpz_bit_unpack_unsigned
  -- * Logic Operations
  , fmpz_complement
  , fmpz_clrbit
  , fmpz_combit
  , fmpz_and
  , fmpz_or
  , fmpz_xor
  , fmpz_popcnt
  -- * Chinese remaindering
  , fmpz_CRT_ui
  , fmpz_CRT
  , fmpz_multi_mod_ui
  , fmpz_multi_CRT_ui
  -- ** Comb for multi CRT
  , FmpzComb (..)
  , CFmpzComb (..)
  , FmpzCombTemp (..)
  , CFmpzCombTemp (..)
  , newFmpzComb
  , withFmpzComb
  , fmpz_comb_init
  , newFmpzCombTemp
  , withFmpzCombTemp
  , fmpz_comb_temp_init
  , fmpz_comb_clear
  , fmpz_comb_temp_clear
  -- ** Multi CRT
  , FmpzMultiCRT (..)
  , CFmpzMultiCRT(..)
  , newFmpzMultiCRT
  , withFmpzMultiCRT
  , fmpz_multi_CRT_init
  , fmpz_multi_CRT_precompute
  , fmpz_multi_CRT_precomp
  , fmpz_multi_CRT
  , fmpz_multi_CRT_clear
  -- * Primality testing
  , fmpz_is_strong_probabprime
  , fmpz_is_probabprime_lucas
  , fmpz_is_probabprime_BPSW
  , fmpz_is_probabprime
  , fmpz_is_prime_pseudosquare
  , fmpz_is_prime_pocklington
  , _fmpz_nm1_trial_factors
  , fmpz_is_prime_morrison
  , _fmpz_np1_trial_factors
  , fmpz_is_prime
  , fmpz_lucas_chain
  , fmpz_lucas_chain_full
  , fmpz_lucas_chain_double
  , fmpz_lucas_chain_add
  , fmpz_lucas_chain_mul
  , fmpz_lucas_chain_VtoU
  , fmpz_divisor_in_residue_class_lenstra
  , fmpz_nextprime
  -- * Special functions
  , fmpz_primorial
  , fmpz_factor_euler_phi
  , fmpz_euler_phi
  , fmpz_factor_moebius_mu
  , fmpz_moebius_mu
  , fmpz_factor_divisor_sigma
  , fmpz_divisor_sigma
) where

-- Integers --------------------------------------------------------------------

import System.IO.Unsafe

import Control.Monad

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr, nullPtr, castPtr )
import Foreign.Storable
import Foreign.Marshal ( free )

import Data.Int ( Int64 )
import Data.Bits
import Data.Functor ((<&>))

import Data.Number.Flint.Flint
import Data.Number.Flint.NMod
import Data.Number.Flint.NMod.Types

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

-- fmpz_preinv_t --------------------------------------------------

-- | Data structure containing the /CFmpz/ pointer
data FmpzPreInvN = FmpzPreInvN {-# UNPACK #-} !(ForeignPtr CFmpzPreInvN) 
type CFmpzPreInvN = CFlint FmpzPreInvN 

-- fmpz_comb_t -----------------------------------------------------------------

-- | Data structure containing /CFmpzComb/ pointer
data FmpzComb = FmpzComb {-# UNPACK #-} !(ForeignPtr CFmpzComb)
type CFmpzComb = CFlint FmpzComb

instance Storable CFmpzComb where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fmpz_comb_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fmpz_comb_t}
  peek = error "CFmpzComb.peek: Not defined"
  poke = error "CFmpzComb.poke: Not defined"

-- fmpz_comb_temp_t ------------------------------------------------------------

-- | Data structure containing /CFmpzCombTemp/ pointer
data FmpzCombTemp = FmpzCombTemp {-# UNPACK #-} !(ForeignPtr CFmpzCombTemp)
type CFmpzCombTemp = CFlint FmpzCombTemp

instance Storable CFmpzCombTemp where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fmpz_comb_temp_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fmpz_comb_temp_t}
  peek = error "CFmpzCombTemp.peek: Not defined"
  poke = error "CFmpzCombTemp.poke: Not defined"

-- fmpz_multi_crt_t ------------------------------------------------------------

-- | Data structure containing /CFmpzMultiCRT/ pointer
data FmpzMultiCRT = FmpzMultiCRT {-# UNPACK #-} !(ForeignPtr CFmpzMultiCRT)
type CFmpzMultiCRT = CFlint FmpzMultiCRT

instance Storable CFmpzMultiCRT where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fmpz_multi_CRT_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fmpz_multi_CRT_t}
  peek = error "CFmpzMultiCRT.peek: Not defined"
  poke = error "CFmpzMultiCRT.poke: Not defined"

-- fmpz_factor_t ---------------------------------------------------------------

-- | Data structure containing /CFmpzFactor/ pointer
data FmpzFactor = FmpzFactor {-# UNPACK #-} !(ForeignPtr CFmpzFactor)
data CFmpzFactor = CFmpzFactor CInt (Ptr CFmpz) (Ptr CULong) CLong CLong

instance Storable CFmpzFactor where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fmpz_factor_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fmpz_factor_t}
  peek ptr = CFmpzFactor
    <$> #{peek fmpz_factor_struct, sign } ptr
    <*> #{peek fmpz_factor_struct, p    } ptr
    <*> #{peek fmpz_factor_struct, exp  } ptr
    <*> #{peek fmpz_factor_struct, alloc} ptr
    <*> #{peek fmpz_factor_struct, num  } ptr
  poke = error "CFmpzFactor.poke: Not defined"

-- Fmpz ------------------------------------------------------------------------

-- | /newFmpz/
--
-- Create a new `Fmpz`.
newFmpz = do
  x <- mallocForeignPtr
  withForeignPtr x fmpz_init
  addForeignPtrFinalizer p_fmpz_clear x
  return $ Fmpz x

-- | /withFmpz/ /x/ /f/
--
-- Apply /f/ to /x/.
{-# INLINE withFmpz #-}
withFmpz (Fmpz x) f = withForeignPtr x $ \xp -> f xp <&> (Fmpz x,)

-- | /withNewFmpz/ /f/
--
-- Apply /f/ to a new `Fmpz`.
{-# INLINE withNewFmpz #-}
withNewFmpz f = newFmpz >>= flip withFmpz f

--------------------------------------------------------------------------------

-- | /_fmpz_new_mpz/ 
-- 
-- initialises a new @mpz_t@ and returns a pointer to it. This is only used
-- internally.
foreign import ccall "fmpz.h _fmpz_new_mpz"
  _fmpz_new_mpz :: IO (Ptr CMpz)

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

foreign import ccall "p_fmpz_init"
  p_fmpz_init :: Ptr CFmpz -> IO ()

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

-- foreign import ccall "fmpz.h &fmpz_clear"
foreign import ccall "&p_fmpz_clear"
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

-- Random generation -----------------------------------------------------------

-- For thread-safety, the randomisation methods take as one of their
-- parameters an object of type @flint_rand_t@. Before calling any of the
-- randomisation functions such an object first has to be initialised with
-- a call to @flint_randinit@. When one is finished generating random
-- numbers, one should call @flint_randclear@ to clean up.
--
-- | /fmpz_randbits/ /f/ /state/ /bits/ 
-- 
-- Generates a random signed integer whose absolute value has precisely the
-- given number of bits.
foreign import ccall "fmpz.h fmpz_randbits"
  fmpz_randbits :: Ptr CFmpz -> Ptr CFRandState -> CFBitCnt -> IO ()

-- | /fmpz_randtest/ /f/ /state/ /bits/ 
-- 
-- Generates a random signed integer whose absolute value has a number of
-- bits which is random from \(0\) up to @bits@ inclusive.
foreign import ccall "fmpz.h fmpz_randtest"
  fmpz_randtest :: Ptr CFmpz -> Ptr CFRandState -> CFBitCnt -> IO ()

-- | /fmpz_randtest_unsigned/ /f/ /state/ /bits/ 
-- 
-- Generates a random unsigned integer whose value has a number of bits
-- which is random from \(0\) up to @bits@ inclusive.
foreign import ccall "fmpz.h fmpz_randtest_unsigned"
  fmpz_randtest_unsigned :: Ptr CFmpz -> Ptr CFRandState -> CFBitCnt -> IO ()

-- | /fmpz_randtest_not_zero/ /f/ /state/ /bits/ 
-- 
-- As per @fmpz_randtest@, but the result will not be \(0\). If @bits@ is
-- set to \(0\), an exception will result.
foreign import ccall "fmpz.h fmpz_randtest_not_zero"
  fmpz_randtest_not_zero :: Ptr CFmpz -> Ptr CFRandState -> CFBitCnt -> IO ()

-- | /fmpz_randm/ /f/ /state/ /m/ 
-- 
-- Generates a random integer in the range \(0\) to \(m - 1\) inclusive.
foreign import ccall "fmpz.h fmpz_randm"
  fmpz_randm :: Ptr CFmpz -> Ptr CFRandState -> Ptr CFmpz -> IO ()

-- | /fmpz_randtest_mod/ /f/ /state/ /m/ 
-- 
-- Generates a random integer in the range \(0\) to \(m - 1\) inclusive,
-- with an increased probability of generating values close to the
-- endpoints.
foreign import ccall "fmpz.h fmpz_randtest_mod"
  fmpz_randtest_mod :: Ptr CFmpz -> Ptr CFRandState -> Ptr CFmpz -> IO ()

-- | /fmpz_randtest_mod_signed/ /f/ /state/ /m/ 
-- 
-- Generates a random integer in the range \((-m/2, m/2]\), with an
-- increased probability of generating values close to the endpoints or
-- close to zero.
foreign import ccall "fmpz.h fmpz_randtest_mod_signed"
  fmpz_randtest_mod_signed :: Ptr CFmpz -> Ptr CFRandState -> Ptr CFmpz -> IO ()

-- | /fmpz_randprime/ /f/ /state/ /bits/ /proved/ 
-- 
-- Generates a random prime number with the given number of bits.
-- 
-- The generation is performed by choosing a random number and then finding
-- the next largest prime, and therefore does not quite give a uniform
-- distribution over the set of primes with that many bits.
-- 
-- Random number generation is performed using the standard Flint random
-- number generator, which is not suitable for cryptographic use.
-- 
-- If @proved@ is nonzero, then the integer returned is guaranteed to
-- actually be prime.
foreign import ccall "fmpz.h fmpz_randprime"
  fmpz_randprime :: Ptr CFmpz -> Ptr CFRandState -> CFBitCnt -> CInt -> IO ()

-- Conversion ------------------------------------------------------------------

-- | /fmpz_get_si/ /f/ 
-- 
-- Returns \(f\) as a @slong@. The result is undefined if \(f\) does not
-- fit into a @slong@.
foreign import ccall "fmpz.h fmpz_get_si"
  fmpz_get_si :: Ptr CFmpz -> IO CLong

-- | /fmpz_get_ui/ /f/ 
-- 
-- Returns \(f\) as an @ulong@. The result is undefined if \(f\) does not
-- fit into an @ulong@ or is negative.
foreign import ccall "fmpz.h fmpz_get_ui"
  fmpz_get_ui :: Ptr CFmpz -> IO CULong

-- | /fmpz_get_uiui/ /hi/ /low/ /f/ 
-- 
-- If \(f\) consists of two limbs, then @*hi@ and @*low@ are set to the
-- high and low limbs, otherwise @*low@ is set to the low limb and @*hi@ is
-- set to \(0\).
foreign import ccall "fmpz.h fmpz_get_uiui"
  fmpz_get_uiui :: Ptr CMpLimb -> Ptr CMpLimb -> Ptr CFmpz -> IO ()

-- | /fmpz_get_nmod/ /f/ /mod/ 
-- 
-- Returns \(f \mod n\).
foreign import ccall "fmpz.h fmpz_get_nmod"
  fmpz_get_nmod :: Ptr CFmpz -> Ptr CNMod -> IO CMpLimb

-- | /fmpz_get_d/ /f/ 
-- 
-- Returns \(f\) as a @double@, rounding down towards zero if \(f\) cannot
-- be represented exactly. The outcome is undefined if \(f\) is too large
-- to fit in the normal range of a double.
foreign import ccall "fmpz.h fmpz_get_d"
  fmpz_get_d :: Ptr CFmpz -> IO CDouble

-- | /fmpz_set_mpf/ /f/ /x/ 
-- 
-- Sets \(f\) to the @mpf_t@ \(x\), rounding down towards zero if the value
-- of \(x\) is fractional.
foreign import ccall "fmpz.h fmpz_set_mpf"
  fmpz_set_mpf :: Ptr CFmpz -> Ptr CMpf -> IO ()

-- | /fmpz_get_mpf/ /x/ /f/ 
-- 
-- Sets the value of the @mpf_t@ \(x\) to the value of \(f\).
foreign import ccall "fmpz.h fmpz_get_mpf"
  fmpz_get_mpf :: Ptr CMpf -> Ptr CFmpz -> IO ()

-- | /fmpz_get_mpfr/ /x/ /f/ /rnd/ 
-- 
-- Sets the value of \(x\) from \(f\), rounded toward the given direction
-- @rnd@.
foreign import ccall "fmpz.h fmpz_get_mpfr"
  fmpz_get_mpfr :: Ptr CMpfr -> Ptr CFmpz -> CMpfrRnd -> IO ()

-- | /fmpz_get_d_2exp/ /exp/ /f/ 
-- 
-- Returns \(f\) as a normalized @double@ along with a \(2\)-exponent
-- @exp@, i.e.if \(r\) is the return value then \(f = r 2^{exp}\), to
-- within 1 ULP.
foreign import ccall "fmpz.h fmpz_get_d_2exp"
  fmpz_get_d_2exp :: Ptr CLong -> Ptr CFmpz -> IO CDouble

-- | /fmpz_get_mpz/ /x/ /f/ 
-- 
-- Sets the @mpz_t@ \(x\) to the same value as \(f\).
foreign import ccall "fmpz.h fmpz_get_mpz"
  fmpz_get_mpz :: Ptr CMpz -> Ptr CFmpz -> IO ()

-- | /fmpz_get_mpn/ /n/ /n_in/ 
-- 
-- Sets the @mp_ptr@ \(n\) to the same value as \(n_{in}\). Returned
-- integer is number of limbs allocated to \(n\), minimum number of limbs
-- required to hold the value stored in \(n_{in}\).
foreign import ccall "fmpz.h fmpz_get_mpn"
  fmpz_get_mpn :: Ptr CMp -> Ptr CFmpz -> IO CInt

-- | /fmpz_get_str/ /str/ /b/ /f/ 
-- 
-- Returns the representation of \(f\) in base \(b\), which can vary
-- between \(2\) and \(62\), inclusive.
-- 
-- If @str@ is @NULL@, the result string is allocated by the function.
-- Otherwise, it is up to the caller to ensure that the allocated block of
-- memory is sufficiently large.
foreign import ccall "fmpz.h fmpz_get_str"
  fmpz_get_str :: CString -> CInt -> Ptr CFmpz -> IO CString

-- | /fmpz_set_si/ /f/ /val/ 
-- 
-- Sets \(f\) to the given @slong@ value.
foreign import ccall "fmpz.h fmpz_set_si"
  fmpz_set_si :: Ptr CFmpz -> CLong -> IO ()

-- | /fmpz_set_ui/ /f/ /val/ 
-- 
-- Sets \(f\) to the given @ulong@ value.
foreign import ccall "fmpz.h fmpz_set_ui"
  fmpz_set_ui :: Ptr CFmpz -> CULong -> IO ()

-- | /fmpz_set_d/ /f/ /c/ 
-- 
-- Sets \(f\) to the @double@ \(c\), rounding down towards zero if the
-- value of \(c\) is fractional. The outcome is undefined if \(c\) is
-- infinite, not-a-number, or subnormal.
foreign import ccall "fmpz.h fmpz_set_d"
  fmpz_set_d :: Ptr CFmpz -> CDouble -> IO ()

-- | /fmpz_set_d_2exp/ /f/ /d/ /exp/ 
-- 
-- Sets \(f\) to the nearest integer to \(d 2^{exp}\).
foreign import ccall "fmpz.h fmpz_set_d_2exp"
  fmpz_set_d_2exp :: Ptr CFmpz -> CDouble -> CLong -> IO ()

-- | /fmpz_neg_ui/ /f/ /val/ 
-- 
-- Sets \(f\) to the given @ulong@ value, and then negates \(f\).
foreign import ccall "fmpz.h fmpz_neg_ui"
  fmpz_neg_ui :: Ptr CFmpz -> CULong -> IO ()

-- | /fmpz_set_uiui/ /f/ /hi/ /lo/ 
-- 
-- Sets \(f\) to @lo@, plus @hi@ shifted to the left by @FLINT_BITS@.
foreign import ccall "fmpz.h fmpz_set_uiui"
  fmpz_set_uiui :: Ptr CFmpz -> CMpLimb -> CMpLimb -> IO ()

-- | /fmpz_neg_uiui/ /f/ /hi/ /lo/ 
-- 
-- Sets \(f\) to @lo@, plus @hi@ shifted to the left by @FLINT_BITS@, and
-- then negates \(f\).
foreign import ccall "fmpz.h fmpz_neg_uiui"
  fmpz_neg_uiui :: Ptr CFmpz -> CMpLimb -> CMpLimb -> IO ()

-- | /fmpz_set_signed_uiui/ /f/ /hi/ /lo/ 
-- 
-- Sets \(f\) to @lo@, plus @hi@ shifted to the left by @FLINT_BITS@,
-- interpreted as a signed two\'s complement integer with @2 * FLINT_BITS@
-- bits.
foreign import ccall "fmpz.h fmpz_set_signed_uiui"
  fmpz_set_signed_uiui :: Ptr CFmpz -> CULong -> CULong -> IO ()

-- | /fmpz_set_signed_uiuiui/ /f/ /hi/ /mid/ /lo/ 
-- 
-- Sets \(f\) to @lo@, plus @mid@ shifted to the left by @FLINT_BITS@, plus
-- @hi@ shifted to the left by @2*FLINT_BITS@ bits, interpreted as a signed
-- two\'s complement integer with @3 * FLINT_BITS@ bits.
foreign import ccall "fmpz.h fmpz_set_signed_uiuiui"
  fmpz_set_signed_uiuiui :: Ptr CFmpz -> CULong -> CULong -> CULong -> IO ()

-- | /fmpz_set_ui_array/ /out/ /in/ /n/ 
-- 
-- Sets @out@ to the nonnegative integer
-- @in[0] + in[1]*X  + ... + in[n - 1]*X^(n - 1)@ where @X = 2^FLINT_BITS@.
-- It is assumed that @n > 0@.
foreign import ccall "fmpz.h fmpz_set_ui_array"
  fmpz_set_ui_array :: Ptr CFmpz -> Ptr CULong -> CLong -> IO ()

-- | /fmpz_set_signed_ui_array/ /out/ /in/ /n/ 
-- 
-- Sets @out@ to the integer represented in @in[0], ..., in[n - 1]@ as a
-- signed two\'s complement integer with @n * FLINT_BITS@ bits. It is
-- assumed that @n > 0@. The function operates as a call to
-- @fmpz_set_ui_array@ followed by a symmetric remainder modulo
-- \(2^(n*FLINT\_BITS)\).
foreign import ccall "fmpz.h fmpz_set_signed_ui_array"
  fmpz_set_signed_ui_array :: Ptr CFmpz -> Ptr CULong -> CLong -> IO ()

-- | /fmpz_get_ui_array/ /out/ /n/ /in/ 
-- 
-- Assuming that the nonnegative integer @in@ can be represented in the
-- form @out[0] + out[1]*X + ... + out[n - 1]*X^(n - 1)@, where
-- \(X = 2^{FLINT\_BITS}\), sets the corresponding elements of @out@ so
-- that this is true. It is assumed that @n > 0@.
foreign import ccall "fmpz.h fmpz_get_ui_array"
  fmpz_get_ui_array :: Ptr CULong -> CLong -> Ptr CFmpz -> IO ()

-- | /fmpz_get_signed_ui_array/ /out/ /n/ /in/ 
-- 
-- Retrieves the value of \(in\) modulo \(2^{n * FLINT\_BITS}\) and puts
-- the \(n\) words of the result in @out[0], ..., out[n-1]@. This will give
-- a signed two\'s complement representation of \(in\) (assuming \(in\)
-- doesn\'t overflow the array).
foreign import ccall "fmpz.h fmpz_get_signed_ui_array"
  fmpz_get_signed_ui_array :: Ptr CULong -> CLong -> Ptr CFmpz -> IO ()

-- | /fmpz_get_signed_uiui/ /hi/ /lo/ /in/ 
-- 
-- Retrieves the value of \(in\) modulo \(2^{2 * FLINT\_BITS}\) and puts
-- the high and low words into @*hi@ and @*lo@ respectively.
foreign import ccall "fmpz.h fmpz_get_signed_uiui"
  fmpz_get_signed_uiui :: Ptr CULong -> Ptr CULong -> Ptr CFmpz -> IO ()

-- | /fmpz_set_mpz/ /f/ /x/ 
-- 
-- Sets \(f\) to the given @mpz_t@ value.
foreign import ccall "fmpz.h fmpz_set_mpz"
  fmpz_set_mpz :: Ptr CFmpz -> Ptr CMpz -> IO ()

-- | /fmpz_set_str/ /f/ /str/ /b/ 
-- 
-- Sets \(f\) to the value given in the null-terminated string @str@, in
-- base \(b\). The base \(b\) can vary between \(2\) and \(62\), inclusive.
-- Returns \(0\) if the string contains a valid input and \(-1\) otherwise.
foreign import ccall "fmpz.h fmpz_set_str"
  fmpz_set_str :: Ptr CFmpz -> CString -> CInt -> IO CInt

-- | /fmpz_set_ui_smod/ /f/ /x/ /m/ 
-- 
-- Sets \(f\) to the signed remainder \(y \equiv x \bmod m\) satisfying
-- \(-m/2 < y \leq m/2\), given \(x\) which is assumed to satisfy
-- \(0 \leq x < m\).
foreign import ccall "fmpz.h fmpz_set_ui_smod"
  fmpz_set_ui_smod :: Ptr CFmpz -> CMpLimb -> CMpLimb -> IO ()

-- | /flint_mpz_init_set_readonly/ /z/ /f/ 
-- 
-- Sets the uninitialised @mpz_t@ \(z\) to the value of the readonly
-- @fmpz_t@ \(f\).
-- 
-- Note that it is assumed that \(f\) does not change during the lifetime
-- of \(z\).
-- 
-- The integer \(z\) has to be cleared by a call to
-- @flint_mpz_clear_readonly@.
-- 
-- The suggested use of the two functions is as follows:
-- 
-- > fmpz_t f;
-- > ...
-- > {
-- >     mpz_t z;
-- >
-- >     flint_mpz_init_set_readonly(z, f);
-- >     foo(..., z);
-- >     flint_mpz_clear_readonly(z);
-- > }
-- 
-- This provides a convenient function for user code, only requiring to
-- work with the types @fmpz_t@ and @mpz_t@.
-- 
-- In critical code, the following approach may be favourable:
-- 
-- > fmpz_t f;
-- > ...
-- > {
-- >     __mpz_struct *z;
-- >
-- >     z = _fmpz_promote_val(f);
-- >     foo(..., z);
-- >     _fmpz_demote_val(f);
-- > }
foreign import ccall "fmpz.h flint_mpz_init_set_readonly"
  flint_mpz_init_set_readonly :: Ptr CMpz -> Ptr CFmpz -> IO ()

-- | /flint_mpz_clear_readonly/ /z/ 
-- 
-- Clears the readonly @mpz_t@ \(z\).
foreign import ccall "fmpz.h flint_mpz_clear_readonly"
  flint_mpz_clear_readonly :: Ptr CMpz -> IO ()

-- | /fmpz_init_set_readonly/ /f/ /z/ 
-- 
-- Sets the uninitialised @fmpz_t@ \(f\) to a readonly version of the
-- integer \(z\).
-- 
-- Note that the value of \(z\) is assumed to remain constant throughout
-- the lifetime of \(f\).
-- 
-- The @fmpz_t@ \(f\) has to be cleared by calling the function
-- @fmpz_clear_readonly@.
-- 
-- The suggested use of the two functions is as follows:
-- 
-- > mpz_t z;
-- > ...
-- > {
-- >     fmpz_t f;
-- >
-- >     fmpz_init_set_readonly(f, z);
-- >     foo(..., f);
-- >     fmpz_clear_readonly(f);
-- > }
foreign import ccall "fmpz.h fmpz_init_set_readonly"
  fmpz_init_set_readonly :: Ptr CFmpz -> Ptr CMpz -> IO ()

-- | /fmpz_clear_readonly/ /f/ 
-- 
-- Clears the readonly @fmpz_t@ \(f\).
foreign import ccall "fmpz.h fmpz_clear_readonly"
  fmpz_clear_readonly :: Ptr CFmpz -> IO ()

-- Input and output ------------------------------------------------------------

-- | /fmpz_read/ /f/ 
-- 
-- Reads a multiprecision integer from @stdin@. The format is an optional
-- minus sign, followed by one or more digits. The first digit should be
-- non-zero unless it is the only digit.
-- 
-- In case of success, returns a positive number. In case of failure,
-- returns a non-positive number.
-- 
-- This convention is adopted in light of the return values of @scanf@ from
-- the standard library and @mpz_inp_str@ from MPIR.
foreign import ccall "fmpz.h fmpz_read"
  fmpz_read :: Ptr CFmpz -> IO CInt

-- | /fmpz_fread/ /file/ /f/ 
-- 
-- Reads a multiprecision integer from the stream @file@. The format is an
-- optional minus sign, followed by one or more digits. The first digit
-- should be non-zero unless it is the only digit.
-- 
-- In case of success, returns a positive number. In case of failure,
-- returns a non-positive number.
-- 
-- This convention is adopted in light of the return values of @scanf@ from
-- the standard library and @mpz_inp_str@ from MPIR.
foreign import ccall "fmpz.h fmpz_fread"
  fmpz_fread :: Ptr CFile -> Ptr CFmpz -> IO CInt

-- | /fmpz_inp_raw/ /x/ /fin/ 
-- 
-- Reads a multiprecision integer from the stream @file@. The format is raw
-- binary format write by @fmpz_out_raw@.
-- 
-- In case of success, return a positive number, indicating number of bytes
-- read. In case of failure 0.
-- 
-- This function calls the @mpz_inp_raw@ function in library gmp. So that
-- it can read the raw data written by @mpz_inp_raw@ directly.
foreign import ccall "fmpz.h fmpz_inp_raw"
  fmpz_inp_raw :: Ptr CFmpz -> Ptr CFile -> IO (Ptr CSize)

-- | /fmpz_print/ /x/ 
-- 
-- Prints the value \(x\) to @stdout@, without a carriage return(CR). The
-- value is printed as either \(0\), the decimal digits of a positive
-- integer, or a minus sign followed by the digits of a negative integer.
-- 
-- In case of success, returns a positive number. In case of failure,
-- returns a non-positive number.
-- 
-- This convention is adopted in light of the return values of
-- @flint_printf@ from the standard library and @mpz_out_str@ from MPIR.
fmpz_print :: Ptr CFmpz -> IO CInt
fmpz_print x = printCStr (fmpz_get_str nullPtr 10) x

-- | /fmpz_fprint/ /file/ /x/ 
-- 
-- Prints the value \(x\) to @file@, without a carriage return(CR). The
-- value is printed as either \(0\), the decimal digits of a positive
-- integer, or a minus sign followed by the digits of a negative integer.
-- 
-- In case of success, returns a positive number. In case of failure,
-- returns a non-positive number.
-- 
-- This convention is adopted in light of the return values of
-- @flint_printf@ from the standard library and @mpz_out_str@ from MPIR.
foreign import ccall "fmpz.h fmpz_fprint"
  fmpz_fprint :: Ptr CFile -> Ptr CFmpz -> IO CInt

-- | /fmpz_out_raw/ /fout/ /x/ 
-- 
-- Writes the value \(x\) to @file@. The value is written in raw binary
-- format. The integer is written in portable format, with 4 bytes of size
-- information, and that many bytes of limbs. Both the size and the limbs
-- are written in decreasing significance order (i.e., in big-endian).
-- 
-- The output can be read with @fmpz_inp_raw@.
-- 
-- In case of success, return a positive number, indicating number of bytes
-- written. In case of failure, return 0.
-- 
-- The output of this can also be read by @mpz_inp_raw@ from GMP >= 2,
-- Since this function calls the @mpz_inp_raw@ function in library gmp.
foreign import ccall "fmpz.h fmpz_out_raw"
  fmpz_out_raw :: Ptr CFile -> Ptr CFmpz -> IO (Ptr CSize)

-- Basic properties and manipulation -------------------------------------------

-- | /fmpz_sizeinbase/ /f/ /b/ 
-- 
-- Returns the size of the absolute value of \(f\) in base \(b\), measured
-- in numbers of digits. The base \(b\) can be between \(2\) and \(62\),
-- inclusive.
foreign import ccall "fmpz.h fmpz_sizeinbase"
  fmpz_sizeinbase :: Ptr CFmpz -> CInt -> IO (Ptr CSize)

-- | /fmpz_bits/ /f/ 
-- 
-- Returns the number of bits required to store the absolute value of
-- \(f\). If \(f\) is \(0\) then \(0\) is returned.
foreign import ccall "fmpz.h fmpz_bits"
  fmpz_bits :: Ptr CFmpz -> IO CFBitCnt

-- | /fmpz_size/ /f/ 
-- 
-- Returns the number of limbs required to store the absolute value of
-- \(f\). If \(f\) is zero then \(0\) is returned.
foreign import ccall "fmpz.h fmpz_size"
  fmpz_size :: Ptr CFmpz -> IO CMpSize

-- | /fmpz_sgn/ /f/ 
-- 
-- Returns \(-1\) if the sign of \(f\) is negative, \(+1\) if it is
-- positive, otherwise returns \(0\).
foreign import ccall "fmpz.h fmpz_sgn"
  fmpz_sgn :: Ptr CFmpz -> IO CInt

-- | /fmpz_val2/ /f/ 
-- 
-- Returns the exponent of the largest power of two dividing \(f\), or
-- equivalently the number of trailing zeros in the binary expansion of
-- \(f\). If \(f\) is zero then \(0\) is returned.
foreign import ccall "fmpz.h fmpz_val2"
  fmpz_val2 :: Ptr CFmpz -> IO CFBitCnt

-- | /fmpz_swap/ /f/ /g/ 
-- 
-- Efficiently swaps \(f\) and \(g\). No data is copied.
foreign import ccall "fmpz.h fmpz_swap"
  fmpz_swap :: Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpz_set/ /f/ /g/ 
-- 
-- Sets \(f\) to the same value as \(g\).
foreign import ccall "fmpz.h fmpz_set"
  fmpz_set :: Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpz_zero/ /f/ 
-- 
-- Sets \(f\) to zero.
foreign import ccall "fmpz.h fmpz_zero"
  fmpz_zero :: Ptr CFmpz -> IO ()

-- | /fmpz_one/ /f/ 
-- 
-- Sets \(f\) to one.
foreign import ccall "fmpz.h fmpz_one"
  fmpz_one :: Ptr CFmpz -> IO ()

-- | /fmpz_abs_fits_ui/ /f/ 
-- 
-- Returns whether the absolute value of \(f\) fits into an @ulong@.
foreign import ccall "fmpz.h fmpz_abs_fits_ui"
  fmpz_abs_fits_ui :: Ptr CFmpz -> IO CInt

-- | /fmpz_fits_si/ /f/ 
-- 
-- Returns whether the value of \(f\) fits into a @slong@.
foreign import ccall "fmpz.h fmpz_fits_si"
  fmpz_fits_si :: Ptr CFmpz -> IO CInt

-- | /fmpz_setbit/ /f/ /i/ 
-- 
-- Sets bit index \(i\) of \(f\).
foreign import ccall "fmpz.h fmpz_setbit"
  fmpz_setbit :: Ptr CFmpz -> CULong -> IO ()

-- | /fmpz_tstbit/ /f/ /i/ 
-- 
-- Test bit index \(i\) of \(f\) and return \(0\) or \(1\), accordingly.
foreign import ccall "fmpz.h fmpz_tstbit"
  fmpz_tstbit :: Ptr CFmpz -> CULong -> IO CInt

-- | /fmpz_abs_lbound_ui_2exp/ /exp/ /x/ /bits/ 
-- 
-- For nonzero \(x\), returns a mantissa \(m\) with exactly @bits@ bits and
-- sets @exp@ to an exponent \(e\), such that \(|x| \ge m 2^e\). The number
-- of bits must be between 1 and @FLINT_BITS@ inclusive. The mantissa is
-- guaranteed to be correctly rounded.
foreign import ccall "fmpz.h fmpz_abs_lbound_ui_2exp"
  fmpz_abs_lbound_ui_2exp :: Ptr CLong -> Ptr CFmpz -> CInt -> IO CMpLimb

-- | /fmpz_abs_ubound_ui_2exp/ /exp/ /x/ /bits/ 
-- 
-- For nonzero \(x\), returns a mantissa \(m\) with exactly @bits@ bits and
-- sets @exp@ to an exponent \(e\), such that \(|x| \le m 2^e\). The number
-- of bits must be between 1 and @FLINT_BITS@ inclusive. The mantissa is
-- either correctly rounded or one unit too large (possibly meaning that
-- the exponent is one too large, if the mantissa is a power of two).
foreign import ccall "fmpz.h fmpz_abs_ubound_ui_2exp"
  fmpz_abs_ubound_ui_2exp :: Ptr CLong -> Ptr CFmpz -> CInt -> IO CMpLimb

-- Comparison ------------------------------------------------------------------

foreign import ccall "fmpz.h fmpz_cmp"
  fmpz_cmp :: Ptr CFmpz -> Ptr CFmpz -> IO CInt

foreign import ccall "fmpz.h fmpz_cmp_ui"
  fmpz_cmp_ui :: Ptr CFmpz -> CULong -> IO CInt

-- | /fmpz_cmp_si/ /f/ /g/ 
-- 
-- Returns a negative value if \(f < g\), positive value if \(g < f\),
-- otherwise returns \(0\).
foreign import ccall "fmpz.h fmpz_cmp_si"
  fmpz_cmp_si :: Ptr CFmpz -> CLong -> IO CInt

-- | /fmpz_cmpabs/ /f/ /g/ 
-- 
-- Returns a negative value if \(\lvert f\rvert < \lvert g\rvert\),
-- positive value if \(\lvert g\rvert < \lvert f \rvert\), otherwise
-- returns \(0\).
foreign import ccall "fmpz.h fmpz_cmpabs"
  fmpz_cmpabs :: Ptr CFmpz -> Ptr CFmpz -> IO CInt

-- | /fmpz_cmp2abs/ /f/ /g/ 
-- 
-- Returns a negative value if \(\lvert f\rvert < \lvert 2g\rvert\),
-- positive value if \(\lvert 2g\rvert < \lvert f \rvert\), otherwise
-- returns \(0\).
foreign import ccall "fmpz.h fmpz_cmp2abs"
  fmpz_cmp2abs :: Ptr CFmpz -> Ptr CFmpz -> IO CInt

foreign import ccall "fmpz.h fmpz_equal"
  fmpz_equal :: Ptr CFmpz -> Ptr CFmpz -> IO CInt

foreign import ccall "fmpz.h fmpz_equal_ui"
  fmpz_equal_ui :: Ptr CFmpz -> CULong -> IO CInt

-- | /fmpz_equal_si/ /f/ /g/ 
-- 
-- Returns \(1\) if \(f\) is equal to \(g\), otherwise returns \(0\).
foreign import ccall "fmpz.h fmpz_equal_si"
  fmpz_equal_si :: Ptr CFmpz -> CLong -> IO CInt

-- | /fmpz_is_zero/ /f/ 
-- 
-- Returns \(1\) if \(f\) is \(0\), otherwise returns \(0\).
foreign import ccall "fmpz.h fmpz_is_zero"
  fmpz_is_zero :: Ptr CFmpz -> IO CInt

-- | /fmpz_is_one/ /f/ 
-- 
-- Returns \(1\) if \(f\) is equal to one, otherwise returns \(0\).
foreign import ccall "fmpz.h fmpz_is_one"
  fmpz_is_one :: Ptr CFmpz -> IO CInt

-- | /fmpz_is_pm1/ /f/ 
-- 
-- Returns \(1\) if \(f\) is equal to one or minus one, otherwise returns
-- \(0\).
foreign import ccall "fmpz.h fmpz_is_pm1"
  fmpz_is_pm1 :: Ptr CFmpz -> IO CInt

-- | /fmpz_is_even/ /f/ 
-- 
-- Returns whether the integer \(f\) is even.
foreign import ccall "fmpz.h fmpz_is_even"
  fmpz_is_even :: Ptr CFmpz -> IO CInt

-- | /fmpz_is_odd/ /f/ 
-- 
-- Returns whether the integer \(f\) is odd.
foreign import ccall "fmpz.h fmpz_is_odd"
  fmpz_is_odd :: Ptr CFmpz -> IO CInt

-- Basic arithmetic ------------------------------------------------------------

-- | /fmpz_neg/ /f1/ /f2/ 
-- 
-- Sets \(f_1\) to \(-f_2\).
foreign import ccall "fmpz.h fmpz_neg"
  fmpz_neg :: Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpz_abs/ /f1/ /f2/ 
-- 
-- Sets \(f_1\) to the absolute value of \(f_2\).
foreign import ccall "fmpz.h fmpz_abs"
  fmpz_abs :: Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpz_add/ /f/ /g/ /h/ 
-- 
-- Sets \(f\) to \(g + h\).
foreign import ccall "fmpz.h fmpz_add"
  fmpz_add :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

foreign import ccall "fmpz.h fmpz_add_ui"
  fmpz_add_ui :: Ptr CFmpz -> Ptr CFmpz -> CULong -> IO ()

foreign import ccall "fmpz.h fmpz_add_si"
  fmpz_add_si :: Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- | /fmpz_sub/ /f/ /g/ /h/ 
-- 
-- Sets \(f\) to \(g - h\).
foreign import ccall "fmpz.h fmpz_sub"
  fmpz_sub :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

foreign import ccall "fmpz.h fmpz_sub_ui"
  fmpz_sub_ui :: Ptr CFmpz -> Ptr CFmpz -> CULong -> IO ()

foreign import ccall "fmpz.h fmpz_sub_si"
  fmpz_sub_si :: Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- | /fmpz_mul/ /f/ /g/ /h/ 
-- 
-- Sets \(f\) to \(g \times h\).
foreign import ccall "fmpz.h fmpz_mul"
  fmpz_mul :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

foreign import ccall "fmpz.h fmpz_mul_ui"
  fmpz_mul_ui :: Ptr CFmpz -> Ptr CFmpz -> CULong -> IO ()

foreign import ccall "fmpz.h fmpz_mul_si"
  fmpz_mul_si :: Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()
  
-- | /fmpz_mul2_uiui/ /f/ /g/ /x/ /y/ 
-- 
-- Sets \(f\) to \(g \times x \times y\) where \(x\) and \(y\) are of type
-- @ulong@.
foreign import ccall "fmpz.h fmpz_mul2_uiui"
  fmpz_mul2_uiui :: Ptr CFmpz -> Ptr CFmpz -> CULong -> CULong -> IO ()

-- | /fmpz_mul_2exp/ /f/ /g/ /e/ 
-- 
-- Sets \(f\) to \(g \times 2^e\).
-- 
-- Note: Assumes that @e + FLINT_BITS@ does not overflow.
foreign import ccall "fmpz.h fmpz_mul_2exp"
  fmpz_mul_2exp :: Ptr CFmpz -> Ptr CFmpz -> CULong -> IO ()

-- | /fmpz_one_2exp/ /f/ /e/ 
-- 
-- Sets \(f\) to \(2^e\).
foreign import ccall "fmpz.h fmpz_one_2exp"
  fmpz_one_2exp :: Ptr CFmpz -> CULong -> IO ()

-- | /fmpz_addmul/ /f/ /g/ /h/ 
-- 
-- Sets \(f\) to \(f + g \times h\).
foreign import ccall "fmpz.h fmpz_addmul"
  fmpz_addmul :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

foreign import ccall "fmpz.h fmpz_addmul_ui"
  fmpz_addmul_ui :: Ptr CFmpz -> Ptr CFmpz -> CULong -> IO ()

foreign import ccall "fmpz.h fmpz_addmul_si"
  fmpz_addmul_si :: Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- | /fmpz_submul/ /f/ /g/ /h/ 
-- 
-- Sets \(f\) to \(f - g \times h\).
foreign import ccall "fmpz.h fmpz_submul"
  fmpz_submul :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

foreign import ccall "fmpz.h fmpz_submul_ui"
  fmpz_submul_ui :: Ptr CFmpz -> Ptr CFmpz -> CULong -> IO ()

foreign import ccall "fmpz.h fmpz_submul_si"
  fmpz_submul_si :: Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- | /fmpz_fmma/ /f/ /a/ /b/ /c/ /d/ 
-- 
-- Sets \(f\) to \(a \times b + c \times d\).
foreign import ccall "fmpz.h fmpz_fmma"
  fmpz_fmma :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpz_fmms/ /f/ /a/ /b/ /c/ /d/ 
-- 
-- Sets \(f\) to \(a \times b - c \times d\).
foreign import ccall "fmpz.h fmpz_fmms"
  fmpz_fmms :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

foreign import ccall "fmpz.h fmpz_cdiv_qr"
  fmpz_cdiv_qr :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

foreign import ccall "fmpz.h fmpz_fdiv_qr"
  fmpz_fdiv_qr :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

foreign import ccall "fmpz.h fmpz_tdiv_qr"
  fmpz_tdiv_qr :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

foreign import ccall "fmpz.h fmpz_ndiv_qr"
  fmpz_ndiv_qr :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

foreign import ccall "fmpz.h fmpz_cdiv_q"
  fmpz_cdiv_q :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

foreign import ccall "fmpz.h fmpz_fdiv_q"
  fmpz_fdiv_q :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

foreign import ccall "fmpz.h fmpz_tdiv_q"
  fmpz_tdiv_q :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

foreign import ccall "fmpz.h fmpz_cdiv_q_si"
  fmpz_cdiv_q_si :: Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

foreign import ccall "fmpz.h fmpz_fdiv_q_si"
  fmpz_fdiv_q_si :: Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

foreign import ccall "fmpz.h fmpz_tdiv_q_si"
  fmpz_tdiv_q_si :: Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

foreign import ccall "fmpz.h fmpz_cdiv_q_ui"
  fmpz_cdiv_q_ui :: Ptr CFmpz -> Ptr CFmpz -> CULong -> IO ()

foreign import ccall "fmpz.h fmpz_fdiv_q_ui"
  fmpz_fdiv_q_ui :: Ptr CFmpz -> Ptr CFmpz -> CULong -> IO ()

foreign import ccall "fmpz.h fmpz_tdiv_q_ui"
  fmpz_tdiv_q_ui :: Ptr CFmpz -> Ptr CFmpz -> CULong -> IO ()

foreign import ccall "fmpz.h fmpz_cdiv_q_2exp"
  fmpz_cdiv_q_2exp :: Ptr CFmpz -> Ptr CFmpz -> CULong -> IO ()

foreign import ccall "fmpz.h fmpz_fdiv_q_2exp"
  fmpz_fdiv_q_2exp :: Ptr CFmpz -> Ptr CFmpz -> CULong -> IO ()

foreign import ccall "fmpz.h fmpz_tdiv_q_2exp"
  fmpz_tdiv_q_2exp :: Ptr CFmpz -> Ptr CFmpz -> CULong -> IO ()

foreign import ccall "fmpz.h fmpz_fdiv_r"
  fmpz_fdiv_r :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

foreign import ccall "fmpz.h fmpz_cdiv_r_2exp"
  fmpz_cdiv_r_2exp :: Ptr CFmpz -> Ptr CFmpz -> CULong -> IO ()

foreign import ccall "fmpz.h fmpz_fdiv_r_2exp"
  fmpz_fdiv_r_2exp :: Ptr CFmpz -> Ptr CFmpz -> CULong -> IO ()

-- | /fmpz_tdiv_r_2exp/ /s/ /g/ /exp/ 
-- 
-- Sets \(f\) to the quotient of \(g\) by \(h\) and\/or \(s\) to the
-- remainder. For the @2exp@ functions, @g = 2^exp@. \(If :math:`h\) is
-- \(0\) an exception is raised.
-- 
-- Rounding is made in the following way:
-- 
-- -   @fdiv@ rounds the quotient via floor rounding.
-- -   @cdiv@ rounds the quotient via ceil rounding.
-- -   @tdiv@ rounds the quotient via truncation, i.e. rounding towards
--     zero.
-- -   @ndiv@ rounds the quotient such that the remainder has the smallest
--     absolute value. In case of ties, it rounds the quotient towards
--     zero.
foreign import ccall "fmpz.h fmpz_tdiv_r_2exp"
  fmpz_tdiv_r_2exp :: Ptr CFmpz -> Ptr CFmpz -> CULong -> IO ()

foreign import ccall "fmpz.h fmpz_cdiv_ui"
  fmpz_cdiv_ui :: Ptr CFmpz -> CULong -> IO CULong

foreign import ccall "fmpz.h fmpz_fdiv_ui"
  fmpz_fdiv_ui :: Ptr CFmpz -> CULong -> IO CULong

-- | /fmpz_tdiv_ui/ /g/ /h/ 
-- 
-- Returns the absolute value remainder of \(g\) divided by \(h\),
-- following the convention of rounding as seen above. If \(h\) is zero an
-- exception is raised.
foreign import ccall "fmpz.h fmpz_tdiv_ui"
  fmpz_tdiv_ui :: Ptr CFmpz -> CULong -> IO CULong

foreign import ccall "fmpz.h fmpz_divexact"
  fmpz_divexact :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

foreign import ccall "fmpz.h fmpz_divexact_si"
  fmpz_divexact_si :: Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- | /fmpz_divexact_ui/ /f/ /g/ /h/ 
-- 
-- Sets \(f\) to the quotient of \(g\) and \(h\), assuming that the
-- division is exact, i.e.\(g\) is a multiple of \(h\). If \(h\) is \(0\)
-- an exception is raised.
foreign import ccall "fmpz.h fmpz_divexact_ui"
  fmpz_divexact_ui :: Ptr CFmpz -> Ptr CFmpz -> CULong -> IO ()

-- | /fmpz_divexact2_uiui/ /f/ /g/ /x/ /y/ 
-- 
-- Sets \(f\) to the quotient of \(g\) and \(h = x \times y\), assuming
-- that the division is exact, i.e.\(g\) is a multiple of \(h\). If \(x\)
-- or \(y\) is \(0\) an exception is raised.
foreign import ccall "fmpz.h fmpz_divexact2_uiui"
  fmpz_divexact2_uiui :: Ptr CFmpz -> Ptr CFmpz -> CULong -> CULong -> IO ()

foreign import ccall "fmpz.h fmpz_divisible"
  fmpz_divisible :: Ptr CFmpz -> Ptr CFmpz -> IO CInt

-- | /fmpz_divisible_si/ /f/ /g/ 
-- 
-- Returns \(1\) if there is an integer \(q\) with \(f = q g\) and \(0\) if
-- there is none.
foreign import ccall "fmpz.h fmpz_divisible_si"
  fmpz_divisible_si :: Ptr CFmpz -> CLong -> IO CInt

-- | /fmpz_divides/ /q/ /g/ /h/ 
-- 
-- Returns \(1\) if there is an integer \(q\) with \(f = q g\) and sets
-- \(q\) to the quotient. Otherwise returns \(0\) and sets \(q\) to \(0\).
foreign import ccall "fmpz.h fmpz_divides"
  fmpz_divides :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO CInt

-- | /fmpz_mod/ /f/ /g/ /h/ 
-- 
-- Sets \(f\) to the remainder of \(g\) divided by \(h\) such that the
-- remainder is positive. Assumes that \(h\) is not zero.
foreign import ccall "fmpz.h fmpz_mod"
  fmpz_mod :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_ui/ /f/ /g/ /h/ 
-- 
-- Sets \(f\) to the remainder of \(g\) divided by \(h\) such that the
-- remainder is positive and also returns this value. Raises an exception
-- if \(h\) is zero.
foreign import ccall "fmpz.h fmpz_mod_ui"
  fmpz_mod_ui :: Ptr CFmpz -> Ptr CFmpz -> CULong -> IO CULong

-- | /fmpz_smod/ /f/ /g/ /h/ 
-- 
-- Sets \(f\) to the signed remainder \(y \equiv g \bmod h\) satisfying
-- \(-\lvert h \rvert/2 < y \leq \lvert h\rvert/2\).
foreign import ccall "fmpz.h fmpz_smod"
  fmpz_smod :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpz_preinvn_init/ /inv/ /f/ 
-- 
-- Compute a precomputed inverse @inv@ of @f@ for use in the @preinvn@
-- functions listed below.
foreign import ccall "fmpz.h fmpz_preinvn_init"
  fmpz_preinvn_init :: Ptr CFmpzPreInvN -> Ptr CFmpz -> IO ()

-- | /fmpz_preinvn_clear/ /inv/ 
-- 
-- Clean up the resources used by a precomputed inverse created with the
-- @fmpz_preinvn_init@ function.
foreign import ccall "fmpz.h fmpz_preinvn_clear"
  fmpz_preinvn_clear :: Ptr CFmpzPreInvN -> IO ()

-- | /fmpz_fdiv_qr_preinvn/ /f/ /s/ /g/ /h/ /hinv/ 
-- 
-- As per @fmpz_fdiv_qr@, but takes a precomputed inverse @hinv@ of \(h\)
-- constructed using @fmpz_preinvn@.
-- 
-- This function will be faster than @fmpz_fdiv_qr_preinvn@ when the number
-- of limbs of \(h\) is at least @PREINVN_CUTOFF@.
foreign import ccall "fmpz.h fmpz_fdiv_qr_preinvn"
  fmpz_fdiv_qr_preinvn :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpzPreInvN -> IO ()

-- | /fmpz_pow_ui/ /f/ /g/ /x/ 
-- 
-- Sets \(f\) to \(g^x\). Defines \(0^0 = 1\).
foreign import ccall "fmpz.h fmpz_pow_ui"
  fmpz_pow_ui :: Ptr CFmpz -> Ptr CFmpz -> CULong -> IO ()

-- | /fmpz_pow_fmpz/ /f/ /g/ /x/ 
-- 
-- Sets \(f\) to \(g^x\). Defines \(0^0 = 1\). Return \(1\) for success and
-- \(0\) for failure. The function throws only if \(x\) is negative.
foreign import ccall "fmpz.h fmpz_pow_fmpz"
  fmpz_pow_fmpz :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO CInt

foreign import ccall "fmpz.h fmpz_powm_ui"
  fmpz_powm_ui :: Ptr CFmpz -> Ptr CFmpz -> CULong -> Ptr CFmpz -> IO ()

-- | /fmpz_powm/ /f/ /g/ /e/ /m/ 
-- 
-- Sets \(f\) to \(g^e \bmod{m}\). If \(e = 0\), sets \(f\) to \(1\).
-- 
-- Assumes that \(m \neq 0\), raises an @abort@ signal otherwise.
foreign import ccall "fmpz.h fmpz_powm"
  fmpz_powm :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpz_clog/ /x/ /b/ 
-- 
-- Returns \(\lceil\log_b x\rceil\).
-- 
-- Assumes that \(x \geq 1\) and \(b \geq 2\) and that the return value
-- fits into a signed @slong@.
foreign import ccall "fmpz.h fmpz_clog"
  fmpz_clog :: Ptr CFmpz -> Ptr CFmpz -> IO CLong

-- | /fmpz_flog/ /x/ /b/ 
-- 
-- Returns \(\lfloor\log_b x\rfloor\).
-- 
-- Assumes that \(x \geq 1\) and \(b \geq 2\) and that the return value
-- fits into a signed @slong@.
foreign import ccall "fmpz.h fmpz_flog"
  fmpz_flog :: Ptr CFmpz -> Ptr CFmpz -> IO CLong

-- | /fmpz_dlog/ /x/ 
-- 
-- Returns a double precision approximation of the natural logarithm of
-- \(x\).
-- 
-- The accuracy depends on the implementation of the floating-point
-- logarithm provided by the C standard library. The result can typically
-- be expected to have a relative error no greater than 1-2 bits.
foreign import ccall "fmpz.h fmpz_dlog"
  fmpz_dlog :: Ptr CFmpz -> IO CDouble

-- | /fmpz_sqrtmod/ /b/ /a/ /p/ 
-- 
-- If \(p\) is prime, set \(b\) to a square root of \(a\) modulo \(p\) if
-- \(a\) is a quadratic residue modulo \(p\) and return \(1\), otherwise
-- return \(0\).
-- 
-- If \(p\) is not prime the return value is with high probability \(0\),
-- indicating that \(p\) is not prime, or \(a\) is not a square modulo
-- \(p\). If \(p\) is not prime and the return value is \(1\), the value of
-- \(b\) is meaningless.
foreign import ccall "fmpz.h fmpz_sqrtmod"
  fmpz_sqrtmod :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO CInt

-- | /fmpz_sqrt/ /f/ /g/ 
-- 
-- Sets \(f\) to the integer part of the square root of \(g\), where \(g\)
-- is assumed to be non-negative. If \(g\) is negative, an exception is
-- raised.
foreign import ccall "fmpz.h fmpz_sqrt"
  fmpz_sqrt :: Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpz_sqrtrem/ /f/ /r/ /g/ 
-- 
-- Sets \(f\) to the integer part of the square root of \(g\), where \(g\)
-- is assumed to be non-negative, and sets \(r\) to the remainder, that is,
-- the difference \(g - f^2\). If \(g\) is negative, an exception is
-- raised. The behaviour is undefined if \(f\) and \(r\) are aliases.
foreign import ccall "fmpz.h fmpz_sqrtrem"
  fmpz_sqrtrem :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpz_is_square/ /f/ 
-- 
-- Returns nonzero if \(f\) is a perfect square and zero otherwise.
foreign import ccall "fmpz.h fmpz_is_square"
  fmpz_is_square :: Ptr CFmpz -> IO CInt

-- | /fmpz_root/ /r/ /f/ /n/ 
-- 
-- Set \(r\) to the integer part of the \(n\)-th root of \(f\). Requires
-- that \(n > 0\) and that if \(n\) is even then \(f\) be non-negative,
-- otherwise an exception is raised. The function returns \(1\) if the root
-- was exact, otherwise \(0\).
foreign import ccall "fmpz.h fmpz_root"
  fmpz_root :: Ptr CFmpz -> Ptr CFmpz -> CLong -> IO CInt

-- | /fmpz_is_perfect_power/ /root/ /f/ 
-- 
-- If \(f\) is a perfect power \(r^k\) set @root@ to \(r\) and return
-- \(k\), otherwise return \(0\). Note that \(-1, 0, 1\) are all considered
-- perfect powers. No guarantee is made about \(r\) or \(k\) being the
-- smallest possible value. Negative values of \(f\) are permitted.
foreign import ccall "fmpz.h fmpz_is_perfect_power"
  fmpz_is_perfect_power :: Ptr CFmpz -> Ptr CFmpz -> IO CInt

-- | /fmpz_fac_ui/ /f/ /n/ 
-- 
-- Sets \(f\) to the factorial \(n!\) where \(n\) is an @ulong@.
foreign import ccall "fmpz.h fmpz_fac_ui"
  fmpz_fac_ui :: Ptr CFmpz -> CULong -> IO ()

-- | /fmpz_fib_ui/ /f/ /n/ 
-- 
-- Sets \(f\) to the Fibonacci number \(F_n\) where \(n\) is an @ulong@.
foreign import ccall "fmpz.h fmpz_fib_ui"
  fmpz_fib_ui :: Ptr CFmpz -> CULong -> IO ()

-- | /fmpz_bin_uiui/ /f/ /n/ /k/ 
-- 
-- Sets \(f\) to the binomial coefficient \({n \choose k}\).
foreign import ccall "fmpz.h fmpz_bin_uiui"
  fmpz_bin_uiui :: Ptr CFmpz -> CULong -> CULong -> IO ()

-- | /_fmpz_rfac_ui/ /r/ /x/ /a/ /b/ 
-- 
-- Sets \(r\) to the rising factorial
-- \((x+a) (x+a+1) (x+a+2) \cdots (x+b-1)\). Assumes \(b > a\).
foreign import ccall "fmpz.h _fmpz_rfac_ui"
  _fmpz_rfac_ui :: Ptr CFmpz -> Ptr CFmpz -> CULong -> CULong -> IO ()

-- | /fmpz_rfac_ui/ /r/ /x/ /k/ 
-- 
-- Sets \(r\) to the rising factorial \(x (x+1) (x+2) \cdots (x+k-1)\).
foreign import ccall "fmpz.h fmpz_rfac_ui"
  fmpz_rfac_ui :: Ptr CFmpz -> Ptr CFmpz -> CULong -> IO ()

-- | /fmpz_rfac_uiui/ /r/ /x/ /k/ 
-- 
-- Sets \(r\) to the rising factorial \(x (x+1) (x+2) \cdots (x+k-1)\).
foreign import ccall "fmpz.h fmpz_rfac_uiui"
  fmpz_rfac_uiui :: Ptr CFmpz -> CULong -> CULong -> IO ()

-- | /fmpz_mul_tdiv_q_2exp/ /f/ /g/ /h/ /exp/ 
-- 
-- Sets \(f\) to the product \(g\) and \(h\) divided by @2^exp@, rounding
-- down towards zero.
foreign import ccall "fmpz.h fmpz_mul_tdiv_q_2exp"
  fmpz_mul_tdiv_q_2exp :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CULong -> IO ()

-- | /fmpz_mul_si_tdiv_q_2exp/ /f/ /g/ /x/ /exp/ 
-- 
-- Sets \(f\) to the product \(g\) and \(x\) divided by @2^exp@, rounding
-- down towards zero.
foreign import ccall "fmpz.h fmpz_mul_si_tdiv_q_2exp"
  fmpz_mul_si_tdiv_q_2exp :: Ptr CFmpz -> Ptr CFmpz -> CLong -> CULong -> IO ()

-- Greatest common divisor -----------------------------------------------------

foreign import ccall "fmpz.h fmpz_gcd_ui"
  fmpz_gcd_ui :: Ptr CFmpz -> Ptr CFmpz -> CULong -> IO ()

-- | /fmpz_gcd/ /f/ /g/ /h/ 
-- 
-- Sets \(f\) to the greatest common divisor of \(g\) and \(h\). The result
-- is always positive, even if one of \(g\) and \(h\) is negative.
foreign import ccall "fmpz.h fmpz_gcd"
  fmpz_gcd :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpz_gcd3/ /f/ /a/ /b/ /c/ 
-- 
-- Sets \(f\) to the greatest common divisor of \(a\), \(b\) and \(c\).
-- This is equivalent to calling @fmpz_gcd@ twice, but may be faster.
foreign import ccall "fmpz.h fmpz_gcd3"
  fmpz_gcd3 :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpz_lcm/ /f/ /g/ /h/ 
-- 
-- Sets \(f\) to the least common multiple of \(g\) and \(h\). The result
-- is always nonnegative, even if one of \(g\) and \(h\) is negative.
foreign import ccall "fmpz.h fmpz_lcm"
  fmpz_lcm :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpz_gcdinv/ /d/ /a/ /f/ /g/ 
-- 
-- Given integers \(f, g\) with \(0 \leq f < g\), computes the greatest
-- common divisor \(d = \gcd(f, g)\) and the modular inverse
-- \(a = f^{-1} \pmod{g}\), whenever \(f \neq 0\).
-- 
-- Assumes that \(d\) and \(a\) are not aliased.
foreign import ccall "fmpz.h fmpz_gcdinv"
  fmpz_gcdinv :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpz_xgcd/ /d/ /a/ /b/ /f/ /g/ 
-- 
-- Computes the extended GCD of \(f\) and \(g\), i.e. the values \(a\) and
-- \(b\) such that \(af + bg = d\), where \(d = \gcd(f, g)\). Here \(a\)
-- will be the same as calling @fmpz_gcdinv@ when \(f < g\) (or vice versa
-- for \(b\) when \(g < f\)).
-- 
-- To obtain the canonical solution to Bézout\'s identity, call
-- @fmpz_xgcd_canonical_bezout@ instead. This is also faster.
-- 
-- Assumes that there is no aliasing among the outputs.
foreign import ccall "fmpz.h fmpz_xgcd"
  fmpz_xgcd :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpz_xgcd_canonical_bezout/ /d/ /a/ /b/ /f/ /g/ 
-- 
-- Computes the extended GCD \(\mathrm{xgcd}(f, g) = (d, a, b)\) such
-- that the solution is the canonical solution to Bézout\'s identity. We
-- define the canonical solution to satisfy one of the following if one of
-- the given conditions apply:
--
-- \[\begin{aligned}
-- \operatorname{xgcd}(\pm g, g) &= \bigl(|g|, 0, \operatorname{sgn}(g)\bigr)\\
-- \operatorname{xgcd}(f, 0) &= \bigl(|f|, \operatorname{sgn}(f), 0\bigr)\\
-- \operatorname{xgcd}(0, g) &= \bigl(|g|, 0, \operatorname{sgn}(g)\bigr)\\
-- \operatorname{xgcd}(f, \mp 1) &= (1, 0, \mp 1)\\
-- \operatorname{xgcd}(\mp 1, g) &= (1, \mp 1, 0)\quad g \neq 0, \pm 1\\
-- \operatorname{xgcd}(\mp 2 d, g) &=
-- \bigl(d, {\textstyle\frac{d - |g|}{\mp 2 d}}, \operatorname{sgn}(g)\bigr)\\
-- \operatorname{xgcd}(f, \mp 2 d) &=
-- \bigl(d, \operatorname{sgn}(f), {\textstyle\frac{d - |g|}{\mp 2 d}}\bigr).
-- \end{aligned}\]
-- 
-- If the pair \((f, g)\) does not satisfy any of these conditions, the
-- solution \((d, a, b)\) will satisfy the following:
-- 
-- \[`\]
-- \[|a| < \Bigl| \frac{g}{2 d} \Bigr|,
-- \qquad |b| < \Bigl| \frac{f}{2 d} \Bigr|.\]
-- 
-- Assumes that there is no aliasing among the outputs.
foreign import ccall "fmpz.h fmpz_xgcd_canonical_bezout"
  fmpz_xgcd_canonical_bezout :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpz_xgcd_partial/ /co2/ /co1/ /r2/ /r1/ /L/ 
-- 
-- This function is an implementation of Lehmer extended GCD with early
-- termination, as used in the @qfb@ module. It terminates early when
-- remainders fall below the specified bound. The initial values @r1@ and
-- @r2@ are treated as successive remainders in the Euclidean algorithm and
-- are replaced with the last two remainders computed. The values @co1@ and
-- @co2@ are the last two cofactors and satisfy the identity
-- @co2*r1 - co1*r2 == +\/- r2_orig@ upon termination, where @r2_orig@ is
-- the starting value of @r2@ supplied, and @r1@ and @r2@ are the final
-- values.
-- 
-- Aliasing of inputs is not allowed. Similarly aliasing of inputs and
-- outputs is not allowed.
foreign import ccall "fmpz.h fmpz_xgcd_partial"
  fmpz_xgcd_partial :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- Modular arithmetic ----------------------------------------------------------

-- | /_fmpz_remove/ /x/ /f/ /finv/ 
-- 
-- Removes all factors \(f\) from \(x\) and returns the number of such.
-- 
-- Assumes that \(x\) is non-zero, that \(f > 1\) and that @finv@ is the
-- precomputed @double@ inverse of \(f\) whenever \(f\) is a small integer
-- and \(0\) otherwise.
-- 
-- Does not support aliasing.
foreign import ccall "fmpz.h _fmpz_remove"
  _fmpz_remove :: Ptr CFmpz -> Ptr CFmpz -> CDouble -> IO CLong

-- | /fmpz_remove/ /rop/ /op/ /f/ 
-- 
-- Remove all occurrences of the factor \(f > 1\) from the integer @op@ and
-- sets @rop@ to the resulting integer.
-- 
-- If @op@ is zero, sets @rop@ to @op@ and returns \(0\).
-- 
-- Returns an @abort@ signal if any of the assumptions are violated.
foreign import ccall "fmpz.h fmpz_remove"
  fmpz_remove :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO CLong

-- | /fmpz_invmod/ /f/ /g/ /h/ 
-- 
-- Sets \(f\) to the inverse of \(g\) modulo \(h\). The value of \(h\) may
-- not be \(0\) otherwise an exception results. If the inverse exists the
-- return value will be non-zero, otherwise the return value will be \(0\)
-- and the value of \(f\) undefined. As a special case, we consider any
-- number invertible modulo \(h = \pm 1\), with inverse 0.
foreign import ccall "fmpz.h fmpz_invmod"
  fmpz_invmod :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO CInt

-- | /fmpz_negmod/ /f/ /g/ /h/ 
-- 
-- Sets \(f\) to \(-g \pmod{h}\), assuming \(g\) is reduced modulo \(h\).
foreign import ccall "fmpz.h fmpz_negmod"
  fmpz_negmod :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpz_jacobi/ /a/ /n/ 
-- 
-- Computes the Jacobi symbol \(\left(\frac{a}{n}\right)\) for any \(a\)
-- and odd positive \(n\).
foreign import ccall "fmpz.h fmpz_jacobi"
  fmpz_jacobi :: Ptr CFmpz -> Ptr CFmpz -> IO CInt

-- | /fmpz_kronecker/ /a/ /n/ 
-- 
-- Computes the Kronecker symbol \(\left(\frac{a}{n}\right)\) for any \(a\)
-- and any \(n\).
foreign import ccall "fmpz.h fmpz_kronecker"
  fmpz_kronecker :: Ptr CFmpz -> Ptr CFmpz -> IO CInt

-- | /fmpz_divides_mod_list/ /xstart/ /xstride/ /xlength/ /a/ /b/ /n/ 
-- 
-- Set \(xstart\), \(xstride\), and \(xlength\) so that the solution set
-- for x modulo \(n\) in \(a x = b mod n\) is exactly
-- \(\{xstart + xstride i | 0 \le i < xlength\}\). This function
-- essentially gives a list of possibilities for the fraction \(a/b\)
-- modulo \(n\). The outputs may not be aliased, and \(n\) should be
-- positive.
foreign import ccall "fmpz.h fmpz_divides_mod_list"
  fmpz_divides_mod_list :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- Bit packing and unpacking ---------------------------------------------------

-- | /fmpz_bit_pack/ /arr/ /shift/ /bits/ /coeff/ /negate/ /borrow/ 
-- 
-- Shifts the given coefficient to the left by @shift@ bits and adds it to
-- the integer in @arr@ in a field of the given number of bits:
-- 
-- > shift  bits  --------------
-- >
-- > X X X C C C C 0 0 0 0 0 0 0
-- 
-- An optional borrow of \(1\) can be subtracted from @coeff@ before it is
-- packed. If @coeff@ is negative after the borrow, then a borrow will be
-- returned by the function.
-- 
-- The value of @shift@ is assumed to be less than @FLINT_BITS@. All but
-- the first @shift@ bits of @arr@ are assumed to be zero on entry to the
-- function.
-- 
-- The value of @coeff@ may also be optionally (and notionally) negated
-- before it is used, by setting the @negate@ parameter to \(-1\).
foreign import ccall "fmpz.h fmpz_bit_pack"
  fmpz_bit_pack :: Ptr CMpLimb -> CFBitCnt -> CFBitCnt -> Ptr CFmpz -> CInt -> CInt -> IO CInt

-- | /fmpz_bit_unpack/ /coeff/ /arr/ /shift/ /bits/ /negate/ /borrow/ 
-- 
-- A bit field of the given number of bits is extracted from @arr@,
-- starting after @shift@ bits, and placed into @coeff@. An optional borrow
-- of \(1\) may be added to the coefficient. If the result is negative, a
-- borrow of \(1\) is returned. Finally, the resulting @coeff@ may be
-- negated by setting the @negate@ parameter to \(-1\).
-- 
-- The value of @shift@ is expected to be less than @FLINT_BITS@.
foreign import ccall "fmpz.h fmpz_bit_unpack"
  fmpz_bit_unpack :: Ptr CFmpz -> Ptr CMpLimb -> CFBitCnt -> CFBitCnt -> CInt -> CInt -> IO CInt

-- | /fmpz_bit_unpack_unsigned/ /coeff/ /arr/ /shift/ /bits/ 
-- 
-- A bit field of the given number of bits is extracted from @arr@,
-- starting after @shift@ bits, and placed into @coeff@.
-- 
-- The value of @shift@ is expected to be less than @FLINT_BITS@.
foreign import ccall "fmpz.h fmpz_bit_unpack_unsigned"
  fmpz_bit_unpack_unsigned :: Ptr CFmpz -> Ptr CMpLimb -> CFBitCnt -> CFBitCnt -> IO ()

-- Logic Operations ------------------------------------------------------------

-- | /fmpz_complement/ /r/ /f/ 
-- 
-- The variable @r@ is set to the ones-complement of @f@.
foreign import ccall "fmpz.h fmpz_complement"
  fmpz_complement :: Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpz_clrbit/ /f/ /i/ 
-- 
-- Sets the @i@th bit in @f@ to zero.
foreign import ccall "fmpz.h fmpz_clrbit"
  fmpz_clrbit :: Ptr CFmpz -> CULong -> IO ()

-- | /fmpz_combit/ /f/ /i/ 
-- 
-- Complements the @i@th bit in @f@.
foreign import ccall "fmpz.h fmpz_combit"
  fmpz_combit :: Ptr CFmpz -> CULong -> IO ()

-- | /fmpz_and/ /r/ /a/ /b/ 
-- 
-- Sets @r@ to the bit-wise logical @and@ of @a@ and @b@.
foreign import ccall "fmpz.h fmpz_and"
  fmpz_and :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpz_or/ /r/ /a/ /b/ 
-- 
-- Sets @r@ to the bit-wise logical (inclusive) @or@ of @a@ and @b@.
foreign import ccall "fmpz.h fmpz_or"
  fmpz_or :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpz_xor/ /r/ /a/ /b/ 
-- 
-- Sets @r@ to the bit-wise logical exclusive @or@ of @a@ and @b@.
foreign import ccall "fmpz.h fmpz_xor"
  fmpz_xor :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpz_popcnt/ /a/ 
-- 
-- Returns the number of \'1\' bits in the given Z (aka Hamming weight or
-- population count). The return value is undefined if the input is
-- negative.
foreign import ccall "fmpz.h fmpz_popcnt"
  fmpz_popcnt :: Ptr CFmpz -> IO CInt

-- FmpzComb --------------------------------------------------------------------

newFmpzComb primes num_primes = do
  p <- mallocForeignPtr
  withForeignPtr p $ \p -> fmpz_comb_init p primes num_primes
  addForeignPtrFinalizer p_fmpz_comb_clear p
  return $ FmpzComb p

{-# INLINE withFmpzCombTemp #-}
withFmpzComb (FmpzComb p) f = do
  withForeignPtr p $ \fp -> f fp >>= return . (FmpzComb p,)

-- FmpzCombTemp ----------------------------------------------------------------

newFmpzCombTemp comb = do
  p <- mallocForeignPtr
  withForeignPtr p $ \p -> fmpz_comb_temp_init p comb
  addForeignPtrFinalizer p_fmpz_comb_temp_clear p
  return $ FmpzCombTemp p

{-# INLINE withFmpzComb #-}
withFmpzCombTemp (FmpzCombTemp p) f = do
  withForeignPtr p $ \fp -> f fp >>= return . (FmpzCombTemp p,)

-- Chinese remaindering --------------------------------------------------------

-- The following functions can be used to reconstruct an integer from its
-- residues modulo a set of small (word-size) prime numbers. The first two
-- functions, @fmpz_CRT_ui@ and @fmpz_CRT@, are easy to use and allow
-- building the result one residue at a time, which is useful when the
-- number of needed primes is not known in advance. The remaining functions
-- support performing the modular reductions and reconstruction using
-- balanced subdivision. This greatly improves efficiency for large
-- integers but assumes that the basis of primes is known in advance. The
-- user must precompute a @comb@ structure and temporary working space with
-- @fmpz_comb_init@ and @fmpz_comb_temp_init@, and free this data
-- afterwards. For simple demonstration programs showing how to use the CRT
-- functions, see @crt.c@ and @multi_crt.c@ in the @examples@ directory.
-- The @fmpz_multi_crt@ class is similar to @fmpz_multi_CRT_ui@ except that
-- it performs error checking and works with arbitrary moduli.
--
-- | /fmpz_CRT_ui/ /out/ /r1/ /m1/ /r2/ /m2/ /sign/ 
-- 
-- Uses the Chinese Remainder Theorem to compute the unique integer
-- \(0 \le x < M\) (if sign = 0) or \(-M/2 < x \le M/2\) (if sign = 1)
-- congruent to \(r_1\) modulo \(m_1\) and \(r_2\) modulo \(m_2\), where
-- where \(M = m_1 \times m_2\). The result \(x\) is stored in @out@.
-- 
-- It is assumed that \(m_1\) and \(m_2\) are positive integers greater
-- than \(1\) and coprime.
-- 
-- If sign = 0, it is assumed that \(0 \le r_1 < m_1\) and
-- \(0 \le r_2 < m_2\). Otherwise, it is assumed that
-- \(-m_1 \le r_1 < m_1\) and \(0 \le r_2 < m_2\).
foreign import ccall "fmpz.h fmpz_CRT_ui"
  fmpz_CRT_ui :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CULong -> CULong -> CInt -> IO ()

-- | /fmpz_CRT/ /out/ /r1/ /m1/ /r2/ /m2/ /sign/ 
-- 
-- Use the Chinese Remainder Theorem to set @out@ to the unique value
-- \(0 \le x < M\) (if sign = 0) or \(-M/2 < x \le M/2\) (if sign = 1)
-- congruent to \(r_1\) modulo \(m_1\) and \(r_2\) modulo \(m_2\), where
-- where \(M = m_1 \times m_2\).
-- 
-- It is assumed that \(m_1\) and \(m_2\) are positive integers greater
-- than \(1\) and coprime.
-- 
-- If sign = 0, it is assumed that \(0 \le r_1 < m_1\) and
-- \(0 \le r_2 < m_2\). Otherwise, it is assumed that
-- \(-m_1 \le r_1 < m_1\) and \(0 \le r_2 < m_2\).
foreign import ccall "fmpz.h fmpz_CRT"
  fmpz_CRT :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CInt -> IO ()

-- | /fmpz_multi_mod_ui/ /out/ /in/ /comb/ /temp/ 
-- 
-- Reduces the multiprecision integer @in@ modulo each of the primes stored
-- in the @comb@ structure. The array @out@ will be filled with the
-- residues modulo these primes. The structure @temp@ is temporary space
-- which must be provided by @fmpz_comb_temp_init@ and cleared by
-- @fmpz_comb_temp_clear@.
foreign import ccall "fmpz.h fmpz_multi_mod_ui"
  fmpz_multi_mod_ui :: Ptr CMpLimb -> Ptr CFmpz -> Ptr CFmpzComb -> Ptr CFmpzCombTemp -> IO ()

-- | /fmpz_multi_CRT_ui/ /output/ /residues/ /comb/ /ctemp/ /sign/ 
-- 
-- This function takes a set of residues modulo the list of primes
-- contained in the @comb@ structure and reconstructs a multiprecision
-- integer modulo the product of the primes which has these residues modulo
-- the corresponding primes.
-- 
-- If \(N\) is the product of all the primes then @out@ is normalised to be
-- in the range \([0, N)\) if sign = 0 and the range \([-(N-1)/2, N/2]\) if
-- sign = 1. The array @temp@ is temporary space which must be provided by
-- @fmpz_comb_temp_init@ and cleared by @fmpz_comb_temp_clear@.
foreign import ccall "fmpz.h fmpz_multi_CRT_ui"
  fmpz_multi_CRT_ui :: Ptr CFmpz -> Ptr CMp -> Ptr CFmpzComb -> Ptr CFmpzCombTemp -> CInt -> IO ()

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

foreign import ccall "fmpz.h &fmpz_comb_clear"
  p_fmpz_comb_clear :: FunPtr (Ptr CFmpzComb -> IO ())

-- | /fmpz_comb_temp_clear/ /temp/ 
-- 
-- Clears temporary space @temp@ used by multimodular and CRT functions
-- using the given @comb@ structure.
foreign import ccall "fmpz.h fmpz_comb_temp_clear"
  fmpz_comb_temp_clear :: Ptr CFmpzCombTemp -> IO ()

foreign import ccall "fmpz.h &fmpz_comb_temp_clear"
  p_fmpz_comb_temp_clear :: FunPtr (Ptr CFmpzCombTemp -> IO ())

-- FmpzMultiCRT ----------------------------------------------------------------

newFmpzMultiCRT = do
  p <- mallocForeignPtr
  withForeignPtr p fmpz_multi_CRT_init
  addForeignPtrFinalizer p_fmpz_multi_CRT_clear p
  return $ FmpzMultiCRT p

{-# INLINE withFmpzMultiCRT #-}
withFmpzMultiCRT (FmpzMultiCRT p) f = do
  withForeignPtr p $ \fp -> f fp >>= return . (FmpzMultiCRT p,)

-- | /fmpz_multi_CRT_init/ /CRT/ 
-- 
-- Initialize @CRT@ for Chinese remaindering.
foreign import ccall "fmpz.h fmpz_multi_CRT_init"
  fmpz_multi_CRT_init :: Ptr CFmpzMultiCRT -> IO ()

-- | /fmpz_multi_CRT_precompute/ /CRT/ /moduli/ /len/ 
-- 
-- Configure @CRT@ for repeated Chinese remaindering of @moduli@. The
-- number of moduli, @len@, should be positive. A return of @0@ indicates
-- that the compilation failed and future calls to @fmpz_crt_precomp@ will
-- leave the output undefined. A return of @1@ indicates that the
-- compilation was successful, which occurs if and only if either (1)
-- @len == 1@ and @modulus + 0@ is nonzero, or (2) no modulus is \(0,1,-1\)
-- and all moduli are pairwise relatively prime.
foreign import ccall "fmpz.h fmpz_multi_CRT_precompute"
  fmpz_multi_CRT_precompute :: Ptr CFmpzMultiCRT -> Ptr CFmpz -> CLong -> IO CInt

-- | /fmpz_multi_CRT_precomp/ /output/ /P/ /inputs/ 
-- 
-- Set @output@ to an integer of smallest absolute value that is congruent
-- to @values + i@ modulo the @moduli + i@ in @fmpz_crt_precompute@.
foreign import ccall "fmpz.h fmpz_multi_CRT_precomp"
  fmpz_multi_CRT_precomp :: Ptr CFmpz -> Ptr CFmpzMultiCRT -> Ptr CFmpz -> IO ()

-- | /fmpz_multi_CRT/ /output/ /moduli/ /values/ /len/ 
-- 
-- Perform the same operation as @fmpz_multi_CRT_precomp@ while internally
-- constructing and destroying the precomputed data. All of the remarks in
-- @fmpz_multi_CRT_precompute@ apply.
foreign import ccall "fmpz.h fmpz_multi_CRT"
  fmpz_multi_CRT :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> IO CInt

-- | /fmpz_multi_CRT_clear/ /P/ 
-- 
-- Free all space used by @CRT@.
foreign import ccall "fmpz.h fmpz_multi_CRT_clear"
  fmpz_multi_CRT_clear :: Ptr CFmpzMultiCRT -> IO ()

foreign import ccall "fmpz.h &fmpz_multi_CRT_clear"
  p_fmpz_multi_CRT_clear :: FunPtr (Ptr CFmpzMultiCRT -> IO ())

-- not presentin fmpz.h in flintlib 2.9.0 --------------------------------------
-- -- | /_nmod_poly_crt_local_size/ /CRT/ 
-- -- 
-- -- Return the required length of the output for @_nmod_poly_crt_run@.
-- foreign import ccall "fmpz.h _nmod_poly_crt_local_size"
--   _nmod_poly_crt_local_size :: Ptr CNModPolyCRT -> IO CLong

-- not present in flintlib 2.9.0 -----------------------------------------------
-- -- | /_fmpz_multi_CRT_run/ /outputs/ /CRT/ /inputs/ 
-- -- 
-- -- Perform the same operation as fmpz::fmpz_multi_CRT_precomp using
-- -- supplied temporary space. The actual output is placed in @outputs + 0@,
-- -- and @outputs@ should contain space for all temporaries and should be at
-- -- least as long as @_fmpz_multi_CRT_local_size(CRT)@.
-- foreign import ccall "fmpz.h _fmpz_multi_CRT_run"
--   _fmpz_multi_CRT_run :: Ptr CFmpz -> Ptr CFmpzMultiCRT -> Ptr CFmpz -> IO ()

-- Primality testing -----------------------------------------------------------

-- | /fmpz_is_strong_probabprime/ /n/ /a/ 
-- 
-- Returns \(1\) if \(n\) is a strong probable prime to base \(a\),
-- otherwise it returns \(0\).
foreign import ccall "fmpz.h fmpz_is_strong_probabprime"
  fmpz_is_strong_probabprime :: Ptr CFmpz -> Ptr CFmpz -> IO CInt

-- | /fmpz_is_probabprime_lucas/ /n/ 
-- 
-- Performs a Lucas probable prime test with parameters chosen by
-- Selfridge\'s method \(A\) as per < [BaiWag1980]>.
-- 
-- Return \(1\) if \(n\) is a Lucas probable prime, otherwise return \(0\).
-- This function declares some composites probably prime, but no primes
-- composite.
foreign import ccall "fmpz.h fmpz_is_probabprime_lucas"
  fmpz_is_probabprime_lucas :: Ptr CFmpz -> IO CInt

-- | /fmpz_is_probabprime_BPSW/ /n/ 
-- 
-- Perform a Baillie-PSW probable prime test with parameters chosen by
-- Selfridge\'s method \(A\) as per < [BaiWag1980]>.
-- 
-- Return \(1\) if \(n\) is a Lucas probable prime, otherwise return \(0\).
-- 
-- There are no known composites passed as prime by this test, though
-- infinitely many probably exist. The test will declare no primes
-- composite.
foreign import ccall "fmpz.h fmpz_is_probabprime_BPSW"
  fmpz_is_probabprime_BPSW :: Ptr CFmpz -> IO CInt

-- | /fmpz_is_probabprime/ /p/ 
-- 
-- Performs some trial division and then some probabilistic primality
-- tests. If \(p\) is definitely composite, the function returns \(0\),
-- otherwise it is declared probably prime, i.e. prime for most practical
-- purposes, and the function returns \(1\). The chance of declaring a
-- composite prime is very small.
-- 
-- Subsequent calls to the same function do not increase the probability of
-- the number being prime.
foreign import ccall "fmpz.h fmpz_is_probabprime"
  fmpz_is_probabprime :: Ptr CFmpz -> IO CInt

-- | /fmpz_is_prime_pseudosquare/ /n/ 
-- 
-- Return \(0\) is \(n\) is composite. If \(n\) is too large (greater than
-- about \(94\) bits) the function fails silently and returns \(-1\),
-- otherwise, if \(n\) is proven prime by the pseudosquares method, return
-- \(1\).
-- 
-- Tests if \(n\) is a prime according to [Theorem 2.7] < [LukPatWil1996]>.
-- 
-- We first factor \(N\) using trial division up to some limit \(B\). In
-- fact, the number of primes used in the trial factoring is at most
-- @FLINT_PSEUDOSQUARES_CUTOFF@.
-- 
-- Next we compute \(N/B\) and find the next pseudosquare \(L_p\) above
-- this value, using a static table as per
-- <https://oeis.org/A002189/b002189.txt>.
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
foreign import ccall "fmpz.h fmpz_is_prime_pseudosquare"
  fmpz_is_prime_pseudosquare :: Ptr CFmpz -> IO CInt

-- | /fmpz_is_prime_pocklington/ /F/ /R/ /n/ /pm1/ /num_pm1/ 
-- 
-- Applies the Pocklington primality test. The test computes a product
-- \(F\) of prime powers which divide \(n - 1\).
-- 
-- The function then returns either \(0\) if \(n\) is definitely composite
-- or it returns \(1\) if all factors of \(n\) are \(1 \pmod{F}\). Also in
-- that case, \(R\) is set to \((n - 1)/F\).
-- 
-- N.B: a return value of \(1\) only proves \(n\) prime if
-- \(F \ge \sqrt{n}\).
-- 
-- The function does not compute which primes divide \(n - 1\). Instead,
-- these must be supplied as an array @pm1@ of length @num_pm1@. It does
-- not matter how many prime factors are supplied, but the more that are
-- supplied, the larger F will be.
-- 
-- There is a balance between the amount of time spent looking for factors
-- of \(n - 1\) and the usefulness of the output (F may be as low as \(2\)
-- in some cases).
-- 
-- A reasonable heuristic seems to be to choose @limit@ to be some small
-- multiple of \(\log^3(n)/10\) (e.g. \(1, 2, 5\) or \(10\)) depending on
-- how long one is prepared to wait, then to trial factor up to the limit.
-- (See @_fmpz_nm1_trial_factors@.)
-- 
-- Requires \(n\) to be odd.
foreign import ccall "fmpz.h fmpz_is_prime_pocklington"
  fmpz_is_prime_pocklington :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CMp -> CLong -> IO CInt

-- | /_fmpz_nm1_trial_factors/ /n/ /pm1/ /num_pm1/ /limit/ 
-- 
-- Trial factors \(n - 1\) up to the given limit (approximately) and stores
-- the factors in an array @pm1@ whose length is written out to @num_pm1@.
-- 
-- One can use \(\log(n) + 2\) as a bound on the number of factors which
-- might be produced (and hence on the length of the array that needs to be
-- supplied).
foreign import ccall "fmpz.h _fmpz_nm1_trial_factors"
  _fmpz_nm1_trial_factors :: Ptr CFmpz -> Ptr CMp -> Ptr CLong -> CULong -> IO ()

-- | /fmpz_is_prime_morrison/ /F/ /R/ /n/ /pp1/ /num_pp1/ 
-- 
-- Applies the Morrison \(p + 1\) primality test. The test computes a
-- product \(F\) of primes which divide \(n + 1\).
-- 
-- The function then returns either \(0\) if \(n\) is definitely composite
-- or it returns \(1\) if all factors of \(n\) are \(\pm 1 \pmod{F}\). Also
-- in that case, \(R\) is set to \((n + 1)/F\).
-- 
-- N.B: a return value of \(1\) only proves \(n\) prime if
-- \(F > \sqrt{n} + 1\).
-- 
-- The function does not compute which primes divide \(n + 1\). Instead,
-- these must be supplied as an array @pp1@ of length @num_pp1@. It does
-- not matter how many prime factors are supplied, but the more that are
-- supplied, the larger \(F\) will be.
-- 
-- There is a balance between the amount of time spent looking for factors
-- of \(n + 1\) and the usefulness of the output (F may be as low as \(2\)
-- in some cases).
-- 
-- A reasonable heuristic seems to be to choose @limit@ to be some small
-- multiple of \(\log^3(n)/10\) (e.g. \(1, 2, 5\) or \(10\)) depending on
-- how long one is prepared to wait, then to trial factor up to the limit.
-- (See @_fmpz_np1_trial_factors@.)
-- 
-- Requires \(n\) to be odd and non-square.
foreign import ccall "fmpz.h fmpz_is_prime_morrison"
  fmpz_is_prime_morrison :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CMp -> CLong -> IO CInt

-- | /_fmpz_np1_trial_factors/ /n/ /pp1/ /num_pp1/ /limit/ 
-- 
-- Trial factors \(n + 1\) up to the given limit (approximately) and stores
-- the factors in an array @pp1@ whose length is written out to @num_pp1@.
-- 
-- One can use \(\log(n) + 2\) as a bound on the number of factors which
-- might be produced (and hence on the length of the array that needs to be
-- supplied).
foreign import ccall "fmpz.h _fmpz_np1_trial_factors"
  _fmpz_np1_trial_factors :: Ptr CFmpz -> Ptr CMp -> Ptr CLong -> CULong -> IO ()

-- | /fmpz_is_prime/ /n/ 
-- 
-- Attempts to prove \(n\) prime. If \(n\) is proven prime, the function
-- returns \(1\). If \(n\) is definitely composite, the function returns
-- \(0\).
-- 
-- This function calls @n_is_prime@ for \(n\) that fits in a single word.
-- For \(n\) larger than one word, it tests divisibility by a few small
-- primes and whether \(n\) is a perfect square to rule out trivial
-- composites. For \(n\) up to about 81 bits, it then uses a strong
-- probable prime test (Miller-Rabin test) with the first 13 primes as
-- witnesses. This has been shown to prove primality < [SorWeb2016]>.
-- 
-- For larger \(n\), it does a single base-2 strong probable prime test to
-- eliminate most composite numbers. If \(n\) passes, it does a combination
-- of Pocklington, Morrison and Brillhart, Lehmer, Selfridge tests. If any
-- of these tests fails to give a proof, it falls back to performing an
-- APRCL test.
-- 
-- The APRCL test could theoretically fail to prove that \(n\) is prime or
-- composite. In that case, the program aborts. This is not expected to
-- occur in practice.
foreign import ccall "fmpz.h fmpz_is_prime"
  fmpz_is_prime :: Ptr CFmpz -> IO CInt

-- | /fmpz_lucas_chain/ /Vm/ /Vm1/ /A/ /m/ /n/ 
-- 
-- Given \(V_0 = 2\), \(V_1 = A\) compute \(V_m, V_{m + 1} \pmod{n}\) from
-- the recurrences \(V_j = AV_{j - 1} - V_{j - 2} \pmod{n}\).
-- 
-- This is computed efficiently using \(V_{2j} = V_j^2 - 2 \pmod{n}\) and
-- \(V_{2j + 1} = V_jV_{j + 1} - A \pmod{n}\).
-- 
-- No aliasing is permitted.
foreign import ccall "fmpz.h fmpz_lucas_chain"
  fmpz_lucas_chain :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpz_lucas_chain_full/ /Vm/ /Vm1/ /A/ /B/ /m/ /n/ 
-- 
-- Given \(V_0 = 2\), \(V_1 = A\) compute \(V_m, V_{m + 1} \pmod{n}\) from
-- the recurrences \(V_j = AV_{j - 1} - BV_{j - 2} \pmod{n}\).
-- 
-- This is computed efficiently using double and add formulas.
-- 
-- No aliasing is permitted.
foreign import ccall "fmpz.h fmpz_lucas_chain_full"
  fmpz_lucas_chain_full :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpz_lucas_chain_double/ /U2m/ /U2m1/ /Um/ /Um1/ /A/ /B/ /n/ 
-- 
-- Given \(U_m, U_{m + 1} \pmod{n}\) compute
-- \(U_{2m}, U_{2m + 1} \pmod{n}\).
-- 
-- Aliasing of \(U_{2m}\) and \(U_m\) and aliasing of \(U_{2m + 1}\) and
-- \(U_{m + 1}\) is permitted. No other aliasing is allowed.
foreign import ccall "fmpz.h fmpz_lucas_chain_double"
  fmpz_lucas_chain_double :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpz_lucas_chain_add/ /Umn/ /Umn1/ /Um/ /Um1/ /Un/ /Un1/ /A/ /B/ /n/ 
-- 
-- Given \(U_m, U_{m + 1} \pmod{n}\) and \(U_n, U_{n + 1} \pmod{n}\)
-- compute \(U_{m + n}, U_{m + n + 1} \pmod{n}\).
-- 
-- Aliasing of \(U_{m + n}\) with \(U_m\) or \(U_n\) and aliasing of
-- \(U_{m + n + 1}\) with \(U_{m + 1}\) or \(U_{n + 1}\) is permitted. No
-- other aliasing is allowed.
foreign import ccall "fmpz.h fmpz_lucas_chain_add"
  fmpz_lucas_chain_add :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpz_lucas_chain_mul/ /Ukm/ /Ukm1/ /Um/ /Um1/ /A/ /B/ /k/ /n/ 
-- 
-- Given \(U_m, U_{m + 1} \pmod{n}\) compute
-- \(U_{km}, U_{km + 1} \pmod{n}\).
-- 
-- Aliasing of \(U_{km}\) and \(U_m\) and aliasing of \(U_{km + 1}\) and
-- \(U_{m + 1}\) is permitted. No other aliasing is allowed.
foreign import ccall "fmpz.h fmpz_lucas_chain_mul"
  fmpz_lucas_chain_mul :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpz_lucas_chain_VtoU/ /Um/ /Um1/ /Vm/ /Vm1/ /A/ /B/ /Dinv/ /n/ 
-- 
-- Given \(V_m, V_{m + 1} \pmod{n}\) compute \(U_m, U_{m + 1} \pmod{n}\).
-- 
-- Aliasing of \(V_m\) and \(U_m\) and aliasing of \(V_{m + 1}\) and
-- \(U_{m + 1}\) is permitted. No other aliasing is allowed.
foreign import ccall "fmpz.h fmpz_lucas_chain_VtoU"
  fmpz_lucas_chain_VtoU :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpz_divisor_in_residue_class_lenstra/ /fac/ /n/ /r/ /s/ 
-- 
-- If there exists a proper divisor of \(n\) which is \(r \pmod{s}\) for
-- \(0 < r < s < n\), this function returns \(1\) and sets @fac@ to such a
-- divisor. Otherwise the function returns \(0\) and the value of @fac@ is
-- undefined.
-- 
-- We require \(\gcd(r, s) = 1\).
-- 
-- This is efficient if \(s^3 > n\).
foreign import ccall "fmpz.h fmpz_divisor_in_residue_class_lenstra"
  fmpz_divisor_in_residue_class_lenstra :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO CInt

-- | /fmpz_nextprime/ /res/ /n/ /proved/ 
-- 
-- Finds the next prime number larger than \(n\).
-- 
-- If @proved@ is nonzero, then the integer returned is guaranteed to
-- actually be prime. Otherwise if \(n\) fits in @FLINT_BITS - 3@ bits
-- @n_nextprime@ is called, and if not then the GMP @mpz_nextprime@
-- function is called. Up to an including GMP 6.1.2 this used Miller-Rabin
-- iterations, and thereafter uses a BPSW test.
foreign import ccall "fmpz.h fmpz_nextprime"
  fmpz_nextprime :: Ptr CFmpz -> Ptr CFmpz -> CInt -> IO ()

-- Special functions -----------------------------------------------------------

-- | /fmpz_primorial/ /res/ /n/ 
-- 
-- Sets @res@ to @n@ primorial or \(n \#\), the product of all prime
-- numbers less than or equal to \(n\).
foreign import ccall "fmpz.h fmpz_primorial"
  fmpz_primorial :: Ptr CFmpz -> CULong -> IO ()

-- | /fmpz_factor_euler_phi/ /res/ /fac/ 
-- 
-- Sets @res@ to the Euler totient function \(\phi(n)\), counting the
-- number of positive integers less than or equal to \(n\) that are coprime
-- to \(n\). The factor version takes a precomputed factorisation of \(n\).
foreign import ccall "fmpz.h fmpz_factor_euler_phi"
  fmpz_factor_euler_phi :: Ptr CFmpz -> Ptr CFmpzFactor -> IO ()

foreign import ccall "fmpz.h fmpz_euler_phi"
  fmpz_euler_phi :: Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpz_factor_moebius_mu/ /fac/ 
-- 
-- Computes the Moebius function \(\mu(n)\), which is defined as
-- \(\mu(n) = 0\) if \(n\) has a prime factor of multiplicity greater than
-- \(1\), \(\mu(n) = -1\) if \(n\) has an odd number of distinct prime
-- factors, and \(\mu(n) = 1\) if \(n\) has an even number of distinct
-- prime factors. By convention, \(\mu(0) = 0\). The factor version takes a
-- precomputed factorisation of \(n\).
foreign import ccall "fmpz.h fmpz_factor_moebius_mu"
  fmpz_factor_moebius_mu :: Ptr CFmpzFactor -> IO CInt

foreign import ccall "fmpz.h fmpz_moebius_mu"
  fmpz_moebius_mu :: Ptr CFmpz -> Ptr CFmpz -> CInt

-- | /fmpz_factor_divisor_sigma/ /res/ /k/ /fac/ 
-- 
-- Sets @res@ to \(\sigma_k(n)\), the sum of \(k`th powers of all 
-- divisors of :math:`n\). The factor version takes a precomputed
-- factorisation of \(n\).
foreign import ccall "fmpz.h fmpz_factor_divisor_sigma"
  fmpz_factor_divisor_sigma :: Ptr CFmpz -> CULong -> Ptr CFmpzFactor -> IO ()

foreign import ccall "fmpz.h fmpz_divisor_sigma"
  fmpz_divisor_sigma :: Ptr CFmpz -> CULong -> Ptr CFmpz -> IO ()

-- | /nmod_pow_fmpz/ /a/ /e/ /mod/ 
-- 
-- Returns \(a^e\) modulo @mod.n@. No assumptions are made about @mod.n@.
-- It is assumed that \(a\) is already reduced modulo @mod.n@ and that
-- \(e\) is not negative.
foreign import ccall "nmod.h nmod_pow_fmpz"
  nmod_pow_fmpz :: CMpLimb -> Ptr CFmpz -> Ptr CNMod -> IO CMpLimb
