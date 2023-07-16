{-|
module      :  Data.Number.Flint.Fmpq.FFI
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de
-}
module Data.Number.Flint.Fmpq.FFI (
  -- * Rational numbers @Fmpq@
    Fmpq (..)
  , CFmpq (..)
  , newFmpq
  , withFmpq
  , withFmpqNum
  , withFmpqDen
  , withNewFmpq
  , (//)
  , numerator
  , denominator
  -- * Memory management
  , fmpq_init
  , fmpq_clear
  -- * Canonicalisation
  , fmpq_canonicalise
  , _fmpq_canonicalise
  , fmpq_is_canonical
  , _fmpq_is_canonical
  -- * Basic assignment
  , fmpq_set
  , fmpq_swap
  , fmpq_neg
  , fmpq_abs
  , fmpq_zero
  , fmpq_one
  -- * Comparison
  , fmpq_is_zero
  , fmpq_is_one
  , fmpq_is_pm1
  , fmpq_equal
  , fmpq_sgn
  , fmpq_cmp
  , fmpq_cmp_fmpz
  , fmpq_cmp_si
  , fmpq_equal_ui
  , fmpq_equal_si
  , fmpq_height
  , fmpq_height_bits
  -- * Conversion
  , fmpq_set_fmpz_frac
  , fmpq_get_fmpz_frac
  , fmpq_get_mpz_frac
  , fmpq_set_si
  , _fmpq_set_si
  , fmpq_set_ui
  , _fmpq_set_ui
  , fmpq_set_mpq
  , fmpq_set_str
  , fmpq_init_set_mpz_frac_readonly
  , fmpq_get_d
  , fmpq_get_mpq
  , fmpq_get_mpfr
  , fmpq_get_str
  , _fmpq_get_str
  , flint_mpq_init_set_readonly
  , flint_mpq_clear_readonly
  , fmpq_init_set_readonly
  , fmpq_clear_readonly
  -- * Input and output
  , fmpq_fprint
  , _fmpq_fprint
  , fmpq_print
  , _fmpq_print
  -- * Random number generation
  , fmpq_randtest
  , _fmpq_randtest
  , fmpq_randtest_not_zero
  , fmpq_randbits
  , _fmpq_randbits
  -- * Arithmetic
  , fmpq_add
  , fmpq_sub
  , fmpq_mul
  , fmpq_div
  , _fmpq_add
  , _fmpq_sub
  , _fmpq_mul
  , _fmpq_div 
  , _fmpq_add_si
  , _fmpq_sub_si
  , _fmpq_add_ui
  , _fmpq_sub_ui
  , _fmpq_add_fmpz
  , _fmpq_sub_fmpz
  , _fmpq_mul_si
  , fmpq_add_si
  , fmpq_sub_si
  , fmpq_add_ui
  , fmpq_sub_ui
  , fmpq_add_fmpz
  , fmpq_sub_fmpz
  , _fmpq_mul_ui
  , fmpq_mul_ui
  , fmpq_addmul
  , fmpq_submul
  , _fmpq_addmul
  , fmpq_inv
  , _fmpq_pow_si
  , fmpq_pow_si
  , fmpq_pow_fmpz
  , fmpq_mul_fmpz
  , fmpq_div_fmpz
  , fmpq_mul_2exp
  , fmpq_div_2exp
  , _fmpq_gcd
  , fmpq_gcd
  , _fmpq_gcd_cofactors
  , fmpq_gcd_cofactors
  , _fmpq_add_small
  , _fmpq_mul_small
  -- * Modular reduction and rational reconstruction
  , _fmpq_mod_fmpz
  , _fmpq_reconstruct_fmpz_2_naive
  , _fmpq_reconstruct_fmpz
  -- * Rational enumeration
  , _fmpq_next_minimal
  , _fmpq_next_signed_minimal
  , _fmpq_next_calkin_wilf
  , _fmpq_next_signed_calkin_wilf
  , fmpq_farey_neighbors
  , fmpq_simplest_between
  -- * Continued fractions
  , fmpq_get_cfrac
  , fmpq_set_cfrac
  , fmpq_cfrac_bound
  -- * Special functions
  , _fmpq_harmonic_ui
  , fmpq_harmonic_ui
  -- * Dedekind sums
  , fmpq_dedekind_sum
  , fmpq_dedekind_sum_naive
) where 

-- rational numbers ------------------------------------------------------------

import System.IO.Unsafe

import Control.Monad

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr, nullPtr, castPtr )
import Foreign.Storable
import Foreign.Marshal ( free )
import Foreign.Marshal.Array ( advancePtr )

import Data.Functor ((<&>))

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz

#include <flint/flint.h>
#include <flint/fmpq.h>

-- fmpq_t ----------------------------------------------------------------------

-- | Rational numbers (opaque pointer)
data Fmpq = Fmpq {-# UNPACK #-} !(ForeignPtr CFmpq)
data CFmpq = CFmpq CFmpz CFmpz

instance Storable CFmpq where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fmpq_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fmpq_t}
  peek ptr = CFmpq
    <$> #{peek fmpq, num} ptr
    <*> #{peek fmpq, den} ptr
  poke = error "CFmpz.poke: Not defined"

-- Fmpq ------------------------------------------------------------------------

-- | Create a new `Fmpq` structure.
newFmpq = do
  x <- mallocForeignPtr
  withForeignPtr x fmpq_init
  addForeignPtrFinalizer p_fmpq_clear x
  return $ Fmpq x

-- | Use `Fmpq` structure.
{-# INLINE withFmpq #-}
withFmpq (Fmpq x) f = withForeignPtr x $ \xp -> f xp <&> (Fmpq x,)

-- | Use new `Fmpq` structure.
{-# INLINE withNewFmpq #-}
withNewFmpq f = newFmpq >>= flip withFmpq f

withFmpqNum x f = do
  withFmpq x $ \x -> do 
    f $ castPtr x

withFmpqDen x f = do
  withFmpq x $ \x -> do 
    f $ flip advancePtr 1 $ castPtr x

-- Fmpz <-> Fmpq ---------------------------------------------------------------

infixl 7 //

(//) :: Fmpz -> Fmpz -> Fmpq
(//) x y = unsafePerformIO $ do
  result <- newFmpq
  withFmpq result $ \result -> do
    withFmpz x $ \x -> do
      withFmpz y $ \y -> do
        fmpq_set_fmpz_frac result x y
  return result

numerator :: Fmpq -> Fmpz
numerator x = unsafePerformIO $ do
  result <- newFmpz
  withFmpz result $ \result -> do
    withFmpq x $ \x -> do
      withNewFmpz $ \tmp -> do
        fmpq_get_fmpz_frac result tmp x
  return result

denominator :: Fmpq -> Fmpz
denominator x = unsafePerformIO $ do
  result <- newFmpz
  withFmpz result $ \result -> do
    withFmpq x $ \x -> do
      withNewFmpz $ \tmp -> do
        fmpq_get_fmpz_frac tmp result x
  return result

-- Memory management -----------------------------------------------------------

-- | /fmpq_init/ /x/ 
-- 
-- Initialises the @fmpq_t@ variable @x@ for use. Its value is set to 0.
foreign import ccall "fmpq.h fmpq_init"
  fmpq_init :: Ptr CFmpq -> IO ()

-- | /fmpq_clear/ /x/ 
-- 
-- Clears the @fmpq_t@ variable @x@. To use the variable again, it must be
-- re-initialised with @fmpq_init@.
foreign import ccall "fmpq.h fmpq_clear"
  fmpq_clear :: Ptr CFmpq -> IO ()

foreign import ccall "fmpq.h &fmpq_clear"
  p_fmpq_clear :: FunPtr (Ptr CFmpq -> IO ())

-- Canonicalisation ------------------------------------------------------------

-- | /fmpq_canonicalise/ /res/ 
-- 
-- Puts @res@ in canonical form: the numerator and denominator are reduced
-- to lowest terms, and the denominator is made positive. If the numerator
-- is zero, the denominator is set to one.
-- 
-- If the denominator is zero, the outcome of calling this function is
-- undefined, regardless of the value of the numerator.
foreign import ccall "fmpq.h fmpq_canonicalise"
  fmpq_canonicalise :: Ptr CFmpq -> IO ()

-- | /_fmpq_canonicalise/ /num/ /den/ 
-- 
-- Does the same thing as @fmpq_canonicalise@, but for numerator and
-- denominator given explicitly as @fmpz_t@ variables. Aliasing of @num@
-- and @den@ is not allowed.
foreign import ccall "fmpq.h _fmpq_canonicalise"
  _fmpq_canonicalise :: Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpq_is_canonical/ /x/ 
-- 
-- Returns nonzero if @fmpq_t@ x is in canonical form (as produced by
-- @fmpq_canonicalise@), and zero otherwise.
foreign import ccall "fmpq.h fmpq_is_canonical"
  fmpq_is_canonical :: Ptr CFmpq -> IO CInt

-- | /_fmpq_is_canonical/ /num/ /den/ 
-- 
-- Does the same thing as @fmpq_is_canonical@, but for numerator and
-- denominator given explicitly as @fmpz_t@ variables.
foreign import ccall "fmpq.h _fmpq_is_canonical"
  _fmpq_is_canonical :: Ptr CFmpz -> Ptr CFmpz -> IO CInt

-- Basic assignment ------------------------------------------------------------

-- | /fmpq_set/ /dest/ /src/ 
-- 
-- Sets @dest@ to a copy of @src@. No canonicalisation is performed.
foreign import ccall "fmpq.h fmpq_set"
  fmpq_set :: Ptr CFmpq -> Ptr CFmpq -> IO ()

-- | /fmpq_swap/ /op1/ /op2/ 
-- 
-- Swaps the two rational numbers @op1@ and @op2@.
foreign import ccall "fmpq.h fmpq_swap"
  fmpq_swap :: Ptr CFmpq -> Ptr CFmpq -> IO ()

-- | /fmpq_neg/ /dest/ /src/ 
-- 
-- Sets @dest@ to the additive inverse of @src@.
foreign import ccall "fmpq.h fmpq_neg"
  fmpq_neg :: Ptr CFmpq -> Ptr CFmpq -> IO ()

-- | /fmpq_abs/ /dest/ /src/ 
-- 
-- Sets @dest@ to the absolute value of @src@.
foreign import ccall "fmpq.h fmpq_abs"
  fmpq_abs :: Ptr CFmpq -> Ptr CFmpq -> IO ()

-- | /fmpq_zero/ /res/ 
-- 
-- Sets the value of @res@ to 0.
foreign import ccall "fmpq.h fmpq_zero"
  fmpq_zero :: Ptr CFmpq -> IO ()

-- | /fmpq_one/ /res/ 
-- 
-- Sets the value of @res@ to \(1\).
foreign import ccall "fmpq.h fmpq_one"
  fmpq_one :: Ptr CFmpq -> IO ()

-- Comparison ------------------------------------------------------------------

-- | /fmpq_is_zero/ /res/ 
-- 
-- Returns nonzero if @res@ has value 0, and returns zero otherwise.
foreign import ccall "fmpq.h fmpq_is_zero"
  fmpq_is_zero :: Ptr CFmpq -> IO CInt

-- | /fmpq_is_one/ /res/ 
-- 
-- Returns nonzero if @res@ has value \(1\), and returns zero otherwise.
foreign import ccall "fmpq.h fmpq_is_one"
  fmpq_is_one :: Ptr CFmpq -> IO CInt

-- | /fmpq_is_pm1/ /res/ 
-- 
-- Returns nonzero if @res@ has value \(\pm{1}\) and zero otherwise.
foreign import ccall "fmpq.h fmpq_is_pm1"
  fmpq_is_pm1 :: Ptr CFmpq -> IO CInt

-- | /fmpq_equal/ /x/ /y/ 
-- 
-- Returns nonzero if @x@ and @y@ are equal, and zero otherwise. Assumes
-- that @x@ and @y@ are both in canonical form.
foreign import ccall "fmpq.h fmpq_equal"
  fmpq_equal :: Ptr CFmpq -> Ptr CFmpq -> IO CInt

-- | /fmpq_sgn/ /x/ 
-- 
-- Returns the sign of the rational number \(x\).
foreign import ccall "fmpq.h fmpq_sgn"
  fmpq_sgn :: Ptr CFmpq -> IO CInt

-- | /fmpq_cmp/ /x/ /y/ 
-- 
-- Returns negative if \(x < y\), zero if \(x = y\), and positive if
-- \(x > y\).
foreign import ccall "fmpq.h fmpq_cmp"
  fmpq_cmp :: Ptr CFmpq -> Ptr CFmpq -> IO CInt

foreign import ccall "fmpq.h fmpq_cmp_fmpz"
  fmpq_cmp_fmpz :: Ptr CFmpq -> Ptr CFmpz -> IO CInt

foreign import ccall "fmpq.h fmpq_cmp_ui"
  fmpq_cmp_ui :: Ptr CFmpq -> Ptr CULong -> IO CInt

-- | /fmpq_cmp_si/ /x/ /y/ 
-- 
-- Returns negative if \(x < y\), zero if \(x = y\), and positive if
-- \(x > y\).
foreign import ccall "fmpq.h fmpq_cmp_si"
  fmpq_cmp_si :: Ptr CFmpq -> CLong -> IO CInt

-- | /fmpq_equal_ui/ /x/ /y/ 
-- 
-- Returns \(1\) if \(x = y\), otherwise returns \(0\).
foreign import ccall "fmpq.h fmpq_equal_ui"
  fmpq_equal_ui :: Ptr CFmpq -> CULong -> IO CInt

-- | /fmpq_equal_si/ /x/ /y/ 
-- 
-- Returns \(1\) if \(x = y\), otherwise returns \(0\).
foreign import ccall "fmpq.h fmpq_equal_si"
  fmpq_equal_si :: Ptr CFmpq -> CLong -> IO CInt

-- | /fmpq_height/ /height/ /x/ 
-- 
-- Sets @height@ to the height of \(x\), defined as the larger of the
-- absolute values of the numerator and denominator of \(x\).
foreign import ccall "fmpq.h fmpq_height"
  fmpq_height :: Ptr CFmpz -> Ptr CFmpq -> IO ()

-- | /fmpq_height_bits/ /x/ 
-- 
-- Returns the number of bits in the height of \(x\).
foreign import ccall "fmpq.h fmpq_height_bits"
  fmpq_height_bits :: Ptr CFmpq -> IO CFBitCnt

-- Conversion ------------------------------------------------------------------

-- | /fmpq_set_fmpz_frac/ /res/ /p/ /q/ 
-- 
-- Sets @res@ to the canonical form of the fraction @p \/ q@. This is
-- equivalent to assigning the numerator and denominator separately and
-- calling @fmpq_canonicalise@.
foreign import ccall "fmpq.h fmpq_set_fmpz_frac"
  fmpq_set_fmpz_frac :: Ptr CFmpq -> Ptr CFmpz -> Ptr CFmpz -> IO ()

foreign import ccall "fmpq.h fmpq_get_fmpz_frac"
  fmpq_get_fmpz_frac :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpq -> IO ()

-- | /fmpq_get_mpz_frac/ /a/ /b/ /c/ 
-- 
-- Sets @a@, @b@ to the numerator and denominator of @c@ respectively.
foreign import ccall "fmpq.h fmpq_get_mpz_frac"
  fmpq_get_mpz_frac :: Ptr CMpz -> Ptr CMpz -> Ptr CFmpq -> IO ()

-- | /fmpq_set_si/ /res/ /p/ /q/ 
-- 
-- Sets @res@ to the canonical form of the fraction @p \/ q@.
foreign import ccall "fmpq.h fmpq_set_si"
  fmpq_set_si :: Ptr CFmpq -> CLong -> CULong -> IO ()

-- | /_fmpq_set_si/ /rnum/ /rden/ /p/ /q/ 
-- 
-- Sets @(rnum, rden)@ to the canonical form of the fraction @p \/ q@.
-- @rnum@ and @rden@ may not be aliased.
foreign import ccall "fmpq.h _fmpq_set_si"
  _fmpq_set_si :: Ptr CFmpz -> Ptr CFmpz -> CLong -> CULong -> IO ()

-- | /fmpq_set_ui/ /res/ /p/ /q/ 
-- 
-- Sets @res@ to the canonical form of the fraction @p \/ q@.
foreign import ccall "fmpq.h fmpq_set_ui"
  fmpq_set_ui :: Ptr CFmpq -> CULong -> CULong -> IO ()

-- | /_fmpq_set_ui/ /rnum/ /rden/ /p/ /q/ 
-- 
-- Sets @(rnum, rden)@ to the canonical form of the fraction @p \/ q@.
-- @rnum@ and @rden@ may not be aliased.
foreign import ccall "fmpq.h _fmpq_set_ui"
  _fmpq_set_ui :: Ptr CFmpz -> Ptr CFmpz -> CULong -> CULong -> IO ()

-- | /fmpq_set_mpq/ /dest/ /src/ 
-- 
-- Sets the value of @dest@ to that of the @mpq_t@ variable @src@.
foreign import ccall "fmpq.h fmpq_set_mpq"
  fmpq_set_mpq :: Ptr CFmpq -> Ptr CMpq -> IO ()

-- | /fmpq_set_str/ /dest/ /s/ /base/ 
-- 
-- Sets the value of @dest@ to the value represented in the string @s@ in
-- base @base@.
-- 
-- Returns 0 if no error occurs. Otherwise returns -1 and @dest@ is set to
-- zero.
foreign import ccall "fmpq.h fmpq_set_str"
  fmpq_set_str :: Ptr CFmpq -> CString -> CInt -> IO CInt

-- | /fmpq_init_set_mpz_frac_readonly/ /z/ /p/ /q/ 
-- 
-- Assuming @z@ is an @fmpz_t@ which will not be cleaned up, this
-- temporarily copies @p@ and @q@ into the numerator and denominator of @z@
-- for read only operations only. The user must not run @fmpq_clear@ on
-- @z@.
foreign import ccall "fmpq.h fmpq_init_set_mpz_frac_readonly"
  fmpq_init_set_mpz_frac_readonly :: Ptr CFmpq -> Ptr CMpz -> Ptr CMpz -> IO ()

-- | /fmpq_get_d/ /f/ 
-- 
-- Returns \(f\) as a @double@, rounding towards zero if @f@ cannot be
-- represented exactly. The return is system dependent if @f@ is too large
-- or too small to fit in a @double@.
foreign import ccall "fmpq.h fmpq_get_d"
  fmpq_get_d :: Ptr CFmpq -> IO CDouble

-- | /fmpq_get_mpq/ /dest/ /src/ 
-- 
-- Sets the value of @dest@
foreign import ccall "fmpq.h fmpq_get_mpq"
  fmpq_get_mpq :: Ptr CMpq -> Ptr CFmpq -> IO ()

-- | /fmpq_get_mpfr/ /dest/ /src/ /rnd/ 
-- 
-- Sets the MPFR variable @dest@ to the value of @src@, rounded to the
-- nearest representable binary floating-point value in direction @rnd@.
-- Returns the sign of the rounding, according to MPFR conventions.
foreign import ccall "fmpq.h fmpq_get_mpfr"
  fmpq_get_mpfr :: Ptr CMpfr -> Ptr CFmpq -> CMpfrRnd -> IO CInt

-- | /_fmpq_get_str/ /str/ /b/ /num/ /den/ 
-- 
-- Prints the string representation of \(x\) in base \(b \in [2, 36]\) to a
-- suitable buffer.
-- 
-- If @str@ is not @NULL@, this is used as the buffer and also the return
-- value. If @str@ is @NULL@, allocates sufficient space and returns a
-- pointer to the string.
foreign import ccall "fmpq.h fmpq_get_str"
  fmpq_get_str :: CString -> CInt -> Ptr CFmpq -> IO CString

foreign import ccall "fmpq.h _fmpq_get_str"
  _fmpq_get_str :: CString -> CInt -> Ptr CFmpz -> Ptr CFmpz -> IO CString

-- | /flint_mpq_init_set_readonly/ /z/ /f/ 
-- 
-- Sets the uninitialised @mpq_t@ \(z\) to the value of the readonly
-- @fmpq_t@ \(f\).
-- 
-- Note that it is assumed that \(f\) does not change during the lifetime
-- of \(z\).
-- 
-- The rational \(z\) has to be cleared by a call to
-- @flint_mpq_clear_readonly@.
-- 
-- The suggested use of the two functions is as follows:
-- 
-- > fmpq_t f;
-- > ...
-- > {
-- >     mpq_t z;
-- >
-- >     flint_mpq_init_set_readonly(z, f);
-- >     foo(..., z);
-- >     flint_mpq_clear_readonly(z);
-- > }
-- 
-- This provides a convenient function for user code, only requiring to
-- work with the types @fmpq_t@ and @mpq_t@.
foreign import ccall "fmpq.h flint_mpq_init_set_readonly"
  flint_mpq_init_set_readonly :: Ptr CMpq -> Ptr CFmpq -> IO ()

-- | /flint_mpq_clear_readonly/ /z/ 
-- 
-- Clears the readonly @mpq_t@ \(z\).
foreign import ccall "fmpq.h flint_mpq_clear_readonly"
  flint_mpq_clear_readonly :: Ptr CMpq -> IO ()

-- | /fmpq_init_set_readonly/ /f/ /z/ 
-- 
-- Sets the uninitialised @fmpq_t@ \(f\) to a readonly version of the
-- rational \(z\).
-- 
-- Note that the value of \(z\) is assumed to remain constant throughout
-- the lifetime of \(f\).
-- 
-- The @fmpq_t@ \(f\) has to be cleared by calling the function
-- @fmpq_clear_readonly@.
-- 
-- The suggested use of the two functions is as follows:
-- 
-- > mpq_t z;
-- > ...
-- > {
-- >     fmpq_t f;
-- >
-- >     fmpq_init_set_readonly(f, z);
-- >     foo(..., f);
-- >     fmpq_clear_readonly(f);
-- > }
foreign import ccall "fmpq.h fmpq_init_set_readonly"
  fmpq_init_set_readonly :: Ptr CFmpq -> Ptr CMpq -> IO ()

-- | /fmpq_clear_readonly/ /f/ 
-- 
-- Clears the readonly @fmpq_t@ \(f\).
foreign import ccall "fmpq.h fmpq_clear_readonly"
  fmpq_clear_readonly :: Ptr CFmpq -> IO ()

-- Input and output ------------------------------------------------------------

-- | /fmpq_fprint/ /file/ /x/ 
-- 
-- Prints @x@ as a fraction to the stream @file@. The numerator and
-- denominator are printed verbatim as integers, with a forward slash (\/)
-- printed in between.
-- 
-- In case of success, returns a positive number. In case of failure,
-- returns a non-positive number.
foreign import ccall "fmpq.h fmpq_fprint"
  fmpq_fprint :: Ptr CFile -> Ptr CFmpq -> IO CInt

-- | /_fmpq_fprint/ /file/ /num/ /den/ 
-- 
-- Does the same thing as @fmpq_fprint@, but for numerator and denominator
-- given explicitly as @fmpz_t@ variables.
-- 
-- In case of success, returns a positive number. In case of failure,
-- returns a non-positive number.
foreign import ccall "fmpq.h _fmpq_fprint"
  _fmpq_fprint :: Ptr CFile -> Ptr CFmpz -> Ptr CFmpz -> IO CInt

-- | /fmpq_print/ /x/ 
-- 
-- Prints @x@ as a fraction. The numerator and denominator are printed
-- verbatim as integers, with a forward slash (\/) printed in between.
-- 
-- In case of success, returns a positive number. In case of failure,
-- returns a non-positive number.
fmpq_print :: Ptr CFmpq -> IO CInt
fmpq_print x = printCStr (fmpq_get_str nullPtr 10) x

-- | /_fmpq_print/ /num/ /den/ 
-- 
-- Does the same thing as @fmpq_print@, but for numerator and denominator
-- given explicitly as @fmpz_t@ variables.
-- 
-- In case of success, returns a positive number. In case of failure,
-- returns a non-positive number.
foreign import ccall "fmpq.h _fmpq_print"
  _fmpq_print :: Ptr CFmpz -> Ptr CFmpz -> IO CInt

-- Random number generation ----------------------------------------------------

-- | /fmpq_randtest/ /res/ /state/ /bits/ 
-- 
-- Sets @res@ to a random value, with numerator and denominator having up
-- to @bits@ bits. The fraction will be in canonical form. This function
-- has an increased probability of generating special values which are
-- likely to trigger corner cases.
foreign import ccall "fmpq.h fmpq_randtest"
  fmpq_randtest :: Ptr CFmpq -> Ptr CFRandState -> CFBitCnt -> IO ()

-- | /_fmpq_randtest/ /num/ /den/ /state/ /bits/ 
-- 
-- Does the same thing as @fmpq_randtest@, but for numerator and
-- denominator given explicitly as @fmpz_t@ variables. Aliasing of @num@
-- and @den@ is not allowed.
foreign import ccall "fmpq.h _fmpq_randtest"
  _fmpq_randtest :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFRandState -> CFBitCnt -> IO ()

-- | /fmpq_randtest_not_zero/ /res/ /state/ /bits/ 
-- 
-- As per @fmpq_randtest@, but the result will not be \(0\). If @bits@ is
-- set to \(0\), an exception will result.
foreign import ccall "fmpq.h fmpq_randtest_not_zero"
  fmpq_randtest_not_zero :: Ptr CFmpq -> Ptr CFRandState -> CFBitCnt -> IO ()

-- | /fmpq_randbits/ /res/ /state/ /bits/ 
-- 
-- Sets @res@ to a random value, with numerator and denominator both having
-- exactly @bits@ bits before canonicalisation, and then puts @res@ in
-- canonical form. Note that as a result of the canonicalisation, the
-- resulting numerator and denominator can be slightly smaller than @bits@
-- bits.
foreign import ccall "fmpq.h fmpq_randbits"
  fmpq_randbits :: Ptr CFmpq -> Ptr CFRandState -> CFBitCnt -> IO ()

-- | /_fmpq_randbits/ /num/ /den/ /state/ /bits/ 
-- 
-- Does the same thing as @fmpq_randbits@, but for numerator and
-- denominator given explicitly as @fmpz_t@ variables. Aliasing of @num@
-- and @den@ is not allowed.
foreign import ccall "fmpq.h _fmpq_randbits"
  _fmpq_randbits :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFRandState -> CFBitCnt -> IO ()

-- Arithmetic ------------------------------------------------------------------

-- | /fmpq_add/ /res/ /op1/ /op2/ 
-- 
-- Sets @res@ respectively to @op1 + op2@, @op1 - op2@, @op1 * op2@, or
-- @op1 \/ op2@. Assumes that the inputs are in canonical form, and
-- produces output in canonical form. Division by zero results in an error.
-- Aliasing between any combination of the variables is allowed.
foreign import ccall "fmpq.h fmpq_add"
  fmpq_add :: Ptr CFmpq -> Ptr CFmpq -> Ptr CFmpq -> IO ()

foreign import ccall "fmpq.h fmpq_sub"
  fmpq_sub :: Ptr CFmpq -> Ptr CFmpq -> Ptr CFmpq -> IO ()

foreign import ccall "fmpq.h fmpq_mul"
  fmpq_mul :: Ptr CFmpq -> Ptr CFmpq -> Ptr CFmpq -> IO ()

foreign import ccall "fmpq.h fmpq_div"
  fmpq_div :: Ptr CFmpq -> Ptr CFmpq -> Ptr CFmpq -> IO ()

-- | /_fmpq_add/ /rnum/ /rden/ /op1num/ /op1den/ /op2num/ /op2den/ 
-- 
-- Sets @(rnum, rden)@ to the canonical form of the sum, difference,
-- product or quotient respectively of the fractions represented by
-- @(op1num, op1den)@ and @(op2num, op2den)@. Aliasing between any
-- combination of the variables is allowed, whilst no numerator is aliased
-- with a denominator.
foreign import ccall "fmpq.h _fmpq_add"
  _fmpq_add :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

foreign import ccall "fmpq.h _fmpq_sub"
  _fmpq_sub :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

foreign import ccall "fmpq.h _fmpq_mul"
  _fmpq_mul :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

foreign import ccall "fmpq.h _fmpq_div"
  _fmpq_div :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /_fmpq_add_si/ /rnum/ /rden/ /p/ /q/ /r/ 
-- 
-- Sets @(rnum, rden)@ to the canonical form of the sum or difference
-- respectively of the fractions represented by @(p, q)@ and @(r, 1)@.
-- Numerators may not be aliased with denominators.
foreign import ccall "fmpq.h _fmpq_add_si"
  _fmpq_add_si :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

foreign import ccall "fmpq.h _fmpq_sub_si"
  _fmpq_sub_si :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

foreign import ccall "fmpq.h _fmpq_add_ui"
  _fmpq_add_ui :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

foreign import ccall "fmpq.h _fmpq_sub_ui"
  _fmpq_sub_ui :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

foreign import ccall "fmpq.h _fmpq_add_fmpz"
  _fmpq_add_fmpz :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

foreign import ccall "fmpq.h _fmpq_sub_fmpz"
  _fmpq_sub_fmpz :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpq_add_si/ /res/ /op1/ /c/ 
-- 
-- Sets @res@ to the sum or difference respectively, of the fraction @op1@
-- and the integer \(c\).
foreign import ccall "fmpq.h fmpq_add_si"
  fmpq_add_si :: Ptr CFmpq -> Ptr CFmpq -> CLong -> IO ()

foreign import ccall "fmpq.h fmpq_sub_si"
  fmpq_sub_si :: Ptr CFmpq -> Ptr CFmpq -> CLong -> IO ()

foreign import ccall "fmpq.h fmpq_add_ui"
  fmpq_add_ui :: Ptr CFmpq -> Ptr CFmpq -> CLong -> IO ()

foreign import ccall "fmpq.h fmpq_sub_ui"
  fmpq_sub_ui :: Ptr CFmpq -> Ptr CFmpq -> CLong -> IO ()

foreign import ccall "fmpq.h fmpq_sub_fmpz"
  fmpq_add_fmpz :: Ptr CFmpq -> Ptr CFmpq -> Ptr CFmpz -> IO ()

foreign import ccall "fmpq.h fmpq_sub_fmpz"
  fmpq_sub_fmpz :: Ptr CFmpq -> Ptr CFmpq -> Ptr CFmpz -> IO ()

-- | /_fmpq_mul_si/ /rnum/ /rden/ /p/ /q/ /r/ 
-- 
-- Sets @(rnum, rden)@ to the product of @(p, q)@ and the integer \(r\).
foreign import ccall "fmpq.h _fmpq_mul_si"
  _fmpq_mul_si :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- | /fmpq_mul_si/ /res/ /op1/ /c/ 
-- 
-- Sets @res@ to the product of @op1@ and the integer \(c\).
foreign import ccall "fmpq.h fmpq_mul_si"
  fmpq_mul_si :: Ptr CFmpq -> Ptr CFmpq -> CLong -> IO ()

-- | /_fmpq_mul_ui/ /rnum/ /rden/ /p/ /q/ /r/ 
-- 
-- Sets @(rnum, rden)@ to the product of @(p, q)@ and the integer \(r\).
foreign import ccall "fmpq.h _fmpq_mul_ui"
  _fmpq_mul_ui :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CULong -> IO ()

-- | /fmpq_mul_ui/ /res/ /op1/ /c/ 
-- 
-- Sets @res@ to the product of @op1@ and the integer \(c\).
foreign import ccall "fmpq.h fmpq_mul_ui"
  fmpq_mul_ui :: Ptr CFmpq -> Ptr CFmpq -> CULong -> IO ()

-- | /fmpq_addmul/ /res/ /op1/ /op2/ 
-- 
-- Sets @res@ to @res + op1 * op2@ or @res - op1 * op2@ respectively,
-- placing the result in canonical form. Aliasing between any combination
-- of the variables is allowed.
foreign import ccall "fmpq.h fmpq_addmul"
  fmpq_addmul :: Ptr CFmpq -> Ptr CFmpq -> Ptr CFmpq -> IO ()

foreign import ccall "fmpq.h fmpq_submul"
  fmpq_submul :: Ptr CFmpq -> Ptr CFmpq -> Ptr CFmpq -> IO ()

-- | /_fmpq_addmul/ /rnum/ /rden/ /op1num/ /op1den/ /op2num/ /op2den/ 
-- 
-- Sets @(rnum, rden)@ to the canonical form of the fraction @(rnum, rden)@
-- + @(op1num, op1den)@ * @(op2num, op2den)@ or @(rnum, rden)@ -
-- @(op1num, op1den)@ * @(op2num, op2den)@ respectively. Aliasing between
-- any combination of the variables is allowed, whilst no numerator is
-- aliased with a denominator.
foreign import ccall "fmpq.h _fmpq_addmul"
  _fmpq_addmul :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpq_inv/ /dest/ /src/ 
-- 
-- Sets @dest@ to @1 \/ src@. The result is placed in canonical form,
-- assuming that @src@ is already in canonical form.
foreign import ccall "fmpq.h fmpq_inv"
  fmpq_inv :: Ptr CFmpq -> Ptr CFmpq -> IO ()

-- | /_fmpq_pow_si/ /rnum/ /rden/ /opnum/ /opden/ /e/ 
-- 
-- Sets @res@ to @op@ raised to the power~\`e\`, where~\`e\` is a @slong@.
-- If \(e\) is \(0\) and @op@ is \(0\), then @res@ will be set to \(1\).
foreign import ccall "fmpq.h _fmpq_pow_si"
  _fmpq_pow_si :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

foreign import ccall "fmpq.h fmpq_pow_si"
  fmpq_pow_si :: Ptr CFmpq -> Ptr CFmpq -> CLong -> IO ()
  
-- | /fmpq_pow_fmpz/ /a/ /b/ /e/ 
-- 
-- Set @res@ to @op@ raised to the power~\`e\`. Return \(1\) for success
-- and \(0\) for failure.
foreign import ccall "fmpq.h fmpq_pow_fmpz"
  fmpq_pow_fmpz :: Ptr CFmpq -> Ptr CFmpq -> Ptr CFmpz -> IO CInt

-- | /fmpq_mul_fmpz/ /res/ /op/ /x/ 
-- 
-- Sets @res@ to the product of the rational number @op@ and the integer
-- @x@.
foreign import ccall "fmpq.h fmpq_mul_fmpz"
  fmpq_mul_fmpz :: Ptr CFmpq -> Ptr CFmpq -> Ptr CFmpz -> IO ()

-- | /fmpq_div_fmpz/ /res/ /op/ /x/ 
-- 
-- Sets @res@ to the quotient of the rational number @op@ and the integer
-- @x@.
foreign import ccall "fmpq.h fmpq_div_fmpz"
  fmpq_div_fmpz :: Ptr CFmpq -> Ptr CFmpq -> Ptr CFmpz -> IO ()

-- | /fmpq_mul_2exp/ /res/ /x/ /exp/ 
-- 
-- Sets @res@ to @x@ multiplied by @2^exp@.
foreign import ccall "fmpq.h fmpq_mul_2exp"
  fmpq_mul_2exp :: Ptr CFmpq -> Ptr CFmpq -> CFBitCnt -> IO ()

-- | /fmpq_div_2exp/ /res/ /x/ /exp/ 
-- 
-- Sets @res@ to @x@ divided by @2^exp@.
foreign import ccall "fmpq.h fmpq_div_2exp"
  fmpq_div_2exp :: Ptr CFmpq -> Ptr CFmpq -> CFBitCnt -> IO ()

-- | /_fmpq_gcd/ /rnum/ /rden/ /p/ /q/ /r/ /s/ 
-- 
-- Set @(rnum, rden)@ to the gcd of @(p, q)@ and @(r, s)@ which we define
-- to be the canonicalisation of gcd\`(ps, qr)\/(qs). (This is apparently
-- Euclid\'s original definition and is stable under scaling of numerator
-- and denominator. It also agrees with the gcd on the integers. Note that
-- it does not agree with gcd as defined in fmpq_poly\`.) This definition
-- agrees with the result as output by Sage and Pari\/GP.
foreign import ccall "fmpq.h _fmpq_gcd"
  _fmpq_gcd :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpq_gcd/ /res/ /op1/ /op2/ 
-- 
-- Set @res@ to the gcd of @op1@ and @op2@. See the low level function
-- @_fmpq_gcd@ for our definition of gcd.
foreign import ccall "fmpq.h fmpq_gcd"
  fmpq_gcd :: Ptr CFmpq -> Ptr CFmpq -> Ptr CFmpq -> IO ()

-- | /_fmpq_gcd_cofactors/ /gnum/ /gden/ /abar/ /bbar/ /anum/ /aden/ /bnum/ /bden/ 
-- 
-- Set \(g\) to \(\operatorname{gcd}(a,b)\) as per @fmpq_gcd@ and also
-- compute \(\overline{a} = a/g\) and \(\overline{b} = b/g\). Unlike
-- @fmpq_gcd@, this function requires canonical inputs.
foreign import ccall "fmpq.h _fmpq_gcd_cofactors"
  _fmpq_gcd_cofactors :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

foreign import ccall "fmpq.h fmpq_gcd_cofactors"
  fmpq_gcd_cofactors :: Ptr CFmpq -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpq -> Ptr CFmpq -> IO ()
  
-- | /_fmpq_add_small/ /rnum/ /rden/ /p1/ /q1/ /p2/ /q2/ 
-- 
-- Sets @(rnum, rden)@ to the sum of @(p1, q1)@ and @(p2, q2)@. Assumes
-- that @(p1, q1)@ and @(p2, q2)@ are in canonical form and that all inputs
-- are between @COEFF_MIN@ and @COEFF_MAX@.
foreign import ccall "fmpq.h _fmpq_add_small"
  _fmpq_add_small :: Ptr CFmpz -> Ptr CFmpz -> CLong -> CULong -> CLong -> CULong -> IO ()

-- | /_fmpq_mul_small/ /rnum/ /rden/ /p1/ /q1/ /p2/ /q2/ 
-- 
-- Sets @(rnum, rden)@ to the product of @(p1, q1)@ and @(p2, q2)@. Assumes
-- that @(p1, q1)@ and @(p2, q2)@ are in canonical form and that all inputs
-- are between @COEFF_MIN@ and @COEFF_MAX@.
foreign import ccall "fmpq.h _fmpq_mul_small"
  _fmpq_mul_small :: Ptr CFmpz -> Ptr CFmpz -> CLong -> CULong -> CLong -> CULong -> IO ()

-- Modular reduction and rational reconstruction -------------------------------

-- | /_fmpq_mod_fmpz/ /res/ /num/ /den/ /mod/ 
-- 
-- Sets the integer @res@ to the residue \(a\) of \(x = n/d\) =
-- @(num, den)@ modulo the positive integer \(m\) = @mod@, defined as the
-- \(0 \le a < m\) satisfying \(n \equiv a d \pmod m\). If such an \(a\)
-- exists, 1 will be returned, otherwise 0 will be returned.
foreign import ccall "fmpq.h _fmpq_mod_fmpz"
  _fmpq_mod_fmpz :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO CInt

foreign import ccall "fmpq.h fmpq_mod_fmpz"
  fmpq_mod_fmpz :: Ptr CFmpz -> Ptr CFmpq -> Ptr CFmpz -> IO CInt
  
-- | /_fmpq_reconstruct_fmpz_2_naive/ /n/ /d/ /a/ /m/ /N/ /D/ 
-- 
-- Reconstructs a rational number from its residue \(a\) modulo \(m\).
-- 
-- Given a modulus \(m > 2\), a residue \(0 \le a < m\), and positive
-- \(N, D\) satisfying \(2ND < m\), this function attempts to find a
-- fraction \(n/d\) with \(0 \le |n| \le N\) and \(0 < d \le D\) such that
-- \(\gcd(n,d) = 1\) and \(n \equiv ad \pmod m\). If a solution exists,
-- then it is also unique. The function returns 1 if successful, and 0 to
-- indicate that no solution exists.
foreign import ccall "fmpq.h _fmpq_reconstruct_fmpz_2_naive"
  _fmpq_reconstruct_fmpz_2_naive :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO CInt

foreign import ccall "fmpq.h _fmpq_reconstruct_fmpz_2"
  _fmpq_reconstruct_fmpz_2 :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

foreign import ccall "fmpq.h fmpq_reconstruct_fmpz_2"
  fmpq_reconstruct_fmpz_2 :: Ptr CFmpq -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()
  
-- | /_fmpq_reconstruct_fmpz/ /n/ /d/ /a/ /m/ 
-- 
-- Reconstructs a rational number from its residue \(a\) modulo \(m\),
-- returning 1 if successful and 0 if no solution exists. Uses the balanced
-- bounds \(N = D = \lfloor\sqrt{\frac{m-1}{2}}\rfloor\).
foreign import ccall "fmpq.h _fmpq_reconstruct_fmpz"
  _fmpq_reconstruct_fmpz :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO CInt

foreign import ccall "fmpq fmpq_reconstruct_fmpz"
  fmpq_reconstruct_fmpz :: Ptr CFmpq -> Ptr CFmpz -> Ptr CFmpz -> IO ()
  
-- Rational enumeration --------------------------------------------------------

-- | /_fmpq_next_minimal/ /rnum/ /rden/ /num/ /den/ 
-- 
-- Given \(x\) which is assumed to be nonnegative and in canonical form,
-- sets @res@ to the next rational number in the sequence obtained by
-- enumerating all positive denominators \(q\), for each \(q\) enumerating
-- the numerators \(1 \le p < q\) in order and generating both \(p/q\) and
-- \(q/p\), but skipping all \(\gcd(p,q) \ne 1\). Starting with zero, this
-- generates every nonnegative rational number once and only once, with the
-- first few entries being:
-- 
-- \(0, 1, 1/2, 2, 1/3, 3, 2/3, 3/2, 1/4, 4, 3/4, 4/3, 1/5, 5, 2/5, \ldots.\)
-- 
-- This enumeration produces the rational numbers in order of minimal
-- height. It has the disadvantage of being somewhat slower to compute than
-- the Calkin-Wilf enumeration.
foreign import ccall "fmpq.h _fmpq_next_minimal"
  _fmpq_next_minimal :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /_fmpq_next_signed_minimal/ /rnum/ /rden/ /num/ /den/ 
-- 
-- Given a signed rational number \(x\) assumed to be in canonical form,
-- sets @res@ to the next element in the minimal-height sequence generated
-- by @fmpq_next_minimal@ but with negative numbers interleaved:
-- 
-- \(0, 1, -1, 1/2, -1/2, 2, -2, 1/3, -1/3, \ldots.\)
-- 
-- Starting with zero, this generates every rational number once and only
-- once, in order of minimal height.
foreign import ccall "fmpq.h _fmpq_next_signed_minimal"
  _fmpq_next_signed_minimal :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /_fmpq_next_calkin_wilf/ /rnum/ /rden/ /num/ /den/ 
-- 
-- Given \(x\) which is assumed to be nonnegative and in canonical form,
-- sets @res@ to the next number in the breadth-first traversal of the
-- Calkin-Wilf tree. Starting with zero, this generates every nonnegative
-- rational number once and only once, with the first few entries being:
-- 
-- \(0, 1, 1/2, 2, 1/3, 3/2, 2/3, 3, 1/4, 4/3, 3/5, 5/2, 2/5, \ldots.\)
-- 
-- Despite the appearance of the initial entries, the Calkin-Wilf
-- enumeration does not produce the rational numbers in order of height:
-- some small fractions will appear late in the sequence. This order has
-- the advantage of being faster to produce than the minimal-height order.
foreign import ccall "fmpq.h _fmpq_next_calkin_wilf"
  _fmpq_next_calkin_wilf :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /_fmpq_next_signed_calkin_wilf/ /rnum/ /rden/ /num/ /den/ 
-- 
-- Given a signed rational number \(x\) assumed to be in canonical form,
-- sets @res@ to the next element in the Calkin-Wilf sequence with negative
-- numbers interleaved:
-- 
-- \(0, 1, -1, 1/2, -1/2, 2, -2, 1/3, -1/3, \ldots.\)
-- 
-- Starting with zero, this generates every rational number once and only
-- once, but not in order of minimal height.
foreign import ccall "fmpq.h _fmpq_next_signed_calkin_wilf"
  _fmpq_next_signed_calkin_wilf :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /fmpq_farey_neighbors/ /l/ /r/ /x/ /Q/ 
-- 
-- Set \(l\) and \(r\) to the fractions directly below and above \(x\) in
-- the Farey sequence of order \(Q\). This function will throw if \(x\) is
-- not canonical or \(Q\) is less than the denominator of \(x\).
foreign import ccall "fmpq.h fmpq_farey_neighbors"
  fmpq_farey_neighbors :: Ptr CFmpq -> Ptr CFmpq -> Ptr CFmpq -> Ptr CFmpz -> IO ()

-- | /fmpq_simplest_between/ /x/ /l/ /r/ 
-- 
-- Set \(x\) to the simplest fraction in the closed interval \([l, r]\).
-- The underscore version makes the additional assumption that \(l \le r\).
-- The endpoints \(l\) and \(r\) do not need to be reduced, but their
-- denominators do need to be positive. \(x\) will be always be returned in
-- canonical form. A canonical fraction \(a_1/b_1\) is defined to be
-- simpler than \(a_2/b_2\) iff \(b_1<b_2\) or \(b_1=b_2\) and \(a_1<a_2\).
foreign import ccall "fmpq.h fmpq_simplest_between"
  fmpq_simplest_between :: Ptr CFmpq -> Ptr CFmpq -> Ptr CFmpq -> IO ()

-- Continued fractions ---------------------------------------------------------

-- | /fmpq_get_cfrac/ /c/ /rem/ /x/ /n/ 
-- 
-- Generates up to \(n\) terms of the (simple) continued fraction expansion
-- of \(x\), writing the coefficients to the vector \(c\) and the remainder
-- \(r\) to the @rem@ variable. The return value is the number \(k\) of
-- generated terms. The output satisfies
-- 
-- \[`\]
-- \[x = c_0 + \cfrac{1}{c_1 + \cfrac{1}{c_2 +
--     \cfrac{1}{ \ddots + \cfrac{1}{c_{k-1} + r }}}}\]
-- 
-- If \(r\) is zero, the continued fraction expansion is complete. If \(r\)
-- is nonzero, \(1/r\) can be passed back as input to generate
-- \(c_k, c_{k+1}, \ldots\). Calls to @fmpq_get_cfrac@ can therefore be
-- chained to generate the continued fraction incrementally, extracting any
-- desired number of coefficients at a time.
-- 
-- In general, a rational number has exactly two continued fraction
-- expansions. By convention, we generate the shorter one. The longer
-- expansion can be obtained by replacing the last coefficient \(a_{k-1}\)
-- by the pair of coefficients \(a_{k-1} - 1, 1\).
-- 
-- [The behaviour of this function in corner cases is as follows:]
--     -   if \(x\) is infinite (anything over 0), @rem@ will be zero and
--         the return is \(k=0\) regardless of \(n\).
-- 
--     -   [else (if \(x\) is finite),]
--             -   if \(n <= 0\), @rem@ will be \(1/x\) (allowing for
--                 infinite in the case \(x=0\)) and the return is \(k=0\)
--             -   else (if \(n > 0\)), @rem@ will finite and the return is
--                 \(0 < k \le n\).
-- 
-- Essentially, if this function is called with canonical \(x\) and
-- \(n > 0\), then @rem@ will be canonical. Therefore, applications relying
-- on canonical @fmpq_t@\'s should not call this function with \(n <= 0\).
foreign import ccall "fmpq.h fmpq_get_cfrac"
  fmpq_get_cfrac :: Ptr CFmpz -> Ptr CFmpq -> Ptr CFmpq -> CLong -> IO CLong

-- | /fmpq_set_cfrac/ /x/ /c/ /n/ 
-- 
-- Sets \(x\) to the value of the continued fraction
-- 
-- \[`\]
-- \[x = c_0 + \cfrac{1}{c_1 + \cfrac{1}{c_2 +
--     \cfrac{1}{ \ddots + \cfrac{1}{c_{n-1}}}}}\]
-- 
-- where all \(c_i\) except \(c_0\) should be nonnegative. It is assumed
-- that \(n > 0\).
-- 
-- For large \(n\), this function implements a subquadratic algorithm. The
-- convergents are given by a chain product of 2 by 2 matrices. This
-- product is split in half recursively to balance the size of the
-- coefficients.
foreign import ccall "fmpq.h fmpq_set_cfrac"
  fmpq_set_cfrac :: Ptr CFmpq -> Ptr CFmpz -> CLong -> IO ()

-- | /fmpq_cfrac_bound/ /x/ 
-- 
-- Returns an upper bound for the number of terms in the continued fraction
-- expansion of \(x\). The computed bound is not necessarily sharp.
-- 
-- We use the fact that the smallest denominator that can give a continued
-- fraction of length \(n\) is the Fibonacci number \(F_{n+1}\).
foreign import ccall "fmpq.h fmpq_cfrac_bound"
  fmpq_cfrac_bound :: Ptr CFmpq -> IO CLong

-- Special functions -----------------------------------------------------------

-- | /_fmpq_harmonic_ui/ /num/ /den/ /n/ 
-- 
-- Computes the harmonic number \(H_n = 1 + 1/2 + 1/3 + \dotsb + 1/n\).
-- Table lookup is used for \(H_n\) whose numerator and denominator fit in
-- single limb. For larger \(n\), a divide and conquer strategy is used.
foreign import ccall "fmpq.h _fmpq_harmonic_ui"
  _fmpq_harmonic_ui :: Ptr CFmpz -> Ptr CFmpz -> CULong -> IO ()

foreign import ccall "fmpq.h fmpq_harmonic_ui"
  fmpq_harmonic_ui ::Ptr CFmpq -> CULong -> IO ()
  
-- Dedekind sums ---------------------------------------------------------------

-- Most of the definitions and relations used in the following section are
-- given by Apostol < [Apostol1997]>. The Dedekind sum \(s(h,k)\) is
-- defined for all integers \(h\) and \(k\) as
--
-- \[`\]
-- \[s(h,k) = \sum_{i=1}^{k-1} \left(\left(\frac{i}{k}\right)\right)
-- \left(\left(\frac{hi}{k}\right)\right)\]
--
-- where
--
-- \[`\]
-- \[\begin{aligned}
-- ((x))=\begin{cases}
-- x-\lfloor x\rfloor-1/2 &\mbox{if }
-- x\in\mathbf{Q}\setminus\mathbf{Z}\\
-- 0 &\mbox{if }x\in\mathbf{Z}.
-- \end{cases}
-- \end{aligned}\]
--
-- If \(0 < h < k\) and \((h,k) = 1\), this reduces to
--
-- \[`\]
-- \[s(h,k) = \sum_{i=1}^{k-1} \frac{i}{k}
--     \left(\frac{hi}{k}-\left\lfloor\frac{hi}{k}\right\rfloor
--     -\frac{1}{2}\right).\]
--
-- The main formula for evaluating the series above is the following.
-- Letting \(r_0 = k\), \(r_1 = h\), \(r_2, r_3, \ldots, r_n, r_{n+1} = 1\)
-- be the remainder sequence in the Euclidean algorithm for computing GCD
-- of \(h\) and \(k\),
--
-- \[`
-- s(h,k) = \frac{1-(-1)^n}{8} - \frac{1}{12} \sum_{i=1}^{n+1}
-- (-1)^i \left(\frac{1+r_i^2+r_{i-1}^2}{r_i r_{i-1}}\right).\]
--
-- Writing \(s(h,k) = p/q\), some useful properties employed are |s| \< k
-- \/ 12, \(q | 6k\) and \(2|p| < k^2\).
--
-- | /fmpq_dedekind_sum/ /s/ /h/ /k/ 
-- 
-- Computes \(s(h,k)\) for arbitrary \(h\) and \(k\). The naive version
-- uses a straightforward implementation of the defining sum using @fmpz@
-- arithmetic and is slow for large \(k\).
foreign import ccall "fmpq.h fmpq_dedekind_sum"
  fmpq_dedekind_sum :: Ptr CFmpq -> Ptr CFmpz -> Ptr CFmpz -> IO ()

foreign import ccall "fmpq.h fmpq_dedekind_sum_naive"
  fmpq_dedekind_sum_naive :: Ptr CFmpq -> Ptr CFmpz -> Ptr CFmpz -> IO ()
