
module Data.Number.Flint.Fmpz.Vec.FFI (
  -- * Vectors of integers
  -- * Memory management
    _fmpz_vec_init
  , _fmpz_vec_clear
  -- * Randomisation
  , _fmpz_vec_randtest
  , _fmpz_vec_randtest_unsigned
  -- * Bit sizes and norms
  , _fmpz_vec_max_bits
  , _fmpz_vec_max_bits_ref
  , _fmpz_vec_sum_max_bits
  , _fmpz_vec_max_limbs
  , _fmpz_vec_height
  , _fmpz_vec_height_index
  -- * Input and output
  , _fmpz_vec_fread
  , _fmpz_vec_read
  , _fmpz_vec_fprint
  , _fmpz_vec_print
  -- * Conversions
  , _fmpz_vec_get_nmod_vec
  , _fmpz_vec_set_nmod_vec
  , _fmpz_vec_get_fft
  , _fmpz_vec_set_fft
  , _fmpz_vec_get_d_vec_2exp
  -- , _fmpz_vec_get_mpf_vec
  -- * Assignment and basic manipulation
  , _fmpz_vec_set
  , _fmpz_vec_swap
  , _fmpz_vec_zero
  , _fmpz_vec_neg
  , _fmpz_vec_scalar_abs
  -- * Comparison
  , _fmpz_vec_equal
  , _fmpz_vec_is_zero
  , _fmpz_vec_max
  , _fmpz_vec_max_inplace
  -- * Sorting
  , _fmpz_vec_sort
  -- * Addition and subtraction
  , _fmpz_vec_add
  , _fmpz_vec_sub
  -- * Scalar multiplication and division
  , _fmpz_vec_scalar_mul_fmpz
  , _fmpz_vec_scalar_mul_si
  , _fmpz_vec_scalar_mul_ui
  , _fmpz_vec_scalar_mul_2exp
  , _fmpz_vec_scalar_divexact_fmpz
  , _fmpz_vec_scalar_divexact_si
  , _fmpz_vec_scalar_divexact_ui
  , _fmpz_vec_scalar_fdiv_q_fmpz
  , _fmpz_vec_scalar_fdiv_q_si
  , _fmpz_vec_scalar_fdiv_q_ui
  , _fmpz_vec_scalar_fdiv_q_2exp
  , _fmpz_vec_scalar_fdiv_r_2exp
  , _fmpz_vec_scalar_tdiv_q_fmpz
  , _fmpz_vec_scalar_tdiv_q_si
  , _fmpz_vec_scalar_tdiv_q_ui
  , _fmpz_vec_scalar_tdiv_q_2exp
  , _fmpz_vec_scalar_addmul_si
  , _fmpz_vec_scalar_addmul_ui
  , _fmpz_vec_scalar_addmul_fmpz
  , _fmpz_vec_scalar_addmul_si_2exp
  , _fmpz_vec_scalar_submul_fmpz
  , _fmpz_vec_scalar_submul_si
  , _fmpz_vec_scalar_submul_si_2exp
  -- * Sums and products
  , _fmpz_vec_sum
  , _fmpz_vec_prod
  -- * Reduction mod \(p\)
  , _fmpz_vec_scalar_mod_fmpz
  , _fmpz_vec_scalar_smod_fmpz
  -- * Gaussian content
  , _fmpz_vec_content
  , _fmpz_vec_content_chained
  , _fmpz_vec_lcm
  -- * Dot product
  , _fmpz_vec_dot
  , _fmpz_vec_dot_ptr
) where 

-- vectors of integers ---------------------------------------------------------

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr, nullPtr, castPtr )
import Foreign.Storable
import Foreign.Marshal ( free )

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.NMod

#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpz_vec.h>

-- Memory management -----------------------------------------------------------

-- | /_fmpz_vec_init/ /len/ 
-- 
-- Returns an initialised vector of @fmpz@\'s of given length.
foreign import ccall "fmpz_vec.h _fmpz_vec_init"
  _fmpz_vec_init :: CLong -> IO (Ptr CFmpz)

-- | /_fmpz_vec_clear/ /vec/ /len/ 
-- 
-- Clears the entries of @(vec, len)@ and frees the space allocated for
-- @vec@.
foreign import ccall "fmpz_vec.h _fmpz_vec_clear"
  _fmpz_vec_clear :: Ptr CFmpz -> CLong -> IO ()

-- Randomisation ---------------------------------------------------------------

-- | /_fmpz_vec_randtest/ /f/ /state/ /len/ /bits/ 
-- 
-- Sets the entries of a vector of the given length to random integers with
-- up to the given number of bits per entry.
foreign import ccall "fmpz_vec.h _fmpz_vec_randtest"
  _fmpz_vec_randtest :: Ptr CFmpz -> Ptr CFRandState -> CLong -> CFBitCnt -> IO ()

-- | /_fmpz_vec_randtest_unsigned/ /f/ /state/ /len/ /bits/ 
-- 
-- Sets the entries of a vector of the given length to random unsigned
-- integers with up to the given number of bits per entry.
foreign import ccall "fmpz_vec.h _fmpz_vec_randtest_unsigned"
  _fmpz_vec_randtest_unsigned :: Ptr CFmpz -> Ptr CFRandState -> CLong -> CFBitCnt -> IO ()

-- Bit sizes and norms ---------------------------------------------------------

-- | /_fmpz_vec_max_bits/ /vec/ /len/ 
-- 
-- If \(b\) is the maximum number of bits of the absolute value of any
-- coefficient of @vec@, then if any coefficient of @vec@ is negative,
-- \(-b\) is returned, else \(b\) is returned.
foreign import ccall "fmpz_vec.h _fmpz_vec_max_bits"
  _fmpz_vec_max_bits :: Ptr CFmpz -> CLong -> IO CLong

-- | /_fmpz_vec_max_bits_ref/ /vec/ /len/ 
-- 
-- If \(b\) is the maximum number of bits of the absolute value of any
-- coefficient of @vec@, then if any coefficient of @vec@ is negative,
-- \(-b\) is returned, else \(b\) is returned. This is a slower reference
-- implementation of @_fmpz_vec_max_bits@.
foreign import ccall "fmpz_vec.h _fmpz_vec_max_bits_ref"
  _fmpz_vec_max_bits_ref :: Ptr CFmpz -> CLong -> IO CLong

-- | /_fmpz_vec_sum_max_bits/ /sumabs/ /maxabs/ /vec/ /len/ 
-- 
-- Sets @sumabs@ to the bit count of the sum of the absolute values of the
-- elements of @vec@. Sets @maxabs@ to the bit count of the maximum of the
-- absolute values of the elements of @vec@.
foreign import ccall "fmpz_vec.h _fmpz_vec_sum_max_bits"
  _fmpz_vec_sum_max_bits :: Ptr CLong -> Ptr CLong -> Ptr CFmpz -> CLong -> IO ()

-- | /_fmpz_vec_max_limbs/ /vec/ /len/ 
-- 
-- Returns the maximum number of limbs needed to store the absolute value
-- of any entry in @(vec, len)@. If all entries are zero, returns zero.
foreign import ccall "fmpz_vec.h _fmpz_vec_max_limbs"
  _fmpz_vec_max_limbs :: Ptr CFmpz -> CLong -> IO CULong

-- | /_fmpz_vec_height/ /height/ /vec/ /len/ 
-- 
-- Computes the height of @(vec, len)@, defined as the largest of the
-- absolute values the coefficients. Equivalently, this gives the infinity
-- norm of the vector. If @len@ is zero, the height is \(0\).
foreign import ccall "fmpz_vec.h _fmpz_vec_height"
  _fmpz_vec_height :: Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- | /_fmpz_vec_height_index/ /vec/ /len/ 
-- 
-- Returns the index of an entry of maximum absolute value in the vector.
-- The the length must be at least 1.
foreign import ccall "fmpz_vec.h _fmpz_vec_height_index"
  _fmpz_vec_height_index :: Ptr CFmpz -> CLong -> IO CLong

-- Input and output ------------------------------------------------------------

foreign import ccall "_fmpz_vec_get_str"
  _fmpz_vec_get_str :: CLong -> Ptr CFmpz -> IO (CString)

-- | /_fmpz_vec_fread/ /file/ /vec/ /len/ 
-- 
-- Reads a vector from the stream @file@ and stores it at @*vec@. The
-- format is the same as the output format of @_fmpz_vec_fprint()@,
-- followed by either any character or the end of the file.
-- 
-- The interpretation of the various input arguments depends on whether or
-- not @*vec@ is @NULL@:
-- 
-- If @*vec == NULL@, the value of @*len@ on input is ignored. Once the
-- length has been read from @file@, @*len@ is set to that value and a
-- vector of this length is allocated at @*vec@. Finally, @*len@
-- coefficients are read from the input stream. In case of a file or
-- parsing error, clears the vector and sets @*vec@ and @*len@ to @NULL@
-- and @0@, respectively.
-- 
-- Otherwise, if @*vec != NULL@, it is assumed that @(*vec, *len)@ is a
-- properly initialised vector. If the length on the input stream does not
-- match @*len@, a parsing error is raised. Attempts to read the right
-- number of coefficients from the input stream. In case of a file or
-- parsing error, leaves the vector @(*vec, *len)@ in its current state.
-- 
-- In case of success, returns a positive value. In case of failure,
-- returns a non-positive value.
foreign import ccall "fmpz_vec.h _fmpz_vec_fread"
  _fmpz_vec_fread :: Ptr CFile -> Ptr CFmpz -> Ptr CLong -> IO CInt

-- | /_fmpz_vec_read/ /vec/ /len/ 
-- 
-- Reads a vector from @stdin@ and stores it at @*vec@.
-- 
-- For further details, see @_fmpz_vec_fread()@.
foreign import ccall "fmpz_vec.h _fmpz_vec_read"
  _fmpz_vec_read :: Ptr CFmpz -> Ptr CLong -> IO CInt

-- | /_fmpz_vec_fprint/ /file/ /vec/ /len/ 
-- 
-- Prints the vector of given length to the stream @file@. The format is
-- the length followed by two spaces, then a space separated list of
-- coefficients. If the length is zero, only \(0\) is printed.
-- 
-- In case of success, returns a positive value. In case of failure,
-- returns a non-positive value.
foreign import ccall "fmpz_vec.h _fmpz_vec_fprint"
  _fmpz_vec_fprint :: Ptr CFile -> Ptr CFmpz -> CLong -> IO CInt

-- | /_fmpz_vec_print/ /vec/ /len/ 
-- 
-- Prints the vector of given length to @stdout@.
-- 
-- For further details, see @_fmpz_vec_fprint()@.
_fmpz_vec_print :: Ptr CFmpz -> CLong -> IO CInt
_fmpz_vec_print x n = printCStr (_fmpz_vec_get_str n) x

-- Conversions -----------------------------------------------------------------

-- | /_fmpz_vec_get_nmod_vec/ /res/ /poly/ /len/ /mod/ 
-- 
-- Reduce the coefficients of @(poly, len)@ modulo the given modulus and
-- set @(res, len)@ to the result.
foreign import ccall "fmpz_vec.h _fmpz_vec_get_nmod_vec"
  _fmpz_vec_get_nmod_vec :: Ptr CMp -> Ptr CFmpz -> CLong -> Ptr CNMod -> IO ()

-- | /_fmpz_vec_set_nmod_vec/ /res/ /poly/ /len/ /mod/ 
-- 
-- Set the coefficients of @(res, len)@ to the symmetric modulus of the
-- coefficients of @(poly, len)@, i.e. convert the given coefficients
-- modulo the given modulus \(n\) to their signed integer representatives
-- in the range \([-n/2, n/2)\).
foreign import ccall "fmpz_vec.h _fmpz_vec_set_nmod_vec"
  _fmpz_vec_set_nmod_vec :: Ptr CFmpz -> Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /_fmpz_vec_get_fft/ /coeffs_f/ /coeffs_m/ /l/ /length/ 
-- 
-- Convert the vector of coeffs @coeffs_m@ to an fft vector @coeffs_f@ of
-- the given @length@ with @l@ limbs per coefficient with an additional
-- limb for overflow.
foreign import ccall "fmpz_vec.h _fmpz_vec_get_fft"
  _fmpz_vec_get_fft :: Ptr (Ptr CMpLimb) -> Ptr CFmpz -> CLong -> CLong -> IO CLong

-- | /_fmpz_vec_set_fft/ /coeffs_m/ /length/ /coeffs_f/ /limbs/ /sign/ 
-- 
-- Convert an fft vector @coeffs_f@ of fully reduced Fermat numbers of the
-- given @length@ to a vector of @fmpz@\'s. Each is assumed to be the given
-- number of limbs in length with an additional limb for overflow. If the
-- output coefficients are to be signed then set @sign@, otherwise clear
-- it. The resulting @fmpz@s will be in the range \([-n,n]\) in the signed
-- case and in the range \([0,2n]\) in the unsigned case where
-- @n = 2^(FLINT_BITS*limbs - 1)@.
foreign import ccall "fmpz_vec.h _fmpz_vec_set_fft"
  _fmpz_vec_set_fft :: Ptr CFmpz -> CLong -> Ptr CMp -> CLong -> CLong -> IO ()

-- | /_fmpz_vec_get_d_vec_2exp/ /appv/ /vec/ /len/ 
-- 
-- Export the array of @len@ entries starting at the pointer @vec@ to an
-- array of doubles @appv@, each entry of which is notionally multiplied by
-- a single returned exponent to give the original entry. The returned
-- exponent is set to be the maximum exponent of all the original entries
-- so that all the doubles in @appv@ have a maximum absolute value of 1.0.
foreign import ccall "fmpz_vec.h _fmpz_vec_get_d_vec_2exp"
  _fmpz_vec_get_d_vec_2exp :: Ptr CDouble -> Ptr CFmpz -> CLong -> IO CLong

-- -- | /_fmpz_vec_get_mpf_vec/ /appv/ /vec/ /len/ 
-- -- 
-- -- Export the array of @len@ entries starting at the pointer @vec@ to an
-- -- array of mpfs @appv@.
-- foreign import ccall "fmpz_vec.h _fmpz_vec_get_mpf_vec"
--   _fmpz_vec_get_mpf_vec :: Ptr CMpf -> Ptr CFmpz -> CLong -> IO ()

-- Assignment and basic manipulation -------------------------------------------

-- | /_fmpz_vec_set/ /vec1/ /vec2/ /len2/ 
-- 
-- Makes a copy of @(vec2, len2)@ into @vec1@.
foreign import ccall "fmpz_vec.h _fmpz_vec_set"
  _fmpz_vec_set :: Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- | /_fmpz_vec_swap/ /vec1/ /vec2/ /len2/ 
-- 
-- Swaps the integers in @(vec1, len2)@ and @(vec2, len2)@.
foreign import ccall "fmpz_vec.h _fmpz_vec_swap"
  _fmpz_vec_swap :: Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- | /_fmpz_vec_zero/ /vec/ /len/ 
-- 
-- Zeros the entries of @(vec, len)@.
foreign import ccall "fmpz_vec.h _fmpz_vec_zero"
  _fmpz_vec_zero :: Ptr CFmpz -> CLong -> IO ()

-- | /_fmpz_vec_neg/ /vec1/ /vec2/ /len2/ 
-- 
-- Negates @(vec2, len2)@ and places it into @vec1@.
foreign import ccall "fmpz_vec.h _fmpz_vec_neg"
  _fmpz_vec_neg :: Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- | /_fmpz_vec_scalar_abs/ /vec1/ /vec2/ /len2/ 
-- 
-- Takes the absolute value of entries in @(vec2, len2)@ and places the
-- result into @vec1@.
foreign import ccall "fmpz_vec.h _fmpz_vec_scalar_abs"
  _fmpz_vec_scalar_abs :: Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- Comparison ------------------------------------------------------------------

-- | /_fmpz_vec_equal/ /vec1/ /vec2/ /len/ 
-- 
-- Compares two vectors of the given length and returns \(1\) if they are
-- equal, otherwise returns \(0\).
foreign import ccall "fmpz_vec.h _fmpz_vec_equal"
  _fmpz_vec_equal :: Ptr CFmpz -> Ptr CFmpz -> CLong -> IO CInt

-- | /_fmpz_vec_is_zero/ /vec/ /len/ 
-- 
-- Returns \(1\) if @(vec, len)@ is zero, and \(0\) otherwise.
foreign import ccall "fmpz_vec.h _fmpz_vec_is_zero"
  _fmpz_vec_is_zero :: Ptr CFmpz -> CLong -> IO CInt

-- | /_fmpz_vec_max/ /vec1/ /vec2/ /vec3/ /len/ 
-- 
-- Sets @vec1@ to the pointwise maximum of @vec2@ and @vec3@.
foreign import ccall "fmpz_vec.h _fmpz_vec_max"
  _fmpz_vec_max :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- | /_fmpz_vec_max_inplace/ /vec1/ /vec2/ /len/ 
-- 
-- Sets @vec1@ to the pointwise maximum of @vec1@ and @vec2@.
foreign import ccall "fmpz_vec.h _fmpz_vec_max_inplace"
  _fmpz_vec_max_inplace :: Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- Sorting ---------------------------------------------------------------------

-- | /_fmpz_vec_sort/ /vec/ /len/ 
-- 
-- Sorts the coefficients of @vec@ in ascending order.
foreign import ccall "fmpz_vec.h _fmpz_vec_sort"
  _fmpz_vec_sort :: Ptr CFmpz -> CLong -> IO ()

-- Addition and subtraction ----------------------------------------------------

-- | /_fmpz_vec_add/ /res/ /vec1/ /vec2/ /len2/ 
-- 
-- Sets @(res, len2)@ to the sum of @(vec1, len2)@ and @(vec2, len2)@.
foreign import ccall "fmpz_vec.h _fmpz_vec_add"
  _fmpz_vec_add :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- | /_fmpz_vec_sub/ /res/ /vec1/ /vec2/ /len2/ 
-- 
-- Sets @(res, len2)@ to @(vec1, len2)@ minus @(vec2, len2)@.
foreign import ccall "fmpz_vec.h _fmpz_vec_sub"
  _fmpz_vec_sub :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- Scalar multiplication and division ------------------------------------------

-- | /_fmpz_vec_scalar_mul_fmpz/ /vec1/ /vec2/ /len2/ /x/ 
-- 
-- Sets @(vec1, len2)@ to @(vec2, len2)@ multiplied by \(c\), where \(c\)
-- is an @fmpz_t@.
foreign import ccall "fmpz_vec.h _fmpz_vec_scalar_mul_fmpz"
  _fmpz_vec_scalar_mul_fmpz :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /_fmpz_vec_scalar_mul_si/ /vec1/ /vec2/ /len2/ /c/ 
-- 
-- Sets @(vec1, len2)@ to @(vec2, len2)@ multiplied by \(c\), where \(c\)
-- is a @slong@.
foreign import ccall "fmpz_vec.h _fmpz_vec_scalar_mul_si"
  _fmpz_vec_scalar_mul_si :: Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

-- | /_fmpz_vec_scalar_mul_ui/ /vec1/ /vec2/ /len2/ /c/ 
-- 
-- Sets @(vec1, len2)@ to @(vec2, len2)@ multiplied by \(c\), where \(c\)
-- is an @ulong@.
foreign import ccall "fmpz_vec.h _fmpz_vec_scalar_mul_ui"
  _fmpz_vec_scalar_mul_ui :: Ptr CFmpz -> Ptr CFmpz -> CLong -> CULong -> IO ()

-- | /_fmpz_vec_scalar_mul_2exp/ /vec1/ /vec2/ /len2/ /exp/ 
-- 
-- Sets @(vec1, len2)@ to @(vec2, len2)@ multiplied by @2^exp@.
foreign import ccall "fmpz_vec.h _fmpz_vec_scalar_mul_2exp"
  _fmpz_vec_scalar_mul_2exp :: Ptr CFmpz -> Ptr CFmpz -> CLong -> CULong -> IO ()

-- | /_fmpz_vec_scalar_divexact_fmpz/ /vec1/ /vec2/ /len2/ /x/ 
-- 
-- Sets @(vec1, len2)@ to @(vec2, len2)@ divided by \(x\), where the
-- division is assumed to be exact for every entry in @vec2@.
foreign import ccall "fmpz_vec.h _fmpz_vec_scalar_divexact_fmpz"
  _fmpz_vec_scalar_divexact_fmpz :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /_fmpz_vec_scalar_divexact_si/ /vec1/ /vec2/ /len2/ /c/ 
-- 
-- Sets @(vec1, len2)@ to @(vec2, len2)@ divided by \(x\), where the
-- division is assumed to be exact for every entry in @vec2@.
foreign import ccall "fmpz_vec.h _fmpz_vec_scalar_divexact_si"
  _fmpz_vec_scalar_divexact_si :: Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

-- | /_fmpz_vec_scalar_divexact_ui/ /vec1/ /vec2/ /len2/ /c/ 
-- 
-- Sets @(vec1, len2)@ to @(vec2, len2)@ divided by \(x\), where the
-- division is assumed to be exact for every entry in @vec2@.
foreign import ccall "fmpz_vec.h _fmpz_vec_scalar_divexact_ui"
  _fmpz_vec_scalar_divexact_ui :: Ptr CFmpz -> Ptr CFmpz -> CULong -> CULong -> IO ()

-- | /_fmpz_vec_scalar_fdiv_q_fmpz/ /vec1/ /vec2/ /len2/ /c/ 
-- 
-- Sets @(vec1, len2)@ to @(vec2, len2)@ divided by \(c\), rounding down
-- towards minus infinity whenever the division is not exact.
foreign import ccall "fmpz_vec.h _fmpz_vec_scalar_fdiv_q_fmpz"
  _fmpz_vec_scalar_fdiv_q_fmpz :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /_fmpz_vec_scalar_fdiv_q_si/ /vec1/ /vec2/ /len2/ /c/ 
-- 
-- Sets @(vec1, len2)@ to @(vec2, len2)@ divided by \(c\), rounding down
-- towards minus infinity whenever the division is not exact.
foreign import ccall "fmpz_vec.h _fmpz_vec_scalar_fdiv_q_si"
  _fmpz_vec_scalar_fdiv_q_si :: Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

-- | /_fmpz_vec_scalar_fdiv_q_ui/ /vec1/ /vec2/ /len2/ /c/ 
-- 
-- Sets @(vec1, len2)@ to @(vec2, len2)@ divided by \(c\), rounding down
-- towards minus infinity whenever the division is not exact.
foreign import ccall "fmpz_vec.h _fmpz_vec_scalar_fdiv_q_ui"
  _fmpz_vec_scalar_fdiv_q_ui :: Ptr CFmpz -> Ptr CFmpz -> CLong -> CULong -> IO ()

-- | /_fmpz_vec_scalar_fdiv_q_2exp/ /vec1/ /vec2/ /len2/ /exp/ 
-- 
-- Sets @(vec1, len2)@ to @(vec2, len2)@ divided by @2^exp@, rounding down
-- towards minus infinity whenever the division is not exact.
foreign import ccall "fmpz_vec.h _fmpz_vec_scalar_fdiv_q_2exp"
  _fmpz_vec_scalar_fdiv_q_2exp :: Ptr CFmpz -> Ptr CFmpz -> CLong -> CULong -> IO ()

-- | /_fmpz_vec_scalar_fdiv_r_2exp/ /vec1/ /vec2/ /len2/ /exp/ 
-- 
-- Sets @(vec1, len2)@ to the remainder of @(vec2, len2)@ divided by
-- @2^exp@, rounding down the quotient towards minus infinity whenever the
-- division is not exact.
foreign import ccall "fmpz_vec.h _fmpz_vec_scalar_fdiv_r_2exp"
  _fmpz_vec_scalar_fdiv_r_2exp :: Ptr CFmpz -> Ptr CFmpz -> CLong -> CULong -> IO ()

-- | /_fmpz_vec_scalar_tdiv_q_fmpz/ /vec1/ /vec2/ /len2/ /c/ 
-- 
-- Sets @(vec1, len2)@ to @(vec2, len2)@ divided by \(c\), rounding towards
-- zero whenever the division is not exact.
foreign import ccall "fmpz_vec.h _fmpz_vec_scalar_tdiv_q_fmpz"
  _fmpz_vec_scalar_tdiv_q_fmpz :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /_fmpz_vec_scalar_tdiv_q_si/ /vec1/ /vec2/ /len2/ /c/ 
-- 
-- Sets @(vec1, len2)@ to @(vec2, len2)@ divided by \(c\), rounding towards
-- zero whenever the division is not exact.
foreign import ccall "fmpz_vec.h _fmpz_vec_scalar_tdiv_q_si"
  _fmpz_vec_scalar_tdiv_q_si :: Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

-- | /_fmpz_vec_scalar_tdiv_q_ui/ /vec1/ /vec2/ /len2/ /c/ 
-- 
-- Sets @(vec1, len2)@ to @(vec2, len2)@ divided by \(c\), rounding towards
-- zero whenever the division is not exact.
foreign import ccall "fmpz_vec.h _fmpz_vec_scalar_tdiv_q_ui"
  _fmpz_vec_scalar_tdiv_q_ui :: Ptr CFmpz -> Ptr CFmpz -> CLong -> CULong -> IO ()

-- | /_fmpz_vec_scalar_tdiv_q_2exp/ /vec1/ /vec2/ /len2/ /exp/ 
-- 
-- Sets @(vec1, len2)@ to @(vec2, len2)@ divided by @2^exp@, rounding down
-- towards zero whenever the division is not exact.
foreign import ccall "fmpz_vec.h _fmpz_vec_scalar_tdiv_q_2exp"
  _fmpz_vec_scalar_tdiv_q_2exp :: Ptr CFmpz -> Ptr CFmpz -> CLong -> CULong -> IO ()

foreign import ccall "fmpz_vec.h _fmpz_vec_scalar_addmul_si"
  _fmpz_vec_scalar_addmul_si :: Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

foreign import ccall "fmpz_vec.h _fmpz_vec_scalar_addmul_ui"
  _fmpz_vec_scalar_addmul_ui :: Ptr CFmpz -> Ptr CFmpz -> CLong -> CULong -> IO ()

-- | /_fmpz_vec_scalar_addmul_fmpz/ /vec1/ /vec2/ /len2/ /c/ 
-- 
-- Adds @(vec2, len2)@ times \(c\) to @(vec1, len2)@.
foreign import ccall "fmpz_vec.h _fmpz_vec_scalar_addmul_fmpz"
  _fmpz_vec_scalar_addmul_fmpz :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /_fmpz_vec_scalar_addmul_si_2exp/ /vec1/ /vec2/ /len2/ /c/ /exp/ 
-- 
-- Adds @(vec2, len2)@ times @c * 2^exp@ to @(vec1, len2)@, where \(c\) is
-- a @slong@.
foreign import ccall "fmpz_vec.h _fmpz_vec_scalar_addmul_si_2exp"
  _fmpz_vec_scalar_addmul_si_2exp :: Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> CULong -> IO ()

-- | /_fmpz_vec_scalar_submul_fmpz/ /vec1/ /vec2/ /len2/ /x/ 
-- 
-- Subtracts @(vec2, len2)@ times \(c\) from @(vec1, len2)@, where \(c\) is
-- a @fmpz_t@.
foreign import ccall "fmpz_vec.h _fmpz_vec_scalar_submul_fmpz"
  _fmpz_vec_scalar_submul_fmpz :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /_fmpz_vec_scalar_submul_si/ /vec1/ /vec2/ /len2/ /c/ 
-- 
-- Subtracts @(vec2, len2)@ times \(c\) from @(vec1, len2)@, where \(c\) is
-- a @slong@.
foreign import ccall "fmpz_vec.h _fmpz_vec_scalar_submul_si"
  _fmpz_vec_scalar_submul_si :: Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

-- | /_fmpz_vec_scalar_submul_si_2exp/ /vec1/ /vec2/ /len2/ /c/ /e/ 
-- 
-- Subtracts @(vec2, len2)@ times \(c \times 2^e\) from @(vec1, len2)@,
-- where \(c\) is a @slong@.
foreign import ccall "fmpz_vec.h _fmpz_vec_scalar_submul_si_2exp"
  _fmpz_vec_scalar_submul_si_2exp :: Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> CULong -> IO ()

-- Sums and products -----------------------------------------------------------

-- | /_fmpz_vec_sum/ /res/ /vec/ /len/ 
-- 
-- Sets @res@ to the sum of the entries in @(vec, len)@. Aliasing of @res@
-- with the entries in @vec@ is not permitted.
foreign import ccall "fmpz_vec.h _fmpz_vec_sum"
  _fmpz_vec_sum :: Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- | /_fmpz_vec_prod/ /res/ /vec/ /len/ 
-- 
-- Sets @res@ to the product of the entries in @(vec, len)@. Aliasing of
-- @res@ with the entries in @vec@ is not permitted. Uses binary splitting.
foreign import ccall "fmpz_vec.h _fmpz_vec_prod"
  _fmpz_vec_prod :: Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- Reduction mod \(p\) ---------------------------------------------------------

-- | /_fmpz_vec_scalar_mod_fmpz/ /res/ /vec/ /len/ /p/ 
-- 
-- Reduces all entries in @(vec, len)@ modulo \(p > 0\).
foreign import ccall "fmpz_vec.h _fmpz_vec_scalar_mod_fmpz"
  _fmpz_vec_scalar_mod_fmpz :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /_fmpz_vec_scalar_smod_fmpz/ /res/ /vec/ /len/ /p/ 
-- 
-- Reduces all entries in @(vec, len)@ modulo \(p > 0\), choosing the
-- unique representative in \((-p/2, p/2]\).
foreign import ccall "fmpz_vec.h _fmpz_vec_scalar_smod_fmpz"
  _fmpz_vec_scalar_smod_fmpz :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- Gaussian content ------------------------------------------------------------

-- | /_fmpz_vec_content/ /res/ /vec/ /len/ 
-- 
-- Sets @res@ to the non-negative content of the entries in @vec@. The
-- content of a zero vector, including the case when the length is zero, is
-- defined to be zero.
foreign import ccall "fmpz_vec.h _fmpz_vec_content"
  _fmpz_vec_content :: Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- | /_fmpz_vec_content_chained/ /res/ /vec/ /len/ /input/ 
-- 
-- Sets @res@ to the non-negative content of @input@ and the entries in
-- @vec@. This is useful for calculating the common content of several
-- vectors.
foreign import ccall "fmpz_vec.h _fmpz_vec_content_chained"
  _fmpz_vec_content_chained :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> IO ()

-- | /_fmpz_vec_lcm/ /res/ /vec/ /len/ 
-- 
-- Sets @res@ to the nonnegative least common multiple of the entries in
-- @vec@. The least common multiple is zero if any entry in the vector is
-- zero. The least common multiple of a length zero vector is defined to be
-- one.
foreign import ccall "fmpz_vec.h _fmpz_vec_lcm"
  _fmpz_vec_lcm :: Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- Dot product -----------------------------------------------------------------

-- | /_fmpz_vec_dot/ /res/ /vec1/ /vec2/ /len2/ 
-- 
-- Sets @res@ to the dot product of @(vec1, len2)@ and @(vec2, len2)@.
foreign import ccall "fmpz_vec.h _fmpz_vec_dot"
  _fmpz_vec_dot :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- | /_fmpz_vec_dot_ptr/ /res/ /vec1/ /vec2/ /offset/ /len/ 
-- 
-- Sets @res@ to the dot product of @len@ values at @vec1@ and the @len@
-- values @vec2[i] + offset@ for @0 \\leq i \< len@.
foreign import ccall "fmpz_vec.h _fmpz_vec_dot_ptr"
  _fmpz_vec_dot_ptr :: Ptr CFmpz -> Ptr CFmpz -> Ptr (Ptr CFmpz) -> CLong -> CLong -> IO ()

