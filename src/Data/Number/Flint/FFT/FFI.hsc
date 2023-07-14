{-|
module      :  Data.Number.Flint.FFT.FFI
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de
-}
module Data.Number.Flint.FFT.FFI (
  -- * Schoenhage-Strassen FFT
  -- * Split\/combine FFT coefficients
    fft_split_limbs
  , fft_split_bits
  , fft_combine_limbs
  , fft_combine_bits
  -- * Test helper functions
  , fermat_to_mpz
  -- * Arithmetic modulo a generalised Fermat number
  , mpn_negmod_2expp1
  , mpn_addmod_2expp1_1
  , mpn_normmod_2expp1
  , mpn_mul_2expmod_2expp1
  , mpn_div_2expmod_2expp1
  -- * Generic butterflies
  , fft_adjust
  , fft_adjust_sqrt2
  , butterfly_lshB
  , butterfly_rshB
  -- * Radix 2 transforms
  , fft_butterfly
  , ifft_butterfly
  , fft_radix2
  , fft_truncate
  , fft_truncate1
  , ifft_radix2
  , ifft_truncate
  , ifft_truncate1
  , fft_butterfly_sqrt2
  , ifft_butterfly_sqrt2
  , fft_truncate_sqrt2
  , ifft_truncate_sqrt2
  -- * Matrix Fourier Transforms
  , fft_butterfly_twiddle
  , ifft_butterfly_twiddle
  , fft_radix2_twiddle
  , ifft_radix2_twiddle
  , fft_truncate1_twiddle
  , ifft_truncate1_twiddle
  , fft_mfa_truncate_sqrt2
  , ifft_mfa_truncate_sqrt2
  , fft_mfa_truncate_sqrt2_outer
  , fft_mfa_truncate_sqrt2_inner
  , ifft_mfa_truncate_sqrt2_outer
  -- * Negacyclic multiplication
  , fft_negacyclic
  , ifft_negacyclic
  , fft_naive_convolution_1
  , _fft_mulmod_2expp1
  , fft_adjust_limbs
  , fft_mulmod_2expp1
  -- * Integer multiplication
  , mul_truncate_sqrt2
  , mul_mfa_truncate_sqrt2
  , flint_mpn_mul_fft_main
  -- * Convolution
  , fft_convolution
  -- * FFT Precaching
  , fft_precache
  , fft_convolution_precache
) where

-- Schoenhage-Strassen FFT -----------------------------------------------------

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr )
import Foreign.Storable
import Foreign.Marshal ( free )

import Data.Number.Flint.Flint

#include <flint/flint.h>
#include <flint/fft.h>

-- Split\/combine FFT coefficients ---------------------------------------------

-- | /fft_split_limbs/ /poly/ /limbs/ /total_limbs/ /coeff_limbs/ /output_limbs/ 
--
-- Split an integer @(limbs, total_limbs)@ into coefficients of length
-- @coeff_limbs@ limbs and store as the coefficients of @poly@ which are
-- assumed to have space for @output_limbs + 1@ limbs per coefficient. The
-- coefficients of the polynomial do not need to be zeroed before calling
-- this function, however the number of coefficients written is returned by
-- the function and any coefficients beyond this point are not touched.
foreign import ccall "fft.h fft_split_limbs"
  fft_split_limbs :: Ptr (Ptr CMpLimb) -> Ptr CMp -> CMpSize -> CMpSize -> CMpSize -> IO CMpSize

-- | /fft_split_bits/ /poly/ /limbs/ /total_limbs/ /bits/ /output_limbs/ 
--
-- Split an integer @(limbs, total_limbs)@ into coefficients of the given
-- number of @bits@ and store as the coefficients of @poly@ which are
-- assumed to have space for @output_limbs + 1@ limbs per coefficient. The
-- coefficients of the polynomial do not need to be zeroed before calling
-- this function, however the number of coefficients written is returned by
-- the function and any coefficients beyond this point are not touched.
foreign import ccall "fft.h fft_split_bits"
  fft_split_bits :: Ptr (Ptr CMpLimb) -> Ptr CMp -> CMpSize -> CFBitCnt -> CMpSize -> IO CMpSize

-- | /fft_combine_limbs/ /res/ /poly/ /length/ /coeff_limbs/ /output_limbs/ /total_limbs/ 
--
-- Evaluate the polynomial @poly@ of the given @length@ at @B^coeff_limbs@,
-- where @B = 2^FLINT_BITS@, and add the result to the integer
-- @(res, total_limbs)@ throwing away any bits that exceed the given number
-- of limbs. The polynomial coefficients are assumed to have at least
-- @output_limbs@ limbs each, however any additional limbs are ignored.
-- 
-- If the integer is initially zero the result will just be the evaluation
-- of the polynomial.
foreign import ccall "fft.h fft_combine_limbs"
  fft_combine_limbs :: Ptr CMpLimb -> Ptr (Ptr CMpLimb) -> CLong -> CMpSize -> CMpSize -> CMpSize -> IO ()

-- | /fft_combine_bits/ /res/ /poly/ /length/ /bits/ /output_limbs/ /total_limbs/ 
--
-- Evaluate the polynomial @poly@ of the given @length@ at @2^bits@ and add
-- the result to the integer @(res, total_limbs)@ throwing away any bits
-- that exceed the given number of limbs. The polynomial coefficients are
-- assumed to have at least @output_limbs@ limbs each, however any
-- additional limbs are ignored. If the integer is initially zero the
-- result will just be the evaluation of the polynomial.
foreign import ccall "fft.h fft_combine_bits"
  fft_combine_bits :: Ptr CMpLimb -> Ptr (Ptr CMpLimb) -> CLong -> CFBitCnt -> CMpSize -> CMpSize -> IO ()

-- Test helper functions -------------------------------------------------------

-- | /fermat_to_mpz/ /m/ /i/ /limbs/ 
--
-- Convert the Fermat number @(i, limbs)@ modulo @B^limbs + 1@ to an
-- @mpz_t m@. Assumes @m@ has been initialised. This function is used only
-- in test code.
foreign import ccall "fft.h fermat_to_mpz"
  fermat_to_mpz :: Ptr CMpz -> Ptr CMpLimb -> CMpSize -> IO ()

-- Arithmetic modulo a generalised Fermat number -------------------------------

-- | /mpn_negmod_2expp1/ /z/ /a/ /limbs/ 
--
-- Set @z@ to the negation of the Fermat number \(a\) modulo @B^limbs + 1@.
-- The input @a@ is expected to be fully reduced, and the output is fully
-- reduced. Aliasing is permitted.
foreign import ccall "fft.h mpn_negmod_2expp1"
  mpn_negmod_2expp1 :: Ptr CMpLimb -> Ptr CMpLimb -> CMpSize -> IO ()

-- | /mpn_addmod_2expp1_1/ /r/ /limbs/ /c/ 
--
-- Adds the signed limb @c@ to the generalised Fermat number @r@ modulo
-- @B^limbs + 1@. The compiler should be able to inline this for the case
-- that there is no overflow from the first limb.
foreign import ccall "fft.h mpn_addmod_2expp1_1"
  mpn_addmod_2expp1_1 :: Ptr CMpLimb -> CMpSize -> Ptr CMpSLimb-> IO ()

-- | /mpn_normmod_2expp1/ /t/ /limbs/ 
--
-- Given @t@ a signed integer of @limbs + 1@ limbs in two\'s complement
-- format, reduce @t@ to the corresponding value modulo the generalised
-- Fermat number @B^limbs + 1@, where @B = 2^FLINT_BITS@.
foreign import ccall "fft.h mpn_normmod_2expp1"
  mpn_normmod_2expp1 :: Ptr CMpLimb -> CMpSize -> IO ()

-- | /mpn_mul_2expmod_2expp1/ /t/ /i1/ /limbs/ /d/ 
--
-- Given @i1@ a signed integer of @limbs + 1@ limbs in two\'s complement
-- format reduced modulo @B^limbs + 1@ up to some overflow, compute
-- @t = i1*2^d@ modulo \(p\). The result will not necessarily be fully
-- reduced. The number of bits @d@ must be nonnegative and less than
-- @FLINT_BITS@. Aliasing is permitted.
foreign import ccall "fft.h mpn_mul_2expmod_2expp1"
  mpn_mul_2expmod_2expp1 :: Ptr CMpLimb -> Ptr CMpLimb -> CMpSize -> CFBitCnt -> IO ()

-- | /mpn_div_2expmod_2expp1/ /t/ /i1/ /limbs/ /d/ 
--
-- Given @i1@ a signed integer of @limbs + 1@ limbs in two\'s complement
-- format reduced modulo @B^limbs + 1@ up to some overflow, compute
-- @t = i1\/2^d@ modulo \(p\). The result will not necessarily be fully
-- reduced. The number of bits @d@ must be nonnegative and less than
-- @FLINT_BITS@. Aliasing is permitted.
foreign import ccall "fft.h mpn_div_2expmod_2expp1"
  mpn_div_2expmod_2expp1 :: Ptr CMpLimb -> Ptr CMpLimb -> CMpSize -> CFBitCnt -> IO ()

-- Generic butterflies ---------------------------------------------------------

-- | /fft_adjust/ /r/ /i1/ /i/ /limbs/ /w/ 
--
-- Set @r@ to @i1@ times \(z^i\) modulo @B^limbs + 1@ where \(z\)
-- corresponds to multiplication by \(2^w\). This can be thought of as part
-- of a butterfly operation. We require \(0 \leq i < n\) where \(nw =\)
-- @limbs*FLINT_BITS@. Aliasing is not supported.
foreign import ccall "fft.h fft_adjust"
  fft_adjust :: Ptr CMpLimb -> Ptr CMpLimb -> CMpSize -> CMpSize -> CFBitCnt -> IO ()

-- | /fft_adjust_sqrt2/ /r/ /i1/ /i/ /limbs/ /w/ /temp/ 
--
-- Set @r@ to @i1@ times \(z^i\) modulo @B^limbs + 1@ where \(z\)
-- corresponds to multiplication by \(\sqrt{2}^w\). This can be thought of
-- as part of a butterfly operation. We require \(0 \leq i < 2\cdot n\) and
-- odd where \(nw =\) @limbs*FLINT_BITS@.
foreign import ccall "fft.h fft_adjust_sqrt2"
  fft_adjust_sqrt2 :: Ptr CMpLimb -> Ptr CMpLimb -> CMpSize -> CMpSize -> CFBitCnt -> Ptr CMpLimb -> IO ()

-- | /butterfly_lshB/ /t/ /u/ /i1/ /i2/ /limbs/ /x/ /y/ 
--
-- We are given two integers @i1@ and @i2@ modulo @B^limbs + 1@ which are
-- not necessarily normalised. We compute @t = (i1 + i2)*B^x@ and
-- @u = (i1 - i2)*B^y@ modulo \(p\). Aliasing between inputs and outputs is
-- not permitted. We require @x@ and @y@ to be less than @limbs@ and
-- nonnegative.
foreign import ccall "fft.h butterfly_lshB"
  butterfly_lshB :: Ptr CMpLimb -> Ptr CMpLimb -> Ptr CMpLimb -> Ptr CMpLimb -> CMpSize -> CMpSize -> CMpSize -> IO ()

-- | /butterfly_rshB/ /t/ /u/ /i1/ /i2/ /limbs/ /x/ /y/ 
--
-- We are given two integers @i1@ and @i2@ modulo @B^limbs + 1@ which are
-- not necessarily normalised. We compute @t = (i1 + i2)\/B^x@ and
-- @u = (i1 - i2)\/B^y@ modulo \(p\). Aliasing between inputs and outputs
-- is not permitted. We require @x@ and @y@ to be less than @limbs@ and
-- nonnegative.
foreign import ccall "fft.h butterfly_rshB"
  butterfly_rshB :: Ptr CMpLimb -> Ptr CMpLimb -> Ptr CMpLimb -> Ptr CMpLimb -> CMpSize -> CMpSize -> CMpSize -> IO ()

-- Radix 2 transforms ----------------------------------------------------------

-- | /fft_butterfly/ /s/ /t/ /i1/ /i2/ /i/ /limbs/ /w/ 
--
-- Set @s = i1 + i2@, @t = z1^i*(i1 - i2)@ modulo @B^limbs + 1@ where
-- @z1 = exp(Pi*I\/n)@ corresponds to multiplication by \(2^w\). Requires
-- \(0 \leq i < n\) where \(nw =\) @limbs*FLINT_BITS@.
foreign import ccall "fft.h fft_butterfly"
  fft_butterfly :: Ptr CMpLimb -> Ptr CMpLimb -> Ptr CMpLimb -> Ptr CMpLimb -> CMpSize -> CMpSize -> CFBitCnt -> IO ()

-- | /ifft_butterfly/ /s/ /t/ /i1/ /i2/ /i/ /limbs/ /w/ 
--
-- Set @s = i1 + z1^i*i2@, @t = i1 -  z1^i*i2@ modulo @B^limbs + 1@ where
-- @z1 = exp(-Pi*I\/n)@ corresponds to division by \(2^w\). Requires
-- \(0 \leq i < 2n\) where \(nw =\) @limbs*FLINT_BITS@.
foreign import ccall "fft.h ifft_butterfly"
  ifft_butterfly :: Ptr CMpLimb -> Ptr CMpLimb -> Ptr CMpLimb -> Ptr CMpLimb -> CMpSize -> CMpSize -> CFBitCnt -> IO ()

-- | /fft_radix2/ /ii/ /n/ /w/ /t1/ /t2/ 
--
-- The radix 2 DIF FFT works as follows:
-- 
-- Input: @[i0, i1, ..., i(m-1)]@, for \(m = 2n\) a power of \(2\).
-- 
-- Output: @[r0, r1, ..., r(m-1)]@ @= FFT[i0, i1, ..., i(m-1)]@.
-- 
-- Algorithm:
-- 
-- \(\bullet\) Recursively compute @[r0, r2, r4, ...., r(m-2)]@
--     @= FFT[i0+i(m\/2), i1+i(m\/2+1), ..., i(m\/2-1)+i(m-1)]@
-- \(\bullet\) Let @[t0, t1, ..., t(m\/2-1)]@
--     @= [i0-i(m\/2), i1-i(m\/2+1), ..., i(m\/2-1)-i(m-1)]@
-- \(\bullet\) Let @[u0, u1, ..., u(m\/2-1)]@
--     @= [z1^0*t0, z1^1*t1, ..., z1^(m\/2-1)*t(m\/2-1)]@
--     where @z1 = exp(2*Pi*I\/m)@ corresponds to multiplication by
-- \(2^w\).
-- \(\bullet\) Recursively compute @[r1, r3, ..., r(m-1)]@
--     @= FFT[u0, u1, ..., u(m\/2-1)]@
-- 
-- The parameters are as follows:
-- 
-- \(\bullet\) @2*n@ is the length of the input and output arrays
-- 
-- [\(\bullet\) \(w\) is such that \(2^w\) is an \(2n\)-th root of unity in the ring \(\mathbf{Z}/p\mathbf{Z}\) that we are working in, i.e. \(p = 2^{wn} + 1\) (here \(n\) is divisible by]
--     @GMP_LIMB_BITS@)
-- 
-- [\(\bullet\) @ii@ is the array of inputs (each input is an]
--     array of limbs of length @wn\/GMP_LIMB_BITS + 1@ (the extra limbs
--     being a \"carry limb\"). Outputs are written in-place.
-- 
-- We require \(nw\) to be at least 64 and the two temporary space pointers
-- to point to blocks of size @n*w + FLINT_BITS@ bits.
foreign import ccall "fft.h fft_radix2"
  fft_radix2 :: Ptr (Ptr CMpLimb) -> CMpSize -> CFBitCnt -> Ptr (Ptr CMpLimb) -> Ptr (Ptr CMpLimb) -> IO ()

-- | /fft_truncate/ /ii/ /n/ /w/ /t1/ /t2/ /trunc/ 
--
-- As for @fft_radix2@ except that only the first @trunc@ coefficients of
-- the output are computed and the input is regarded as having (implied)
-- zero coefficients from coefficient @trunc@ onwards. The coefficients
-- must exist as the algorithm needs to use this extra space, but their
-- value is irrelevant. The value of @trunc@ must be divisible by 2.
foreign import ccall "fft.h fft_truncate"
  fft_truncate :: Ptr (Ptr CMpLimb) -> CMpSize -> CFBitCnt -> Ptr (Ptr CMpLimb) -> Ptr (Ptr CMpLimb) -> CMpSize -> IO ()

-- | /fft_truncate1/ /ii/ /n/ /w/ /t1/ /t2/ /trunc/ 
--
-- As for @fft_radix2@ except that only the first @trunc@ coefficients of
-- the output are computed. The transform still needs all \(2n\) input
-- coefficients to be specified.
foreign import ccall "fft.h fft_truncate1"
  fft_truncate1 :: Ptr (Ptr CMpLimb) -> CMpSize -> CFBitCnt -> Ptr (Ptr CMpLimb) -> Ptr (Ptr CMpLimb) -> CMpSize -> IO ()

-- | /ifft_radix2/ /ii/ /n/ /w/ /t1/ /t2/ 
--
-- The radix 2 DIF IFFT works as follows:
-- 
-- Input: @[i0, i1, ..., i(m-1)]@, for \(m = 2n\) a power of \(2\).
-- 
-- [Output: @[r0, r1, ..., r(m-1)]@]
--     @= IFFT[i0, i1, ..., i(m-1)]@.
-- 
-- Algorithm:
-- 
-- [\(\bullet\) Recursively compute @[s0, s1, ...., s(m\/2-1)]@]
--     @= IFFT[i0, i2, ..., i(m-2)]@
-- 
-- [\(\bullet\) Recursively compute @[t(m\/2), t(m\/2+1), ..., t(m-1)]@]
--     @= IFFT[i1, i3, ..., i(m-1)]@
-- 
-- [\(\bullet\) Let @[r0, r1, ..., r(m\/2-1)]@]
--     @= [s0+z1^0*t0, s1+z1^1*t1, ..., s(m\/2-1)+z1^(m\/2-1)*t(m\/2-1)]@
--     where @z1 = exp(-2*Pi*I\/m)@ corresponds to division by \(2^w\).
-- 
-- [\(\bullet\) Let @[r(m\/2), r(m\/2+1), ..., r(m-1)]@]
--     @= [s0-z1^0*t0, s1-z1^1*t1, ..., s(m\/2-1)-z1^(m\/2-1)*t(m\/2-1)]@
-- 
-- The parameters are as follows:
-- 
-- [\(\bullet\) @2*n@ is the length of the input and output]
--     arrays
-- 
-- [\(\bullet\) \(w\) is such that \(2^w\) is an \(2n\)-th root of unity in the ring \(\mathbf{Z}/p\mathbf{Z}\) that we are working in, i.e. \(p = 2^{wn} + 1\) (here \(n\) is divisible by]
--     @GMP_LIMB_BITS@)
-- 
-- \(\bullet\) @ii@ is the array of inputs (each input is an array of limbs
-- of length @wn\/GMP_LIMB_BITS + 1@ (the extra limbs being a \"carry
-- limb\"). Outputs are written in-place.
-- 
-- We require \(nw\) to be at least 64 and the two temporary space pointers
-- to point to blocks of size @n*w + FLINT_BITS@ bits.
foreign import ccall "fft.h ifft_radix2"
  ifft_radix2 :: Ptr (Ptr CMpLimb) -> CMpSize -> CFBitCnt -> Ptr (Ptr CMpLimb) -> Ptr (Ptr CMpLimb) -> IO ()

-- | /ifft_truncate/ /ii/ /n/ /w/ /t1/ /t2/ /trunc/ 
--
-- As for @ifft_radix2@ except that the output is assumed to have zeros
-- from coefficient trunc onwards and only the first trunc coefficients of
-- the input are specified. The remaining coefficients need to exist as the
-- extra space is needed, but their value is irrelevant. The value of
-- @trunc@ must be divisible by 2.
-- 
-- Although the implementation does not require it, we assume for
-- simplicity that @trunc@ is greater than \(n\). The algorithm begins by
-- computing the inverse transform of the first \(n\) coefficients of the
-- input array. The unspecified coefficients of the second half of the
-- array are then written: coefficient @trunc + i@ is computed as a twist
-- of coefficient @i@ by a root of unity. The values of these coefficients
-- are then equal to what they would have been if the inverse transform of
-- the right hand side of the input array had been computed with full data
-- from the start. The function @ifft_truncate1@ is then called on the
-- entire right half of the input array with this auxiliary data filled in.
-- Finally a single layer of the IFFT is completed on all the coefficients
-- up to @trunc@ being careful to note that this involves doubling the
-- coefficients from @trunc - n@ up to @n@.
foreign import ccall "fft.h ifft_truncate"
  ifft_truncate :: Ptr (Ptr CMpLimb) -> CMpSize -> CFBitCnt -> Ptr (Ptr CMpLimb) -> Ptr (Ptr CMpLimb) -> CMpSize -> IO ()

-- | /ifft_truncate1/ /ii/ /n/ /w/ /t1/ /t2/ /trunc/ 
--
-- Computes the first @trunc@ coefficients of the radix 2 inverse transform
-- assuming the first @trunc@ coefficients are given and that the remaining
-- coefficients have been set to the value they would have if an inverse
-- transform had already been applied with full data.
-- 
-- The algorithm is the same as for @ifft_truncate@ except that the
-- coefficients from @trunc@ onwards after the inverse transform are not
-- inferred to be zero but the supplied values.
foreign import ccall "fft.h ifft_truncate1"
  ifft_truncate1 :: Ptr (Ptr CMpLimb) -> CMpSize -> CFBitCnt -> Ptr (Ptr CMpLimb) -> Ptr (Ptr CMpLimb) -> CMpSize -> IO ()

-- | /fft_butterfly_sqrt2/ /s/ /t/ /i1/ /i2/ /i/ /limbs/ /w/ /temp/ 
--
-- Let \(w = 2k + 1\), \(i = 2j + 1\). Set @s = i1 + i2@,
-- @t = z1^i*(i1 - i2)@ modulo @B^limbs + 1@ where @z1^2 = exp(Pi*I\/n)@
-- corresponds to multiplication by \(2^w\). Requires \(0 \leq i < 2n\)
-- where \(nw =\) @limbs*FLINT_BITS@.
-- 
-- Here @z1@ corresponds to multiplication by \(2^k\) then multiplication
-- by @(2^(3nw\/4) - 2^(nw\/4))@. We see @z1^i@ corresponds to
-- multiplication by @(2^(3nw\/4) - 2^(nw\/4))*2^(j+ik)@.
-- 
-- We first multiply by @2^(j + ik + wn\/4)@ then multiply by an additional
-- @2^(nw\/2)@ and subtract.
foreign import ccall "fft.h fft_butterfly_sqrt2"
  fft_butterfly_sqrt2 :: Ptr CMpLimb -> Ptr CMpLimb -> Ptr CMpLimb -> Ptr CMpLimb -> CMpSize -> CMpSize -> CFBitCnt -> Ptr CMpLimb -> IO ()

-- | /ifft_butterfly_sqrt2/ /s/ /t/ /i1/ /i2/ /i/ /limbs/ /w/ /temp/ 
--
-- Let \(w = 2k + 1\), \(i = 2j + 1\). Set @s = i1 + z1^i*i2@,
-- @t = i1 - z1^i*i2@ modulo @B^limbs + 1@ where @z1^2 = exp(-Pi*I\/n)@
-- corresponds to division by \(2^w\). Requires \(0 \leq i < 2n\) where
-- \(nw =\) @limbs*FLINT_BITS@.
-- 
-- Here @z1@ corresponds to division by \(2^k\) then division by
-- @(2^(3nw\/4) - 2^(nw\/4))@. We see @z1^i@ corresponds to division by
-- @(2^(3nw\/4) - 2^(nw\/4))*2^(j+ik)@ which is the same as division by
-- @2^(j+ik + 1)@ then multiplication by @(2^(3nw\/4) - 2^(nw\/4))@.
-- 
-- Of course, division by @2^(j+ik + 1)@ is the same as multiplication by
-- @2^(2*wn - j - ik - 1)@. The exponent is positive as
-- \(i \leq 2\cdot n\), \(j < n\), \(k < w/2\).
-- 
-- We first multiply by @2^(2*wn - j - ik - 1 + wn\/4)@ then multiply by an
-- additional @2^(nw\/2)@ and subtract.
foreign import ccall "fft.h ifft_butterfly_sqrt2"
  ifft_butterfly_sqrt2 :: Ptr CMpLimb -> Ptr CMpLimb -> Ptr CMpLimb -> Ptr CMpLimb -> CMpSize -> CMpSize -> CFBitCnt -> Ptr CMpLimb -> IO ()

-- | /fft_truncate_sqrt2/ /ii/ /n/ /w/ /t1/ /t2/ /temp/ /trunc/ 
--
-- As per @fft_truncate@ except that the transform is twice the usual
-- length, i.e. length \(4n\) rather than \(2n\). This is achieved by
-- making use of twiddles by powers of a square root of 2, not powers of 2
-- in the first layer of the transform.
-- 
-- We require \(nw\) to be at least 64 and the three temporary space
-- pointers to point to blocks of size @n*w + FLINT_BITS@ bits.
foreign import ccall "fft.h fft_truncate_sqrt2"
  fft_truncate_sqrt2 :: Ptr (Ptr CMpLimb) -> CMpSize -> CFBitCnt -> Ptr (Ptr CMpLimb) -> Ptr (Ptr CMpLimb) -> Ptr (Ptr CMpLimb) -> CMpSize -> IO ()

-- | /ifft_truncate_sqrt2/ /ii/ /n/ /w/ /t1/ /t2/ /temp/ /trunc/ 
--
-- As per @ifft_truncate@ except that the transform is twice the usual
-- length, i.e. length \(4n\) instead of \(2n\). This is achieved by making
-- use of twiddles by powers of a square root of 2, not powers of 2 in the
-- final layer of the transform.
-- 
-- We require \(nw\) to be at least 64 and the three temporary space
-- pointers to point to blocks of size @n*w + FLINT_BITS@ bits.
foreign import ccall "fft.h ifft_truncate_sqrt2"
  ifft_truncate_sqrt2 :: Ptr (Ptr CMpLimb) -> CMpSize -> CFBitCnt -> Ptr (Ptr CMpLimb) -> Ptr (Ptr CMpLimb) -> Ptr (Ptr CMpLimb) -> CMpSize -> IO ()

-- Matrix Fourier Transforms ---------------------------------------------------

-- | /fft_butterfly_twiddle/ /u/ /v/ /s/ /t/ /limbs/ /b1/ /b2/ 
--
-- Set @u = 2^b1*(s + t)@, @v = 2^b2*(s - t)@ modulo @B^limbs + 1@. This is
-- used to compute @u = 2^(ws*tw1)*(s + t)@, @v = 2^(w+ws*tw2)*(s - t)@ in
-- the matrix Fourier algorithm, i.e. effectively computing an ordinary
-- butterfly with additional twiddles by @z1^rc@ for row \(r\) and column
-- \(c\) of the matrix of coefficients. Aliasing is not allowed.
foreign import ccall "fft.h fft_butterfly_twiddle"
  fft_butterfly_twiddle :: Ptr CMpLimb -> Ptr CMpLimb -> Ptr CMpLimb -> Ptr CMpLimb -> CMpSize -> CFBitCnt -> CFBitCnt -> IO ()

-- | /ifft_butterfly_twiddle/ /u/ /v/ /s/ /t/ /limbs/ /b1/ /b2/ 
--
-- Set @u = s\/2^b1 + t\/2^b1)@, @v = s\/2^b1 - t\/2^b1@ modulo
-- @B^limbs + 1@. This is used to compute
-- @u = 2^(-ws*tw1)*s + 2^(-ws*tw2)*t)@,
-- @v = 2^(-ws*tw1)*s + 2^(-ws*tw2)*t)@ in the matrix Fourier algorithm,
-- i.e. effectively computing an ordinary butterfly with additional
-- twiddles by @z1^(-rc)@ for row \(r\) and column \(c\) of the matrix of
-- coefficients. Aliasing is not allowed.
foreign import ccall "fft.h ifft_butterfly_twiddle"
  ifft_butterfly_twiddle :: Ptr CMpLimb -> Ptr CMpLimb -> Ptr CMpLimb -> Ptr CMpLimb -> CMpSize -> CFBitCnt -> CFBitCnt -> IO ()

-- | /fft_radix2_twiddle/ /ii/ /is/ /n/ /w/ /t1/ /t2/ /ws/ /r/ /c/ /rs/ 
--
-- As for @fft_radix2@ except that the coefficients are spaced by @is@ in
-- the array @ii@ and an additional twist by @z^c*i@ is applied to each
-- coefficient where \(i\) starts at \(r\) and increases by @rs@ as one
-- moves from one coefficient to the next. Here @z@ corresponds to
-- multiplication by @2^ws@.
foreign import ccall "fft.h fft_radix2_twiddle"
  fft_radix2_twiddle :: Ptr (Ptr CMpLimb) -> CMpSize -> CMpSize -> CFBitCnt -> Ptr (Ptr CMpLimb) -> Ptr (Ptr CMpLimb) -> CMpSize -> CMpSize -> CMpSize -> CMpSize -> IO ()

-- | /ifft_radix2_twiddle/ /ii/ /is/ /n/ /w/ /t1/ /t2/ /ws/ /r/ /c/ /rs/ 
--
-- As for @ifft_radix2@ except that the coefficients are spaced by @is@ in
-- the array @ii@ and an additional twist by @z^(-c*i)@ is applied to each
-- coefficient where \(i\) starts at \(r\) and increases by @rs@ as one
-- moves from one coefficient to the next. Here @z@ corresponds to
-- multiplication by @2^ws@.
foreign import ccall "fft.h ifft_radix2_twiddle"
  ifft_radix2_twiddle :: Ptr (Ptr CMpLimb) -> CMpSize -> CMpSize -> CFBitCnt -> Ptr (Ptr CMpLimb) -> Ptr (Ptr CMpLimb) -> CMpSize -> CMpSize -> CMpSize -> CMpSize -> IO ()

-- | /fft_truncate1_twiddle/ /ii/ /is/ /n/ /w/ /t1/ /t2/ /ws/ /r/ /c/ /rs/ /trunc/ 
--
-- As per @fft_radix2_twiddle@ except that the transform is truncated as
-- per @fft_truncate1@.
foreign import ccall "fft.h fft_truncate1_twiddle"
  fft_truncate1_twiddle :: Ptr (Ptr CMpLimb) -> CMpSize -> CMpSize -> CFBitCnt -> Ptr (Ptr CMpLimb) -> Ptr (Ptr CMpLimb) -> CMpSize -> CMpSize -> CMpSize -> CMpSize -> CMpSize -> IO ()

-- | /ifft_truncate1_twiddle/ /ii/ /is/ /n/ /w/ /t1/ /t2/ /ws/ /r/ /c/ /rs/ /trunc/ 
--
-- As per @ifft_radix2_twiddle@ except that the transform is truncated as
-- per @ifft_truncate1@.
foreign import ccall "fft.h ifft_truncate1_twiddle"
  ifft_truncate1_twiddle :: Ptr (Ptr CMpLimb) -> CMpSize -> CMpSize -> CFBitCnt -> Ptr (Ptr CMpLimb) -> Ptr (Ptr CMpLimb) -> CMpSize -> CMpSize -> CMpSize -> CMpSize -> CMpSize -> IO ()

-- | /fft_mfa_truncate_sqrt2/ /ii/ /n/ /w/ /t1/ /t2/ /temp/ /n1/ /trunc/ 
--
-- This is as per the @fft_truncate_sqrt2@ function except that the matrix
-- Fourier algorithm is used for the left and right FFTs. The total
-- transform length is \(4n\) where @n = 2^depth@ so that the left and
-- right transforms are both length \(2n\). We require @trunc > 2*n@ and
-- that @trunc@ is divisible by @2*n1@ (explained below). The coefficients
-- are produced in an order different from @fft_truncate_sqrt2@.
-- 
-- The matrix Fourier algorithm, which is applied to each transform of
-- length \(2n\), works as follows. We set @n1@ to a power of 2 about the
-- square root of \(n\). The data is then thought of as a set of @n2@ rows
-- each with @n1@ columns (so that @n1*n2 = 2n@).
-- 
-- The length \(2n\) transform is then computed using a whole pile of short
-- transforms. These comprise @n1@ column transforms of length @n2@
-- followed by some twiddles by roots of unity (namely @z^rc@ where \(r\)
-- is the row and \(c\) the column within the data) followed by @n2@ row
-- transforms of length @n1@. Along the way the data needs to be rearranged
-- due to the fact that the short transforms output the data in binary
-- reversed order compared with what is needed.
-- 
-- The matrix Fourier algorithm provides better cache locality by
-- decomposing the long length \(2n\) transforms into many transforms of
-- about the square root of the original length.
-- 
-- For better cache locality the sqrt2 layer of the full length \(4n\)
-- transform is folded in with the column FFTs performed as part of the
-- first matrix Fourier algorithm on the left half of the data.
-- 
-- The second half of the data requires a truncated version of the matrix
-- Fourier algorithm. This is achieved by truncating to an exact multiple
-- of the row length so that the row transforms are full length. Moreover,
-- the column transforms will then be truncated transforms and their
-- truncated length needs to be a multiple of 2. This explains the
-- condition on @trunc@ given above.
-- 
-- To improve performance, the extra twiddles by roots of unity are
-- combined with the butterflies performed at the last layer of the column
-- transforms.
-- 
-- We require \(nw\) to be at least 64 and the three temporary space
-- pointers to point to blocks of size @n*w + FLINT_BITS@ bits.
foreign import ccall "fft.h fft_mfa_truncate_sqrt2"
  fft_mfa_truncate_sqrt2 :: Ptr (Ptr CMpLimb) -> CMpSize -> CFBitCnt -> Ptr (Ptr CMpLimb) -> Ptr (Ptr CMpLimb) -> Ptr (Ptr CMpLimb) -> CMpSize -> CMpSize -> IO ()

-- | /ifft_mfa_truncate_sqrt2/ /ii/ /n/ /w/ /t1/ /t2/ /temp/ /n1/ /trunc/ 
--
-- This is as per the @ifft_truncate_sqrt2@ function except that the matrix
-- Fourier algorithm is used for the left and right IFFTs. The total
-- transform length is \(4n\) where @n = 2^depth@ so that the left and
-- right transforms are both length \(2n\). We require @trunc > 2*n@ and
-- that @trunc@ is divisible by @2*n1@.
-- 
-- We set @n1@ to a power of 2 about the square root of \(n\).
-- 
-- As per the matrix fourier FFT the sqrt2 layer is folded into the final
-- column IFFTs for better cache locality and the extra twiddles that occur
-- in the matrix Fourier algorithm are combined with the butterflied
-- performed at the first layer of the final column transforms.
-- 
-- We require \(nw\) to be at least 64 and the three temporary space
-- pointers to point to blocks of size @n*w + FLINT_BITS@ bits.
foreign import ccall "fft.h ifft_mfa_truncate_sqrt2"
  ifft_mfa_truncate_sqrt2 :: Ptr (Ptr CMpLimb) -> CMpSize -> CFBitCnt -> Ptr (Ptr CMpLimb) -> Ptr (Ptr CMpLimb) -> Ptr (Ptr CMpLimb) -> CMpSize -> CMpSize -> IO ()

-- | /fft_mfa_truncate_sqrt2_outer/ /ii/ /n/ /w/ /t1/ /t2/ /temp/ /n1/ /trunc/ 
--
-- Just the outer layers of @fft_mfa_truncate_sqrt2@.
foreign import ccall "fft.h fft_mfa_truncate_sqrt2_outer"
  fft_mfa_truncate_sqrt2_outer :: Ptr (Ptr CMpLimb) -> CMpSize -> CFBitCnt -> Ptr (Ptr CMpLimb) -> Ptr (Ptr CMpLimb) -> Ptr (Ptr CMpLimb) -> CMpSize -> CMpSize -> IO ()

-- | /fft_mfa_truncate_sqrt2_inner/ /ii/ /jj/ /n/ /w/ /t1/ /t2/ /temp/ /n1/ /trunc/ /tt/ 
--
-- The inner layers of @fft_mfa_truncate_sqrt2@ and
-- @ifft_mfa_truncate_sqrt2@ combined with pointwise mults.
foreign import ccall "fft.h fft_mfa_truncate_sqrt2_inner"
  fft_mfa_truncate_sqrt2_inner :: Ptr (Ptr CMpLimb) -> Ptr (Ptr CMpLimb) -> CMpSize -> CFBitCnt -> Ptr (Ptr CMpLimb) -> Ptr (Ptr CMpLimb) -> Ptr (Ptr CMpLimb) -> CMpSize -> CMpSize -> Ptr CMpLimb -> IO ()

-- | /ifft_mfa_truncate_sqrt2_outer/ /ii/ /n/ /w/ /t1/ /t2/ /temp/ /n1/ /trunc/ 
--
-- The outer layers of @ifft_mfa_truncate_sqrt2@ combined with
-- normalisation.
foreign import ccall "fft.h ifft_mfa_truncate_sqrt2_outer"
  ifft_mfa_truncate_sqrt2_outer :: Ptr (Ptr CMpLimb) -> CMpSize -> CFBitCnt -> Ptr (Ptr CMpLimb) -> Ptr (Ptr CMpLimb) -> Ptr (Ptr CMpLimb) -> CMpSize -> CMpSize -> IO ()

-- Negacyclic multiplication ---------------------------------------------------

-- | /fft_negacyclic/ /ii/ /n/ /w/ /t1/ /t2/ /temp/ 
--
-- As per @fft_radix2@ except that it performs a sqrt2 negacyclic transform
-- of length \(2n\). This is the same as the radix 2 transform except that
-- the \(i\)-th coefficient of the input is first multiplied by
-- \(\sqrt{2}^{iw}\).
-- 
-- We require \(nw\) to be at least 64 and the two temporary space pointers
-- to point to blocks of size @n*w + FLINT_BITS@ bits.
foreign import ccall "fft.h fft_negacyclic"
  fft_negacyclic :: Ptr (Ptr CMpLimb) -> CMpSize -> CFBitCnt -> Ptr (Ptr CMpLimb) -> Ptr (Ptr CMpLimb) -> Ptr (Ptr CMpLimb) -> IO ()

-- | /ifft_negacyclic/ /ii/ /n/ /w/ /t1/ /t2/ /temp/ 
--
-- As per @ifft_radix2@ except that it performs a sqrt2 negacyclic inverse
-- transform of length \(2n\). This is the same as the radix 2 inverse
-- transform except that the \(i\)-th coefficient of the output is finally
-- divided by \(\sqrt{2}^{iw}\).
-- 
-- We require \(nw\) to be at least 64 and the two temporary space pointers
-- to point to blocks of size @n*w + FLINT_BITS@ bits.
foreign import ccall "fft.h ifft_negacyclic"
  ifft_negacyclic :: Ptr (Ptr CMpLimb) -> CMpSize -> CFBitCnt -> Ptr (Ptr CMpLimb) -> Ptr (Ptr CMpLimb) -> Ptr (Ptr CMpLimb) -> IO ()

-- | /fft_naive_convolution_1/ /r/ /ii/ /jj/ /m/ 
--
-- Performs a naive negacyclic convolution of @ii@ with @jj@, both of
-- length \(m\), and sets \(r\) to the result. This is essentially
-- multiplication of polynomials modulo \(x^m + 1\).
foreign import ccall "fft.h fft_naive_convolution_1"
  fft_naive_convolution_1 :: Ptr CMpLimb -> Ptr CMpLimb -> Ptr CMpLimb -> CMpSize -> IO ()

-- | /_fft_mulmod_2expp1/ /r1/ /i1/ /i2/ /r_limbs/ /depth/ /w/ 
--
-- Multiply @i1@ by @i2@ modulo @B^r_limbs + 1@ where
-- @r_limbs = nw\/FLINT_BITS@ with @n = 2^depth@. Uses the negacyclic FFT
-- convolution CRT\'d with a 1 limb naive convolution. We require that
-- @depth@ and @w@ have been selected as per the wrapper
-- @fft_mulmod_2expp1@ below.
foreign import ccall "fft.h _fft_mulmod_2expp1"
  _fft_mulmod_2expp1 :: Ptr CMpLimb -> Ptr CMpLimb -> Ptr CMpLimb -> CMpSize -> CFBitCnt -> CFBitCnt -> IO ()

-- | /fft_adjust_limbs/ /limbs/ 
--
-- Given a number of limbs, returns a new number of limbs (no more than the
-- next power of 2) which will work with the Nussbaumer code. It is only
-- necessary to make this adjustment if @limbs > FFT_MULMOD_2EXPP1_CUTOFF@.
foreign import ccall "fft.h fft_adjust_limbs"
  fft_adjust_limbs :: CMpSize -> IO CLong

-- | /fft_mulmod_2expp1/ /r/ /i1/ /i2/ /n/ /w/ /tt/ 
--
-- As per @_fft_mulmod_2expp1@ but with a tuned cutoff below which more
-- classical methods are used for the convolution. The temporary space is
-- required to fit @n*w + FLINT_BITS@ bits. There are no restrictions on
-- \(n\), but if @limbs = n*w\/FLINT_BITS@ then if @limbs@ exceeds
-- @FFT_MULMOD_2EXPP1_CUTOFF@ the function @fft_adjust_limbs@ must be
-- called to increase the number of limbs to an appropriate value.
foreign import ccall "fft.h fft_mulmod_2expp1"
  fft_mulmod_2expp1 :: Ptr CMpLimb -> Ptr CMpLimb -> Ptr CMpLimb -> CMpSize -> CMpSize -> Ptr CMpLimb -> IO ()

-- Integer multiplication ------------------------------------------------------

-- | /mul_truncate_sqrt2/ /r1/ /i1/ /n1/ /i2/ /n2/ /depth/ /w/ 
--
-- Integer multiplication using the radix 2 truncated sqrt2 transforms.
-- 
-- Set @(r1, n1 + n2)@ to the product of @(i1, n1)@ by @(i2, n2)@. This is
-- achieved through an FFT convolution of length at most @2^(depth + 2)@
-- with coefficients of size \(nw\) bits where @n = 2^depth@. We require
-- @depth >= 6@. The input data is broken into chunks of data not exceeding
-- @(nw - (depth + 1))\/2@ bits. If breaking the first integer into chunks
-- of this size results in @j1@ coefficients and breaking the second
-- integer results in @j2@ chunks then @j1 + j2 - 1 \<= 2^(depth + 2)@.
-- 
-- If @n = 2^depth@ then we require \(nw\) to be at least 64.
foreign import ccall "fft.h mul_truncate_sqrt2"
  mul_truncate_sqrt2 :: Ptr CMp -> Ptr CMp -> CMpSize -> Ptr CMp -> CMpSize -> CFBitCnt -> CFBitCnt -> IO ()

-- | /mul_mfa_truncate_sqrt2/ /r1/ /i1/ /n1/ /i2/ /n2/ /depth/ /w/ 
--
-- As for @mul_truncate_sqrt2@ except that the cache friendly matrix
-- Fourier algorithm is used.
-- 
-- If @n = 2^depth@ then we require \(nw\) to be at least 64. Here we also
-- require \(w\) to be \(2^i\) for some \(i \geq 0\).
foreign import ccall "fft.h mul_mfa_truncate_sqrt2"
  mul_mfa_truncate_sqrt2 :: Ptr CMp -> Ptr CMp -> CMpSize -> Ptr CMp -> CMpSize -> CFBitCnt -> CFBitCnt -> IO ()

-- | /flint_mpn_mul_fft_main/ /r1/ /i1/ /n1/ /i2/ /n2/ 
--
-- The main integer multiplication routine. Sets @(r1, n1 + n2)@ to
-- @(i1, n1)@ times @(i2, n2)@. We require @n1 >= n2 > 0@.
foreign import ccall "fft.h flint_mpn_mul_fft_main"
  flint_mpn_mul_fft_main :: Ptr CMp -> Ptr CMp -> CMpSize -> Ptr CMp -> CMpSize -> IO ()

-- Convolution -----------------------------------------------------------------

-- | /fft_convolution/ /ii/ /jj/ /depth/ /limbs/ /trunc/ /t1/ /t2/ /s1/ /tt/ 
--
-- Perform an FFT convolution of @ii@ with @jj@, both of length @4*n@ where
-- @n = 2^depth@. Assume that all but the first @trunc@ coefficients of the
-- output (placed in @ii@) are zero. Each coefficient is taken modulo
-- @B^limbs + 1@. The temporary spaces @t1@, @t2@ and @s1@ must have
-- @limbs + 1@ limbs of space and @tt@ must have @2*(limbs + 1)@ of free
-- space.
foreign import ccall "fft.h fft_convolution"
  fft_convolution :: Ptr (Ptr CMpLimb) -> Ptr (Ptr CMpLimb) -> CLong -> CLong -> CLong -> Ptr (Ptr CMpLimb) -> Ptr (Ptr CMpLimb) -> Ptr (Ptr CMpLimb) -> Ptr CMpLimb -> IO ()

-- FFT Precaching --------------------------------------------------------------

-- | /fft_precache/ /jj/ /depth/ /limbs/ /trunc/ /t1/ /t2/ /s1/ 
--
-- Precompute the FFT of @jj@ for use with precache functions. The
-- parameters are as for @fft_convolution@.
foreign import ccall "fft.h fft_precache"
  fft_precache :: Ptr (Ptr CMpLimb) -> CLong -> CLong -> CLong -> Ptr (Ptr CMpLimb) -> Ptr (Ptr CMpLimb) -> Ptr (Ptr CMpLimb) -> IO ()

-- | /fft_convolution_precache/ /ii/ /jj/ /depth/ /limbs/ /trunc/ /t1/ /t2/ /s1/ /tt/ 
--
-- As per @fft_convolution@ except that it is assumed @fft_precache@ has
-- been called on @jj@ with the same parameters. This will then run faster
-- than if @fft_convolution@ had been run with the original @jj@.
foreign import ccall "fft.h fft_convolution_precache"
  fft_convolution_precache :: Ptr (Ptr CMpLimb) -> Ptr (Ptr CMpLimb) -> CLong -> CLong -> CLong -> Ptr (Ptr CMpLimb) -> Ptr (Ptr CMpLimb) -> Ptr (Ptr CMpLimb) -> Ptr (Ptr CMpLimb) -> IO ()

