module Data.Number.Flint.Fmpz.Factor.FFI (
  -- * Integer factorisation
  -- * Memory management
    newFmpzFactor
  , withFmpzFactor
  , withNewFmpzFactor
  , fmpz_factor_init
  , fmpz_factor_clear
  -- * Output
  , fmpz_factor_get_str
  , fmpz_factor_print
  , fmpz_factor_fprint
  -- * Modification
  , _fmpz_factor_append_ui
  , _fmpz_factor_append
  -- * Factoring integers
  , fmpz_factor
  , fmpz_factor_smooth
  , fmpz_factor_si
  , fmpz_factor_trial_range
  , fmpz_factor_trial
  , fmpz_factor_refine
  , fmpz_factor_expand_iterative
  , fmpz_factor_pp1
  , fmpz_factor_pollard_brent_single
  , fmpz_factor_pollard_brent
  -- * Elliptic curve (ECM) method
  , Ecm (..)
  , CEcm (..)
  , fmpz_factor_ecm_init
  , fmpz_factor_ecm_clear
  , fmpz_factor_ecm_addmod
  , fmpz_factor_ecm_submod
  , fmpz_factor_ecm_double
  , fmpz_factor_ecm_add
  , fmpz_factor_ecm_mul_montgomery_ladder
  , fmpz_factor_ecm_select_curve
  , fmpz_factor_ecm_stage_I
  , fmpz_factor_ecm_stage_II
  , fmpz_factor_ecm
) where

-- Integer factorisation -------------------------------------------------------

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr )
import Foreign.Storable
import Foreign.Marshal ( free )

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz

#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpz_factor.h>

-- FmpzFactor ------------------------------------------------------------------

newFmpzFactor = do
  x <- mallocForeignPtr
  withForeignPtr x fmpz_factor_init
  addForeignPtrFinalizer p_fmpz_factor_clear x
  return $ FmpzFactor x

{-# INLINE withFmpzFactor #-}
withFmpzFactor (FmpzFactor x) f = do
  withForeignPtr x $ \xp -> f xp >>= return . (FmpzFactor x,)

{-# INLINE withNewFmpzFactor #-}
withNewFmpzFactor f = do
  x <- newFmpzFactor
  withFmpzFactor x f

-- Ecm -------------------------------------------------------------------------

data Ecm = Ecm {-# UNPACK #-} !(ForeignPtr CEcm)
type CEcm = CFlint Ecm

-- Factoring integers ----------------------------------------------------------

-- An integer may be represented in factored form using the @fmpz_factor_t@
-- data structure. This consists of two @fmpz@ vectors representing bases
-- and exponents, respectively. Canonically, the bases will be prime
-- numbers sorted in ascending order and the exponents will be positive. A
-- separate @int@ field holds the sign, which may be \(-1\), \(0\) or
-- \(1\).
--

-- | /fmpz_factor_init/ /factor/ 
-- 
-- Initialises an @fmpz_factor_t@ structure.
foreign import ccall "fmpz_factor.h fmpz_factor_init"
  fmpz_factor_init :: Ptr CFmpzFactor -> IO ()

-- | /fmpz_factor_clear/ /factor/ 
-- 
-- Clears an @fmpz_factor_t@ structure.
foreign import ccall "fmpz_factor.h fmpz_factor_clear"
  fmpz_factor_clear :: Ptr CFmpzFactor -> IO ()

foreign import ccall "fmpz_factor.h &fmpz_factor_clear"
  p_fmpz_factor_clear :: FunPtr (Ptr CFmpzFactor -> IO ())

-- Output ----------------------------------------------------------------------

-- | /fmpz_factor_get_str/ /factor/
--
-- Get string representation of factorization
foreign import ccall "fmpz_factor_get_str"
  fmpz_factor_get_str :: Ptr CFmpzFactor -> IO CString

-- | /fmpz_factor_print/ /factor/
--
-- Print factorization
fmpz_factor_print = printCStr fmpz_factor_get_str

-- | /fmpz_factor_fprint/ /factor/
--
-- Print factorization to file
foreign import ccall "fmpz_factor_fprint"
  fmpz_factor_fprint :: Ptr CFile -> Ptr CFmpzFactor -> IO ()

--------------------------------------------------------------------------------

-- | /_fmpz_factor_append_ui/ /factor/ /p/ /exp/ 
-- 
-- Append a factor \(p\) to the given exponent to the @fmpz_factor_t@
-- structure @factor@.
foreign import ccall "fmpz_factor.h _fmpz_factor_append_ui"
  _fmpz_factor_append_ui :: Ptr CFmpzFactor -> CMpLimb -> CULong -> IO ()

-- | /_fmpz_factor_append/ /factor/ /p/ /exp/ 
-- 
-- Append a factor \(p\) to the given exponent to the @fmpz_factor_t@
-- structure @factor@.
foreign import ccall "fmpz_factor.h _fmpz_factor_append"
  _fmpz_factor_append :: Ptr CFmpzFactor -> Ptr CFmpz -> CULong -> IO ()

-- | /fmpz_factor/ /factor/ /n/ 
-- 
-- Factors \(n\) into prime numbers. If \(n\) is zero or negative, the sign
-- field of the @factor@ object will be set accordingly.
foreign import ccall "fmpz_factor.h fmpz_factor"
  fmpz_factor :: Ptr CFmpzFactor -> Ptr CFmpz -> IO ()

-- | /fmpz_factor_smooth/ /factor/ /n/ /bits/ /proved/ 
-- 
-- Factors \(n\) into prime numbers up to approximately the given number of
-- bits and possibly one additional cofactor, which may or may not be
-- prime.
-- 
-- If the number is definitely factored fully, the return value is \(1\),
-- otherwise the final factor (which may have exponent greater than \(1\))
-- is composite and needs to be factored further.
-- 
-- If the number has a factor of around the given number of bits, there is
-- at least a two-thirds chance of finding it. Smaller factors should be
-- found with a much higher probability.
-- 
-- The amount of time spent factoring can be controlled by lowering or
-- increasing @bits@. However, the quadratic sieve may be faster if @bits@
-- is set to more than one third of the number of bits of \(n\).
-- 
-- The function uses trial factoring up to @bits = 15@, followed by a
-- primality test and a perfect power test to check if the factorisation is
-- complete. If @bits@ is at least 16, it proceeds to use the elliptic
-- curve method to look for larger factors.
-- 
-- The behavior of primality testing is determined by the @proved@
-- parameter:
-- 
-- If @proved@ is set to \(1\) the function will prove all factors prime
-- (other than the last factor, if the return value is \(0\)).
-- 
-- If @proved@ is set to \(0\), the function will only check that factors
-- are probable primes.
-- 
-- If @proved@ is set to \(-1\), the function will not test primality after
-- performing trial division. A perfect power test is still performed.
-- 
-- As an exception to the rules stated above, this function will call
-- @n_factor@ internally if \(n\) or the remainder after trial division is
-- smaller than one word, guaranteeing a complete factorisation.
foreign import ccall "fmpz_factor.h fmpz_factor_smooth"
  fmpz_factor_smooth :: Ptr CFmpzFactor -> Ptr CFmpz -> CLong -> CInt -> IO CInt

-- | /fmpz_factor_si/ /factor/ /n/ 
-- 
-- Like @fmpz_factor@, but takes a machine integer \(n\) as input.
foreign import ccall "fmpz_factor.h fmpz_factor_si"
  fmpz_factor_si :: Ptr CFmpzFactor -> CLong -> IO ()

-- | /fmpz_factor_trial_range/ /factor/ /n/ /start/ /num_primes/ 
-- 
-- Factors \(n\) into prime factors using trial division. If \(n\) is zero
-- or negative, the sign field of the @factor@ object will be set
-- accordingly.
-- 
-- The algorithm starts with the given start index in the @flint_primes@
-- table and uses at most @num_primes@ primes from that point.
-- 
-- The function returns 1 if \(n\) is completely factored, otherwise it
-- returns \(0\).
foreign import ccall "fmpz_factor.h fmpz_factor_trial_range"
  fmpz_factor_trial_range :: Ptr CFmpzFactor -> Ptr CFmpz -> CULong -> CULong -> IO CInt

-- | /fmpz_factor_trial/ /factor/ /n/ /num_primes/ 
-- 
-- Factors \(n\) into prime factors using trial division. If \(n\) is zero
-- or negative, the sign field of the @factor@ object will be set
-- accordingly.
-- 
-- The algorithm uses the given number of primes, which must be in the
-- range \([0, 3512]\). An exception is raised if a number outside this
-- range is passed.
-- 
-- The function returns 1 if \(n\) is completely factored, otherwise it
-- returns \(0\).
-- 
-- The final entry in the factor struct is set to the cofactor after
-- removing prime factors, if this is not \(1\).
foreign import ccall "fmpz_factor.h fmpz_factor_trial"
  fmpz_factor_trial :: Ptr CFmpzFactor -> Ptr CFmpz -> CLong -> IO CInt

-- | /fmpz_factor_refine/ /res/ /f/ 
-- 
-- Attempts to improve a partial factorization of an integer by
-- \"refining\" the factorization @f@ to a more complete factorization
-- @res@ whose bases are pairwise relatively prime.
-- 
-- This function does not require its input to be in canonical form, nor
-- does it guarantee that the resulting factorization will be canonical.
foreign import ccall "fmpz_factor.h fmpz_factor_refine"
  fmpz_factor_refine :: Ptr CFmpzFactor -> Ptr CFmpzFactor -> IO ()

-- | /fmpz_factor_expand_iterative/ /n/ /factor/ 
-- 
-- Evaluates an integer in factored form back to an @fmpz_t@.
-- 
-- This currently exponentiates the bases separately and multiplies them
-- together one by one, although much more efficient algorithms exist.
foreign import ccall "fmpz_factor.h fmpz_factor_expand_iterative"
  fmpz_factor_expand_iterative :: Ptr CFmpz -> Ptr CFmpzFactor -> IO ()

-- | /fmpz_factor_pp1/ /factor/ /n/ /B1/ /B2_sqrt/ /c/ 
-- 
-- Use Williams\' \(p + 1\) method to factor \(n\), using a prime bound in
-- stage 1 of @B1@ and a prime limit in stage 2 of at least the square of
-- @B2_sqrt@. If a factor is found, the function returns \(1\) and @factor@
-- is set to the factor that is found. Otherwise, the function returns
-- \(0\).
-- 
-- The value \(c\) should be a random value greater than \(2\). Successive
-- calls to the function with different values of \(c\) give additional
-- chances to factor \(n\) with roughly exponentially decaying probability
-- of finding a factor which has been missed (if \(p+1\) or \(p-1\) is not
-- smooth for any prime factors \(p\) of \(n\) then the function will not
-- ever succeed).
foreign import ccall "fmpz_factor.h fmpz_factor_pp1"
  fmpz_factor_pp1 :: Ptr CFmpz -> Ptr CFmpz -> CULong -> CULong -> CULong -> IO CInt

-- | /fmpz_factor_pollard_brent_single/ /p_factor/ /n_in/ /yi/ /ai/ /max_iters/ 
-- 
-- Pollard Rho algorithm for integer factorization. Assumes that the \(n\)
-- is not prime. @factor@ is set as the factor if found. Takes as input the
-- initial value \(y\), to start polynomial evaluation and \(a\), the
-- constant of the polynomial used. It is not assured that the factor found
-- will be prime. Does not compute the complete factorization, just one
-- factor. Returns the number of limbs of factor if factorization is
-- successful (non trivial factor is found), else returns 0.
-- 
-- @max_iters@ is the number of iterations tried in process of finding the
-- cycle. If the algorithm fails to find a non trivial factor in one call,
-- it tries again (this time with a different set of random values).
foreign import ccall "fmpz_factor.h fmpz_factor_pollard_brent_single"
  fmpz_factor_pollard_brent_single :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CMpLimb -> IO CInt

-- | /fmpz_factor_pollard_brent/ /factor/ /state/ /n/ /max_tries/ /max_iters/ 
-- 
-- Pollard Rho algorithm for integer factorization. Assumes that the \(n\)
-- is not prime. @factor@ is set as the factor if found. It is not assured
-- that the factor found will be prime. Does not compute the complete
-- factorization, just one factor. Returns the number of limbs of factor if
-- factorization is successful (non trivial factor is found), else returns
-- 0.
-- 
-- @max_iters@ is the number of iterations tried in process of finding the
-- cycle. If the algorithm fails to find a non trivial factor in one call,
-- it tries again (this time with a different set of random values). This
-- process is repeated a maximum of @max_tries@ times.
-- 
-- The algorithm used is a modification of the original Pollard Rho
-- algorithm, suggested by Richard Brent. It can be found in the paper
-- available at <https://maths-people.anu.edu.au/~brent/pd/rpb051i.pdf>
foreign import ccall "fmpz_factor.h fmpz_factor_pollard_brent"
  fmpz_factor_pollard_brent :: Ptr CFmpz -> Ptr CFRandState -> Ptr CFmpz -> CMpLimb -> CMpLimb -> IO CInt

-- Elliptic curve (ECM) method -------------------------------------------------

-- Factoring of @fmpz@ integers using ECM
--
-- | /fmpz_factor_ecm_init/ /ecm_inf/ /sz/ 
-- 
-- Initializes the @ecm_t@ struct. This is needed in some functions and
-- carries data between subsequent calls.
foreign import ccall "fmpz_factor.h fmpz_factor_ecm_init"
  fmpz_factor_ecm_init :: Ptr CEcm -> CMpLimb -> IO ()

-- | /fmpz_factor_ecm_clear/ /ecm_inf/ 
-- 
-- Clears the @ecm_t@ struct.
foreign import ccall "fmpz_factor.h fmpz_factor_ecm_clear"
  fmpz_factor_ecm_clear :: Ptr CEcm -> IO ()

-- | /fmpz_factor_ecm_addmod/ /a/ /b/ /c/ /n/ /n_size/ 
-- 
-- Sets \(a\) to \((b + c)\) @%@ \(n\). This is not a normal add mod
-- function, it assumes \(n\) is normalized (highest bit set) and \(b\) and
-- \(c\) are reduced modulo \(n\).
-- 
-- Used for arithmetic operations in @fmpz_factor_ecm@.
foreign import ccall "fmpz_factor.h fmpz_factor_ecm_addmod"
  fmpz_factor_ecm_addmod :: Ptr CMp -> Ptr CMp -> Ptr CMp -> Ptr CMp -> CMpLimb -> IO ()

-- | /fmpz_factor_ecm_submod/ /x/ /a/ /b/ /n/ /n_size/ 
-- 
-- Sets \(x\) to \((a - b)\) @%@ \(n\). This is not a normal subtract mod
-- function, it assumes \(n\) is normalized (highest bit set) and \(b\) and
-- \(c\) are reduced modulo \(n\).
-- 
-- Used for arithmetic operations in @fmpz_factor_ecm@.
foreign import ccall "fmpz_factor.h fmpz_factor_ecm_submod"
  fmpz_factor_ecm_submod :: Ptr CMp -> Ptr CMp -> Ptr CMp -> Ptr CMp -> CMpLimb -> IO ()

-- | /fmpz_factor_ecm_double/ /x/ /z/ /x0/ /z0/ /n/ /ecm_inf/ 
-- 
-- Sets the point \((x : z)\) to two times \((x_0 : z_0)\) modulo \(n\)
-- according to the formula
-- 
-- \[`\]
-- \[x = (x_0 + z_0)^2 \cdot (x_0 - z_0)^2 \mod n,\]
-- 
-- \[`\]
-- \[z = 4 x_0 z_0 \left((x_0 - z_0)^2 + 4a_{24}x_0z_0\right) \mod n.\]
-- 
-- @ecm_inf@ is used just to use temporary @mp_ptr@\'s in the structure.
-- This group doubling is valid only for points expressed in Montgomery
-- projective coordinates.
foreign import ccall "fmpz_factor.h fmpz_factor_ecm_double"
  fmpz_factor_ecm_double :: Ptr CMp -> Ptr CMp -> Ptr CMp -> Ptr CMp -> Ptr CMp -> Ptr CEcm -> IO ()

-- | /fmpz_factor_ecm_add/ /x/ /z/ /x1/ /z1/ /x2/ /z2/ /x0/ /z0/ /n/ /ecm_inf/ 
-- 
-- Sets the point \((x : z)\) to the sum of \((x_1 : z_1)\) and
-- \((x_2 : z_2)\) modulo \(n\), given the difference \((x_0 : z_0)\)
-- according to the formula
-- 
-- \[`\]
-- \[\begin{aligned}
-- x = 4z_0(x_1x_2 - z_1z_2)^2 \mod n, \\ z = 4x_0(x_2z_1 - x_1z_2)^2 \mod n.
-- \end{aligned}\]
-- 
-- @ecm_inf@ is used just to use temporary @mp_ptr@\'s in the structure.
-- This group addition is valid only for points expressed in Montgomery
-- projective coordinates.
foreign import ccall "fmpz_factor.h fmpz_factor_ecm_add"
  fmpz_factor_ecm_add :: Ptr CMp -> Ptr CMp -> Ptr CMp -> Ptr CMp -> Ptr CMp -> Ptr CMp -> Ptr CMp -> Ptr CMp -> Ptr CMp -> Ptr CEcm -> IO ()

-- | /fmpz_factor_ecm_mul_montgomery_ladder/ /x/ /z/ /x0/ /z0/ /k/ /n/ /ecm_inf/ 
-- 
-- Montgomery ladder algorithm for scalar multiplication of elliptic
-- points.
-- 
-- Sets the point \((x : z)\) to \(k(x_0 : z_0)\) modulo \(n\).
-- 
-- @ecm_inf@ is used just to use temporary @mp_ptr@\'s in the structure.
-- Valid only for points expressed in Montgomery projective coordinates.
foreign import ccall "fmpz_factor.h fmpz_factor_ecm_mul_montgomery_ladder"
  fmpz_factor_ecm_mul_montgomery_ladder :: Ptr CMp -> Ptr CMp -> Ptr CMp -> Ptr CMp -> CMpLimb -> Ptr CMp -> Ptr CEcm -> IO ()

-- | /fmpz_factor_ecm_select_curve/ /f/ /sigma/ /n/ /ecm_inf/ 
-- 
-- Selects a random elliptic curve given a random integer @sigma@,
-- according to Suyama\'s parameterization. If the factor is found while
-- selecting the curve, the number of limbs required to store the factor is
-- returned, otherwise \(0\).
-- 
-- It could be possible that the selected curve is unsuitable for further
-- computations, in such a case, \(-1\) is returned.
-- 
-- Also selects the initial point \(x_0\), and the value of \((a + 2)/4\),
-- where \(a\) is a curve parameter. Sets \(z_0\) as \(1\). All these are
-- stored in the @ecm_t@ struct.
-- 
-- The curve selected is of Montgomery form, the points selected satisfy
-- the curve and are projective coordinates.
foreign import ccall "fmpz_factor.h fmpz_factor_ecm_select_curve"
  fmpz_factor_ecm_select_curve :: Ptr CMp -> Ptr CMp -> Ptr CMp -> Ptr CEcm -> IO CInt

-- | /fmpz_factor_ecm_stage_I/ /f/ /prime_array/ /num/ /B1/ /n/ /ecm_inf/ 
-- 
-- Stage I implementation of the ECM algorithm.
-- 
-- @f@ is set as the factor if found. @num@ is number of prime numbers
-- \(\le\) the bound @B1@. @prime_array@ is an array of first @B1@ primes.
-- \(n\) is the number being factored.
-- 
-- If the factor is found, number of words required to store the factor is
-- returned, otherwise \(0\).
foreign import ccall "fmpz_factor.h fmpz_factor_ecm_stage_I"
  fmpz_factor_ecm_stage_I :: Ptr CMp -> Ptr CMpLimb -> CMpLimb -> CMpLimb -> Ptr CMp -> Ptr CEcm -> IO CInt

-- | /fmpz_factor_ecm_stage_II/ /f/ /B1/ /B2/ /P/ /n/ /ecm_inf/ 
-- 
-- Stage II implementation of the ECM algorithm.
-- 
-- @f@ is set as the factor if found. @B1@, @B2@ are the two bounds. @P@ is
-- the primorial (approximately equal to \(\sqrt{B2}\)). \(n\) is the
-- number being factored.
-- 
-- If the factor is found, number of words required to store the factor is
-- returned, otherwise \(0\).
foreign import ccall "fmpz_factor.h fmpz_factor_ecm_stage_II"
  fmpz_factor_ecm_stage_II :: Ptr CMp -> CMpLimb -> CMpLimb -> CMpLimb -> Ptr CMp -> Ptr CEcm -> IO CInt

-- | /fmpz_factor_ecm/ /f/ /curves/ /B1/ /B2/ /state/ /n_in/ 
-- 
-- Outer wrapper function for the ECM algorithm. In case @f@ can fit in a
-- single unsigned word, a call to @n_factor_ecm@ is made.
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
foreign import ccall "fmpz_factor.h fmpz_factor_ecm"
  fmpz_factor_ecm :: Ptr CFmpz -> CMpLimb -> CMpLimb -> CMpLimb -> Ptr CFRandState -> Ptr CFmpz -> IO CInt

