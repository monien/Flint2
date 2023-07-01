{-# language
    CApiFFI
  , FlexibleInstances
  , ForeignFunctionInterface
  , MultiParamTypeClasses
  , TupleSections
  , TypeFamilies
  #-}

module Data.Number.Flint.NMod.Poly.Factor.FFI (
  -- * Factorisation of univariate polynomials over integers mod n (word-size n)
  -- * Types
    NModPolyFactor (..)
  , CNModPolyFactor (..)
  , newNModPolyFactor
  , withNModPolyFactor
  , withNewNModPolyFactor
  -- * Memory management
  , nmod_poly_factor_init
  , nmod_poly_factor_clear
  , nmod_poly_factor_realloc
  , nmod_poly_factor_fit_length
  , nmod_poly_factor_set
  -- * Output
  , nmod_poly_factor_print
  , nmod_poly_factor_print_pretty
  , nmod_poly_factor_fprint
  , nmod_poly_factor_fprint_pretty
  , nmod_poly_factor_get_str
  , nmod_poly_factor_get_str_pretty
  -- * Basic manipulations
  , nmod_poly_factor_insert
  , nmod_poly_factor_concat
  , nmod_poly_factor_pow
  , nmod_poly_remove
  , nmod_poly_is_irreducible
  , nmod_poly_is_irreducible_ddf
  , nmod_poly_is_irreducible_rabin
  , _nmod_poly_is_squarefree
  , nmod_poly_is_squarefree
  -- * Factorizations
  , nmod_poly_factor_squarefree
  , nmod_poly_factor_equal_deg_prob
  , nmod_poly_factor_equal_deg
  , nmod_poly_factor_distinct_deg
  , nmod_poly_factor_distinct_deg_threaded
  , nmod_poly_factor_cantor_zassenhaus
  , nmod_poly_factor_berlekamp
  , nmod_poly_factor_kaltofen_shoup
  , nmod_poly_factor_with_berlekamp
  , nmod_poly_factor_with_cantor_zassenhaus
  , nmod_poly_factor_with_kaltofen_shoup
  , nmod_poly_factor
  , _nmod_poly_interval_poly_worker
) where

-- Factorisation of univariate polynomials over integers mod n (word-size n)

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr )
import Foreign.Storable
import Foreign.Marshal ( free )

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.NMod
import Data.Number.Flint.NMod.Types
import Data.Number.Flint.ThreadPool

#include <flint/nmod_poly_factor.h>

-- Types -----------------------------------------------------------------------

-- | Create new `NModPolyFactor`
newNModPolyFactor = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> nmod_poly_factor_init x
  addForeignPtrFinalizer p_nmod_poly_factor_clear x
  return $ NModPolyFactor x

-- | Use `NModPolyFactor`
{-# INLINE withNModPolyFactor #-}
withNModPolyFactor (NModPolyFactor x) f = do
  withForeignPtr x $ \px -> f px >>= return . (NModPolyFactor x,)

-- | Use new `NModPolyFactor`
{-# INLINE withNewNModPolyFactor #-}
withNewNModPolyFactor f = do
  x <- newNModPolyFactor
  withNModPolyFactor x $ \x -> f x

-- Factorisation ---------------------------------------------------------------

-- | /nmod_poly_factor_init/ /fac/ 
-- 
-- Initialises @fac@ for use. An @nmod_poly_factor_t@ represents a
-- polynomial in factorised form as a product of polynomials with
-- associated exponents.
foreign import ccall "nmod_poly_factor.h nmod_poly_factor_init"
  nmod_poly_factor_init :: Ptr CNModPolyFactor -> IO ()

-- | /nmod_poly_factor_clear/ /fac/ 
-- 
-- Frees all memory associated with @fac@.
foreign import ccall "nmod_poly_factor.h nmod_poly_factor_clear"
  nmod_poly_factor_clear :: Ptr CNModPolyFactor -> IO ()

foreign import ccall "nmod_poly_factor.h &nmod_poly_factor_clear"
  p_nmod_poly_factor_clear :: FunPtr (Ptr CNModPolyFactor -> IO ())

-- | /nmod_poly_factor_realloc/ /fac/ /alloc/ 
-- 
-- Reallocates the factor structure to provide space for precisely @alloc@
-- factors.
foreign import ccall "nmod_poly_factor.h nmod_poly_factor_realloc"
  nmod_poly_factor_realloc :: Ptr CNModPolyFactor -> CLong -> IO ()

-- | /nmod_poly_factor_fit_length/ /fac/ /len/ 
-- 
-- Ensures that the factor structure has space for at least @len@ factors.
-- This function takes care of the case of repeated calls by always at
-- least doubling the number of factors the structure can hold.
foreign import ccall "nmod_poly_factor.h nmod_poly_factor_fit_length"
  nmod_poly_factor_fit_length :: Ptr CNModPolyFactor -> CLong -> IO ()

-- | /nmod_poly_factor_set/ /res/ /fac/ 
-- 
-- Sets @res@ to the same factorisation as @fac@.
foreign import ccall "nmod_poly_factor.h nmod_poly_factor_set"
  nmod_poly_factor_set :: Ptr CNModPolyFactor -> Ptr CNModPolyFactor -> IO ()

-- Input and output ------------------------------------------------------------

-- | /nmod_poly_factor_get_str/ /fac/
-- 
-- Returns string representation of the entries of @fac@.
foreign import ccall "nmod_poly_factor.h nmod_poly_factor_get_str"
  nmod_poly_factor_get_str :: Ptr CNModPolyFactor -> IO CString

-- | /nmod_poly_factor_get_str_pretty/ /fac/ /x/
-- 
-- Returns string representation of the entries of @fac@ as polynomials.
foreign import ccall "nmod_poly_factor.h nmod_poly_factor_get_str_pretty"
  nmod_poly_factor_get_str_pretty :: Ptr CNModPolyFactor -> CString -> IO CString

-- | /nmod_poly_factor_fprint/ /fac/ 
-- 
-- Prints the entries of @fac@ to stream.
foreign import ccall "nmod_poly_factor.h nmod_poly_factor_fprint"
  nmod_poly_factor_fprint :: Ptr CFile -> Ptr CNModPolyFactor -> IO ()

-- | /nmod_poly_factor_fprint_pretty/ /fac/ /x/
-- 
-- Prints the entries of @fac@ to stream a polynomials.
foreign import ccall "nmod_poly_factor.h nmod_poly_factor_fprint_pretty"
  nmod_poly_factor_fprint_pretty :: Ptr CFile -> Ptr CNModPolyFactor -> CString -> IO ()

-- | /nmod_poly_factor_print/ /fac/ 
-- 
-- Prints the entries of @fac@ to standard output.
nmod_poly_factor_print :: Ptr CNModPolyFactor -> IO ()
nmod_poly_factor_print fac = do
  printCStr nmod_poly_factor_get_str fac
  return ()

-- | /nmod_poly_factor_print_pretty/ /fac/ /x/
-- 
-- Prints the entries of @fac@ to standard output as polynomials.
nmod_poly_factor_print_pretty :: Ptr CNModPolyFactor -> CString -> IO ()
nmod_poly_factor_print_pretty fac x = do
  printCStr (\fac -> nmod_poly_factor_get_str_pretty fac x) fac
  return ()
  
--------------------------------------------------------------------------------

-- | /nmod_poly_factor_insert/ /fac/ /poly/ /exp/ 
-- 
-- Inserts the factor @poly@ with multiplicity @exp@ into the factorisation
-- @fac@.
-- 
-- If @fac@ already contains @poly@, then @exp@ simply gets added to the
-- exponent of the existing entry.
foreign import ccall "nmod_poly_factor.h nmod_poly_factor_insert"
  nmod_poly_factor_insert :: Ptr CNModPolyFactor -> Ptr CNModPoly -> CLong -> IO ()

-- | /nmod_poly_factor_concat/ /res/ /fac/ 
-- 
-- Concatenates two factorisations.
-- 
-- This is equivalent to calling @nmod_poly_factor_insert@ repeatedly with
-- the individual factors of @fac@.
-- 
-- Does not support aliasing between @res@ and @fac@.
foreign import ccall "nmod_poly_factor.h nmod_poly_factor_concat"
  nmod_poly_factor_concat :: Ptr CNModPolyFactor -> Ptr CNModPolyFactor -> IO ()

-- | /nmod_poly_factor_pow/ /fac/ /exp/ 
-- 
-- Raises @fac@ to the power @exp@.
foreign import ccall "nmod_poly_factor.h nmod_poly_factor_pow"
  nmod_poly_factor_pow :: Ptr CNModPolyFactor -> CLong -> IO ()

-- | /nmod_poly_remove/ /f/ /p/ 
-- 
-- Removes the highest possible power of @p@ from @f@ and returns the
-- exponent.
foreign import ccall "nmod_poly_factor.h nmod_poly_remove"
  nmod_poly_remove :: Ptr CNModPoly -> Ptr CNModPoly -> IO CULong

-- | /nmod_poly_is_irreducible/ /f/ 
-- 
-- Returns 1 if the polynomial @f@ is irreducible, otherwise returns 0.
foreign import ccall "nmod_poly_factor.h nmod_poly_is_irreducible"
  nmod_poly_is_irreducible :: Ptr CNModPoly -> IO CInt

-- | /nmod_poly_is_irreducible_ddf/ /f/ 
-- 
-- Returns 1 if the polynomial @f@ is irreducible, otherwise returns 0.
-- Uses fast distinct-degree factorisation.
foreign import ccall "nmod_poly_factor.h nmod_poly_is_irreducible_ddf"
  nmod_poly_is_irreducible_ddf :: Ptr CNModPoly -> IO CInt

-- | /nmod_poly_is_irreducible_rabin/ /f/ 
-- 
-- Returns 1 if the polynomial @f@ is irreducible, otherwise returns 0.
-- Uses Rabin irreducibility test.
foreign import ccall "nmod_poly_factor.h nmod_poly_is_irreducible_rabin"
  nmod_poly_is_irreducible_rabin :: Ptr CNModPoly -> IO CInt

-- | /_nmod_poly_is_squarefree/ /f/ /len/ /mod/ 
-- 
-- Returns 1 if @(f, len)@ is squarefree, and 0 otherwise. As a special
-- case, the zero polynomial is not considered squarefree. There are no
-- restrictions on the length.
foreign import ccall "nmod_poly_factor.h _nmod_poly_is_squarefree"
  _nmod_poly_is_squarefree :: Ptr CMp -> CLong -> Ptr CNMod -> IO CInt

-- | /nmod_poly_is_squarefree/ /f/ 
-- 
-- Returns 1 if @f@ is squarefree, and 0 otherwise. As a special case, the
-- zero polynomial is not considered squarefree.
foreign import ccall "nmod_poly_factor.h nmod_poly_is_squarefree"
  nmod_poly_is_squarefree :: Ptr CNModPoly -> IO CInt

-- | /nmod_poly_factor_squarefree/ /res/ /f/ 
-- 
-- Sets @res@ to a square-free factorization of @f@.
foreign import ccall "nmod_poly_factor.h nmod_poly_factor_squarefree"
  nmod_poly_factor_squarefree :: Ptr CNModPolyFactor -> Ptr CNModPoly -> IO ()

-- | /nmod_poly_factor_equal_deg_prob/ /factor/ /state/ /pol/ /d/ 
-- 
-- Probabilistic equal degree factorisation of @pol@ into irreducible
-- factors of degree @d@. If it passes, a factor is placed in factor and 1
-- is returned, otherwise 0 is returned and the value of factor is
-- undetermined.
-- 
-- Requires that @pol@ be monic, non-constant and squarefree.
foreign import ccall "nmod_poly_factor.h nmod_poly_factor_equal_deg_prob"
  nmod_poly_factor_equal_deg_prob :: Ptr CNModPoly -> Ptr CFRandState -> Ptr CNModPoly -> CLong -> IO CInt

-- | /nmod_poly_factor_equal_deg/ /factors/ /pol/ /d/ 
-- 
-- Assuming @pol@ is a product of irreducible factors all of degree @d@,
-- finds all those factors and places them in factors. Requires that @pol@
-- be monic, non-constant and squarefree.
foreign import ccall "nmod_poly_factor.h nmod_poly_factor_equal_deg"
  nmod_poly_factor_equal_deg :: Ptr CNModPolyFactor -> Ptr CNModPoly -> CLong -> IO ()

-- | /nmod_poly_factor_distinct_deg/ /res/ /poly/ /degs/ 
-- 
-- Factorises a monic non-constant squarefree polynomial @poly@ of degree n
-- into factors \(f[d]\) such that for \(1 \leq d \leq n\) \(f[d]\) is the
-- product of the monic irreducible factors of @poly@ of degree \(d\).
-- Factors \(f[d]\) are stored in @res@, and the degree \(d\) of the
-- irreducible factors is stored in @degs@ in the same order as the
-- factors.
-- 
-- Requires that @degs@ has enough space for @(n\/2)+1 * sizeof(slong)@.
foreign import ccall "nmod_poly_factor.h nmod_poly_factor_distinct_deg"
  nmod_poly_factor_distinct_deg :: Ptr CNModPolyFactor -> Ptr CNModPoly -> Ptr (Ptr CLong) -> IO ()

-- | /nmod_poly_factor_distinct_deg_threaded/ /res/ /poly/ /degs/ 
-- 
-- Multithreaded version of @nmod_poly_factor_distinct_deg@.
foreign import ccall "nmod_poly_factor.h nmod_poly_factor_distinct_deg_threaded"
  nmod_poly_factor_distinct_deg_threaded :: Ptr CNModPolyFactor -> Ptr CNModPoly -> Ptr (Ptr CLong) -> IO ()

-- | /nmod_poly_factor_cantor_zassenhaus/ /res/ /f/ 
-- 
-- Factorises a non-constant polynomial @f@ into monic irreducible factors
-- using the Cantor-Zassenhaus algorithm.
foreign import ccall "nmod_poly_factor.h nmod_poly_factor_cantor_zassenhaus"
  nmod_poly_factor_cantor_zassenhaus :: Ptr CNModPolyFactor -> Ptr CNModPoly -> IO ()

-- | /nmod_poly_factor_berlekamp/ /res/ /f/ 
-- 
-- Factorises a non-constant, squarefree polynomial @f@ into monic
-- irreducible factors using the Berlekamp algorithm.
foreign import ccall "nmod_poly_factor.h nmod_poly_factor_berlekamp"
  nmod_poly_factor_berlekamp :: Ptr CNModPolyFactor -> Ptr CNModPoly -> IO ()

-- | /nmod_poly_factor_kaltofen_shoup/ /res/ /poly/ 
-- 
-- Factorises a non-constant polynomial @f@ into monic irreducible factors
-- using the fast version of Cantor-Zassenhaus algorithm proposed by
-- Kaltofen and Shoup (1998). More precisely this algorithm uses a “baby
-- step\/giant step” strategy for the distinct-degree factorization step.
-- If @flint_get_num_threads@ is greater than one
-- @nmod_poly_factor_distinct_deg_threaded@ is used.
foreign import ccall "nmod_poly_factor.h nmod_poly_factor_kaltofen_shoup"
  nmod_poly_factor_kaltofen_shoup :: Ptr CNModPolyFactor -> Ptr CNModPoly -> IO ()

-- | /nmod_poly_factor_with_berlekamp/ /res/ /f/ 
-- 
-- Factorises a general polynomial @f@ into monic irreducible factors and
-- returns the leading coefficient of @f@, or 0 if @f@ is the zero
-- polynomial.
-- 
-- This function first checks for small special cases, deflates @f@ if it
-- is of the form \(p(x^m)\) for some \(m > 1\), then performs a
-- square-free factorisation, and finally runs Berlekamp on all the
-- individual square-free factors.
foreign import ccall "nmod_poly_factor.h nmod_poly_factor_with_berlekamp"
  nmod_poly_factor_with_berlekamp :: Ptr CNModPolyFactor -> Ptr CNModPoly -> IO CMpLimb

-- | /nmod_poly_factor_with_cantor_zassenhaus/ /res/ /f/ 
-- 
-- Factorises a general polynomial @f@ into monic irreducible factors and
-- returns the leading coefficient of @f@, or 0 if @f@ is the zero
-- polynomial.
-- 
-- This function first checks for small special cases, deflates @f@ if it
-- is of the form \(p(x^m)\) for some \(m > 1\), then performs a
-- square-free factorisation, and finally runs Cantor-Zassenhaus on all the
-- individual square-free factors.
foreign import ccall "nmod_poly_factor.h nmod_poly_factor_with_cantor_zassenhaus"
  nmod_poly_factor_with_cantor_zassenhaus :: Ptr CNModPolyFactor -> Ptr CNModPoly -> IO CMpLimb

-- | /nmod_poly_factor_with_kaltofen_shoup/ /res/ /f/ 
-- 
-- Factorises a general polynomial @f@ into monic irreducible factors and
-- returns the leading coefficient of @f@, or 0 if @f@ is the zero
-- polynomial.
-- 
-- This function first checks for small special cases, deflates @f@ if it
-- is of the form \(p(x^m)\) for some \(m > 1\), then performs a
-- square-free factorisation, and finally runs Kaltofen-Shoup on all the
-- individual square-free factors.
foreign import ccall "nmod_poly_factor.h nmod_poly_factor_with_kaltofen_shoup"
  nmod_poly_factor_with_kaltofen_shoup :: Ptr CNModPolyFactor -> Ptr CNModPoly -> IO CMpLimb

-- | /nmod_poly_factor/ /res/ /f/ 
-- 
-- Factorises a general polynomial @f@ into monic irreducible factors and
-- returns the leading coefficient of @f@, or 0 if @f@ is the zero
-- polynomial.
-- 
-- This function first checks for small special cases, deflates @f@ if it
-- is of the form \(p(x^m)\) for some \(m > 1\), then performs a
-- square-free factorisation, and finally runs either Cantor-Zassenhaus or
-- Berlekamp on all the individual square-free factors. Currently
-- Cantor-Zassenhaus is used by default unless the modulus is 2, in which
-- case Berlekamp is used.
foreign import ccall "nmod_poly_factor.h nmod_poly_factor"
  nmod_poly_factor :: Ptr CNModPolyFactor -> Ptr CNModPoly -> IO CMpLimb

-- | /_nmod_poly_interval_poly_worker/ /arg_ptr/ 
-- 
-- Worker function to compute interval polynomials in distinct degree
-- factorisation. Input\/output is stored in
-- @nmod_poly_interval_poly_arg_t@.
foreign import ccall "nmod_poly_factor.h _nmod_poly_interval_poly_worker"
  _nmod_poly_interval_poly_worker :: Ptr () -> IO ()

