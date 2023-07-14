{-|
module      :  Data.Number.Flint.Fq.NMod.Poly.Factor.FFI
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de
-}
module Data.Number.Flint.Fq.NMod.Poly.Factor.FFI (
  -- * Factorisation of univariate polynomials over finite fields
  -- (word-size characteristic)
    FqNModPolyFactor (..)
  , CFqNModPolyFactor (..)
  , newFqNModPolyFactor
  , withFqNModPolyFactor
  -- * Memory Management
  , fq_nmod_poly_factor_init
  , fq_nmod_poly_factor_clear
  , fq_nmod_poly_factor_realloc
  , fq_nmod_poly_factor_fit_length
  -- * Basic Operations
  , fq_nmod_poly_factor_set
  , fq_nmod_poly_factor_print_pretty
  , fq_nmod_poly_factor_print
  , fq_nmod_poly_factor_insert
  , fq_nmod_poly_factor_concat
  , fq_nmod_poly_factor_pow
  , fq_nmod_poly_remove
  -- * Irreducibility Testing
  , fq_nmod_poly_is_irreducible
  , fq_nmod_poly_is_irreducible_ddf
  , fq_nmod_poly_is_irreducible_ben_or
  , _fq_nmod_poly_is_squarefree
  , fq_nmod_poly_is_squarefree
  -- * Factorisation
  , fq_nmod_poly_factor_equal_deg_prob
  , fq_nmod_poly_factor_equal_deg
  , fq_nmod_poly_factor_split_single
  , fq_nmod_poly_factor_distinct_deg
  , fq_nmod_poly_factor_squarefree
  , fq_nmod_poly_factor
  , fq_nmod_poly_factor_cantor_zassenhaus
  , fq_nmod_poly_factor_kaltofen_shoup
  , fq_nmod_poly_factor_berlekamp
  , fq_nmod_poly_factor_with_berlekamp
  , fq_nmod_poly_factor_with_cantor_zassenhaus
  , fq_nmod_poly_factor_with_kaltofen_shoup
  , fq_nmod_poly_iterated_frobenius_preinv
  -- * Root Finding
  , fq_nmod_poly_roots
) where 

-- Factorisation of univariate polynomials over finite fields
-- (word-size characteristic)

import Control.Monad

import Foreign.C.String
import Foreign.C.Types
import qualified Foreign.Concurrent
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr )
import Foreign.Marshal.Array ( advancePtr )
import Foreign.Storable
import Foreign.Marshal ( free )

import Data.Number.Flint.Flint

import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Mod.Poly

import Data.Number.Flint.NMod.Poly
import Data.Number.Flint.NMod.Mat

import Data.Number.Flint.Fq
import Data.Number.Flint.Fq.Types

import Data.Number.Flint.Fq.NMod
import Data.Number.Flint.Fq.NMod.Mat

import Data.Number.Flint.Fq.NMod
import Data.Number.Flint.Fq.NMod.Poly
import Data.Number.Flint.Fq.NMod.Types

#include <flint/flint.h>
#include <flint/fq_nmod_poly.h>

-- fq_nmod_poly_factor_t -------------------------------------------------------

instance Storable CFqNModPolyFactor where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fq_nmod_poly_factor_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fq_nmod_poly_factor_t}
  peek ptr = CFqNModPolyFactor
    <$> #{peek fq_nmod_poly_factor_struct, poly } ptr
    <*> #{peek fq_nmod_poly_factor_struct, exp  } ptr
    <*> #{peek fq_nmod_poly_factor_struct, num  } ptr
    <*> #{peek fq_nmod_poly_factor_struct, alloc} ptr
  poke = undefined

newFqNModPolyFactor ctx@(FqNModCtx ftx) = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> do
    withFqNModCtx ctx $ \ctx -> do
      fq_nmod_poly_factor_init x ctx
    addForeignPtrFinalizerEnv p_fq_nmod_poly_factor_clear x ftx
  return $ FqNModPolyFactor x

{-# INLINE withFqNModPolyFactor #-}
withFqNModPolyFactor (FqNModPolyFactor x) f = do
  withForeignPtr x $ \px -> f px >>= return . (FqNModPolyFactor x,)

-- Memory Management -----------------------------------------------------------

-- | /fq_nmod_poly_factor_init/ /fac/ /ctx/ 
--
-- Initialises @fac@ for use. An @fq_nmod_poly_factor_t@ represents a
-- polynomial in factorised form as a product of polynomials with
-- associated exponents.
foreign import ccall "fq_nmod_poly_factor.h fq_nmod_poly_factor_init"
  fq_nmod_poly_factor_init :: Ptr CFqNModPolyFactor -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_poly_factor_clear/ /fac/ /ctx/ 
--
-- Frees all memory associated with @fac@.
foreign import ccall "fq_nmod_poly_factor.h fq_nmod_poly_factor_clear"
  fq_nmod_poly_factor_clear :: Ptr CFqNModPolyFactor -> Ptr CFqNModCtx -> IO ()

foreign import ccall "fq_nmod_poly_factor.h &fq_nmod_poly_factor_clear"
  p_fq_nmod_poly_factor_clear :: FunPtr (Ptr CFqNModPolyFactor -> Ptr CFqNModCtx -> IO ())

-- | /fq_nmod_poly_factor_realloc/ /fac/ /alloc/ /ctx/ 
--
-- Reallocates the factor structure to provide space for precisely @alloc@
-- factors.
foreign import ccall "fq_nmod_poly_factor.h fq_nmod_poly_factor_realloc"
  fq_nmod_poly_factor_realloc :: Ptr CFqNModPolyFactor -> CLong -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_poly_factor_fit_length/ /fac/ /len/ /ctx/ 
--
-- Ensures that the factor structure has space for at least @len@ factors.
-- This function takes care of the case of repeated calls by always at
-- least doubling the number of factors the structure can hold.
foreign import ccall "fq_nmod_poly_factor.h fq_nmod_poly_factor_fit_length"
  fq_nmod_poly_factor_fit_length :: Ptr CFqNModPolyFactor -> CLong -> Ptr CFqNModCtx -> IO ()

-- Basic Operations ------------------------------------------------------------

-- | /fq_nmod_poly_factor_set/ /res/ /fac/ /ctx/ 
--
-- Sets @res@ to the same factorisation as @fac@.
foreign import ccall "fq_nmod_poly_factor.h fq_nmod_poly_factor_set"
  fq_nmod_poly_factor_set :: Ptr CFqNModPolyFactor -> Ptr CFqNModPolyFactor -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_poly_factor_print_pretty/ /fac/ /ctx/ 
--
-- Pretty-prints the entries of @fac@ to standard output.
fq_nmod_poly_factor_print_pretty :: Ptr CFqNModPolyFactor
                                 -> CString
                                 -> Ptr CFqNModCtx
                                 -> IO ()
fq_nmod_poly_factor_print_pretty fac var ctx = do
  CFqNModPolyFactor poly exp num alloc <- peek fac
  forM_ [0 .. fromIntegral num - 1] $ \j -> do
    fq_nmod_poly_print_pretty (poly `advancePtr` j) var ctx
    putStr " ^ "
    e <- peek (exp `advancePtr` j)
    putStrLn $ show e 


-- | /fq_nmod_poly_factor_print/ /fac/ /ctx/ 
--
-- Prints the entries of @fac@ to standard output.
foreign import ccall "fq_nmod_poly_factor.h fq_nmod_poly_factor_print"
  fq_nmod_poly_factor_print :: Ptr CFqNModPolyFactor -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_poly_factor_insert/ /fac/ /poly/ /exp/ /ctx/ 
--
-- Inserts the factor @poly@ with multiplicity @exp@ into the factorisation
-- @fac@.
-- 
-- If @fac@ already contains @poly@, then @exp@ simply gets added to the
-- exponent of the existing entry.
foreign import ccall "fq_nmod_poly_factor.h fq_nmod_poly_factor_insert"
  fq_nmod_poly_factor_insert :: Ptr CFqNModPolyFactor -> Ptr CFqNModPoly -> CLong -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_poly_factor_concat/ /res/ /fac/ /ctx/ 
--
-- Concatenates two factorisations.
-- 
-- This is equivalent to calling @fq_nmod_poly_factor_insert@ repeatedly
-- with the individual factors of @fac@.
-- 
-- Does not support aliasing between @res@ and @fac@.
foreign import ccall "fq_nmod_poly_factor.h fq_nmod_poly_factor_concat"
  fq_nmod_poly_factor_concat :: Ptr CFqNModPolyFactor -> Ptr CFqNModPolyFactor -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_poly_factor_pow/ /fac/ /exp/ /ctx/ 
--
-- Raises @fac@ to the power @exp@.
foreign import ccall "fq_nmod_poly_factor.h fq_nmod_poly_factor_pow"
  fq_nmod_poly_factor_pow :: Ptr CFqNModPolyFactor -> CLong -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_poly_remove/ /f/ /p/ /ctx/ 
--
-- Removes the highest possible power of @p@ from @f@ and returns the
-- exponent.
foreign import ccall "fq_nmod_poly_factor.h fq_nmod_poly_remove"
  fq_nmod_poly_remove :: Ptr CFqNModPoly -> Ptr CFqNModPoly -> Ptr CFqNModCtx -> IO CULong

-- Irreducibility Testing ------------------------------------------------------

-- | /fq_nmod_poly_is_irreducible/ /f/ /ctx/ 
--
-- Returns 1 if the polynomial @f@ is irreducible, otherwise returns 0.
foreign import ccall "fq_nmod_poly_factor.h fq_nmod_poly_is_irreducible"
  fq_nmod_poly_is_irreducible :: Ptr CFqNModPoly -> Ptr CFqNModCtx -> IO CInt

-- | /fq_nmod_poly_is_irreducible_ddf/ /f/ /ctx/ 
--
-- Returns 1 if the polynomial @f@ is irreducible, otherwise returns 0.
-- Uses fast distinct-degree factorisation.
foreign import ccall "fq_nmod_poly_factor.h fq_nmod_poly_is_irreducible_ddf"
  fq_nmod_poly_is_irreducible_ddf :: Ptr CFqNModPoly -> Ptr CFqNModCtx -> IO CInt

-- | /fq_nmod_poly_is_irreducible_ben_or/ /f/ /ctx/ 
--
-- Returns 1 if the polynomial @f@ is irreducible, otherwise returns 0.
-- Uses Ben-Or\'s irreducibility test.
foreign import ccall "fq_nmod_poly_factor.h fq_nmod_poly_is_irreducible_ben_or"
  fq_nmod_poly_is_irreducible_ben_or :: Ptr CFqNModPoly -> Ptr CFqNModCtx -> IO CInt

-- | /_fq_nmod_poly_is_squarefree/ /f/ /len/ /ctx/ 
--
-- Returns 1 if @(f, len)@ is squarefree, and 0 otherwise. As a special
-- case, the zero polynomial is not considered squarefree. There are no
-- restrictions on the length.
foreign import ccall "fq_nmod_poly_factor.h _fq_nmod_poly_is_squarefree"
  _fq_nmod_poly_is_squarefree :: Ptr (Ptr CFqNMod) -> CLong -> Ptr CFqNModCtx -> IO CInt

-- | /fq_nmod_poly_is_squarefree/ /f/ /ctx/ 
--
-- Returns 1 if @f@ is squarefree, and 0 otherwise. As a special case, the
-- zero polynomial is not considered squarefree.
foreign import ccall "fq_nmod_poly_factor.h fq_nmod_poly_is_squarefree"
  fq_nmod_poly_is_squarefree :: Ptr CFqNModPoly -> Ptr CFqNModCtx -> IO CInt

-- Factorisation ---------------------------------------------------------------

-- | /fq_nmod_poly_factor_equal_deg_prob/ /factor/ /state/ /pol/ /d/ /ctx/ 
--
-- Probabilistic equal degree factorisation of @pol@ into irreducible
-- factors of degree @d@. If it passes, a factor is placed in factor and 1
-- is returned, otherwise 0 is returned and the value of factor is
-- undetermined.
-- 
-- Requires that @pol@ be monic, non-constant and squarefree.
foreign import ccall "fq_nmod_poly_factor.h fq_nmod_poly_factor_equal_deg_prob"
  fq_nmod_poly_factor_equal_deg_prob :: Ptr CFqNModPoly -> Ptr CFRandState -> Ptr CFqNModPoly -> CLong -> Ptr CFqNModCtx -> IO CInt

-- | /fq_nmod_poly_factor_equal_deg/ /factors/ /pol/ /d/ /ctx/ 
--
-- Assuming @pol@ is a product of irreducible factors all of degree @d@,
-- finds all those factors and places them in factors. Requires that @pol@
-- be monic, non-constant and squarefree.
foreign import ccall "fq_nmod_poly_factor.h fq_nmod_poly_factor_equal_deg"
  fq_nmod_poly_factor_equal_deg :: Ptr CFqNModPolyFactor -> Ptr CFqNModPoly -> CLong -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_poly_factor_split_single/ /linfactor/ /input/ /ctx/ 
--
-- Assuming @input@ is a product of factors all of degree 1, finds a single
-- linear factor of @input@ and places it in @linfactor@. Requires that
-- @input@ be monic and non-constant.
foreign import ccall "fq_nmod_poly_factor.h fq_nmod_poly_factor_split_single"
  fq_nmod_poly_factor_split_single :: Ptr CFqNModPoly -> Ptr CFqNModPoly -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_poly_factor_distinct_deg/ /res/ /poly/ /degs/ /ctx/ 
--
-- Factorises a monic non-constant squarefree polynomial @poly@ of degree
-- \(n\) into factors \(f[d]\) such that for \(1 \leq d \leq n\) \(f[d]\)
-- is the product of the monic irreducible factors of @poly@ of degree
-- \(d\). Factors are stored in @res@, associated powers of irreducible
-- polynomials are stored in @degs@ in the same order as factors.
-- 
-- Requires that @degs@ have enough space for irreducible polynomials\'
-- powers (maximum space required is \(n * sizeof(slong)\)).
foreign import ccall "fq_nmod_poly_factor.h fq_nmod_poly_factor_distinct_deg"
  fq_nmod_poly_factor_distinct_deg :: Ptr CFqNModPolyFactor -> Ptr CFqNModPoly -> Ptr (Ptr CLong) -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_poly_factor_squarefree/ /res/ /f/ /ctx/ 
--
-- Sets @res@ to a squarefree factorization of @f@.
foreign import ccall "fq_nmod_poly_factor.h fq_nmod_poly_factor_squarefree"
  fq_nmod_poly_factor_squarefree :: Ptr CFqNModPolyFactor -> Ptr CFqNModPoly -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_poly_factor/ /res/ /lead/ /f/ /ctx/ 
--
-- Factorises a non-constant polynomial @f@ into monic irreducible factors
-- choosing the best algorithm for given modulo and degree. The output
-- @lead@ is set to the leading coefficient of \(f\) upon return. Choice of
-- algorithm is based on heuristic measurements.
foreign import ccall "fq_nmod_poly_factor.h fq_nmod_poly_factor"
  fq_nmod_poly_factor :: Ptr CFqNModPolyFactor -> Ptr CFqNMod -> Ptr CFqNModPoly -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_poly_factor_cantor_zassenhaus/ /res/ /f/ /ctx/ 
--
-- Factorises a non-constant polynomial @f@ into monic irreducible factors
-- using the Cantor-Zassenhaus algorithm.
foreign import ccall "fq_nmod_poly_factor.h fq_nmod_poly_factor_cantor_zassenhaus"
  fq_nmod_poly_factor_cantor_zassenhaus :: Ptr CFqNModPolyFactor -> Ptr CFqNModPoly -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_poly_factor_kaltofen_shoup/ /res/ /poly/ /ctx/ 
--
-- Factorises a non-constant polynomial @f@ into monic irreducible factors
-- using the fast version of Cantor-Zassenhaus algorithm proposed by
-- Kaltofen and Shoup (1998). More precisely this algorithm uses a “baby
-- step\/giant step” strategy for the distinct-degree factorization step.
foreign import ccall "fq_nmod_poly_factor.h fq_nmod_poly_factor_kaltofen_shoup"
  fq_nmod_poly_factor_kaltofen_shoup :: Ptr CFqNModPolyFactor -> Ptr CFqNModPoly -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_poly_factor_berlekamp/ /factors/ /f/ /ctx/ 
--
-- Factorises a non-constant polynomial @f@ into monic irreducible factors
-- using the Berlekamp algorithm.
foreign import ccall "fq_nmod_poly_factor.h fq_nmod_poly_factor_berlekamp"
  fq_nmod_poly_factor_berlekamp :: Ptr CFqNModPolyFactor -> Ptr CFqNModPoly -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_poly_factor_with_berlekamp/ /res/ /leading_coeff/ /f/ /ctx/ 
--
-- Factorises a general polynomial @f@ into monic irreducible factors and
-- sets @leading_coeff@ to the leading coefficient of @f@, or 0 if @f@ is
-- the zero polynomial.
-- 
-- This function first checks for small special cases, deflates @f@ if it
-- is of the form \(p(x^m)\) for some \(m > 1\), then performs a
-- square-free factorisation, and finally runs Berlekamp on all the
-- individual square-free factors.
foreign import ccall "fq_nmod_poly_factor.h fq_nmod_poly_factor_with_berlekamp"
  fq_nmod_poly_factor_with_berlekamp :: Ptr CFqNModPolyFactor -> Ptr CFqNMod -> Ptr CFqNModPoly -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_poly_factor_with_cantor_zassenhaus/ /res/ /leading_coeff/ /f/ /ctx/ 
--
-- Factorises a general polynomial @f@ into monic irreducible factors and
-- sets @leading_coeff@ to the leading coefficient of @f@, or 0 if @f@ is
-- the zero polynomial.
-- 
-- This function first checks for small special cases, deflates @f@ if it
-- is of the form \(p(x^m)\) for some \(m > 1\), then performs a
-- square-free factorisation, and finally runs Cantor-Zassenhaus on all the
-- individual square-free factors.
foreign import ccall "fq_nmod_poly_factor.h fq_nmod_poly_factor_with_cantor_zassenhaus"
  fq_nmod_poly_factor_with_cantor_zassenhaus :: Ptr CFqNModPolyFactor -> Ptr CFqNMod -> Ptr CFqNModPoly -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_poly_factor_with_kaltofen_shoup/ /res/ /leading_coeff/ /f/ /ctx/ 
--
-- Factorises a general polynomial @f@ into monic irreducible factors and
-- sets @leading_coeff@ to the leading coefficient of @f@, or 0 if @f@ is
-- the zero polynomial.
-- 
-- This function first checks for small special cases, deflates @f@ if it
-- is of the form \(p(x^m)\) for some \(m > 1\), then performs a
-- square-free factorisation, and finally runs Kaltofen-Shoup on all the
-- individual square-free factors.
foreign import ccall "fq_nmod_poly_factor.h fq_nmod_poly_factor_with_kaltofen_shoup"
  fq_nmod_poly_factor_with_kaltofen_shoup :: Ptr CFqNModPolyFactor -> Ptr CFqNMod -> Ptr CFqNModPoly -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_poly_iterated_frobenius_preinv/ /rop/ /n/ /v/ /vinv/ /ctx/ 
--
-- Sets @rop[i]@ to be \(x^{q^i} \bmod v\) for \(0 \le i < n\).
-- 
-- It is required that @vinv@ is the inverse of the reverse of @v@ mod
-- @x^lenv@.
foreign import ccall "fq_nmod_poly_factor.h fq_nmod_poly_iterated_frobenius_preinv"
  fq_nmod_poly_iterated_frobenius_preinv :: Ptr (Ptr CFqNModPoly) -> CLong -> Ptr CFqNModPoly -> Ptr CFqNModPoly -> Ptr CFqNModCtx -> IO ()

-- Root Finding ----------------------------------------------------------------

-- | /fq_nmod_poly_roots/ /r/ /f/ /with_multiplicity/ /ctx/ 
--
-- Fill \(r\) with factors of the form \(x - r_i\) where the \(r_i\) are
-- the distinct roots of a nonzero \(f\) in \(F_q\). If
-- \(with\_multiplicity\) is zero, the exponent \(e_i\) of the factor
-- \(x - r_i\) is \(1\). Otherwise, it is the largest \(e_i\) such that
-- \((x-r_i)^e_i\) divides \(f\). This function throws if \(f\) is zero,
-- but is otherwise always successful.
foreign import ccall "fq_nmod_poly_factor.h fq_nmod_poly_roots"
  fq_nmod_poly_roots :: Ptr CFqNModPolyFactor -> Ptr CFqNModPoly -> CInt -> Ptr CFqNModCtx -> IO ()

