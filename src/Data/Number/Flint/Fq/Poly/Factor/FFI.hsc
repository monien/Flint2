{-# language
    CApiFFI
  , FlexibleInstances
  , ForeignFunctionInterface
  , MultiParamTypeClasses
  , TupleSections
  , TypeFamilies
  #-}
  
module Data.Number.Flint.Fq.Poly.Factor.FFI (
  -- * Factorisation of univariate polynomials over finite fields
    FqPolyFactor (..)
  , CFqPolyFactor (..)
  , newFqPolyFactor
  , withFqPolyFactor
  , withNewFqPolyFactor
  -- * Memory Management
  , fq_poly_factor_init
  , fq_poly_factor_clear
  , fq_poly_factor_realloc
  , fq_poly_factor_fit_length
  -- * Basic Operations
  , fq_poly_factor_set
  , fq_poly_factor_print_pretty
  , fq_poly_factor_print
  , fq_poly_factor_insert
  , fq_poly_factor_concat
  , fq_poly_factor_pow
  , fq_poly_remove
  -- * Irreducibility Testing
  , fq_poly_is_irreducible
  , fq_poly_is_irreducible_ddf
  , fq_poly_is_irreducible_ben_or
  , _fq_poly_is_squarefree
  , fq_poly_is_squarefree
  -- * Factorisation
  , fq_poly_factor_equal_deg_prob
  , fq_poly_factor_equal_deg
  , fq_poly_factor_split_single
  , fq_poly_factor_distinct_deg
  , fq_poly_factor_squarefree
  , fq_poly_factor
  , fq_poly_factor_cantor_zassenhaus
  , fq_poly_factor_kaltofen_shoup
  , fq_poly_factor_berlekamp
  , fq_poly_factor_with_berlekamp
  , fq_poly_factor_with_cantor_zassenhaus
  , fq_poly_factor_with_kaltofen_shoup
  , fq_poly_iterated_frobenius_preinv
  -- * Root Finding
  , fq_poly_roots
) where 

-- Factorisation of univariate polynomials over finite fields ------------------

import Control.Monad

import Foreign.C.String
import Foreign.C.Types
import qualified Foreign.Concurrent
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr )
import Foreign.Storable
import Foreign.Marshal ( free )
import Foreign.Marshal.Array ( advancePtr )

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Mod.Poly
import Data.Number.Flint.Fmpz.Mod.Mat
import Data.Number.Flint.Fmpq
import Data.Number.Flint.Fq
import Data.Number.Flint.Fq.Poly

#include <flint/flint.h>

#include <flint/fmpz.h>
#include <flint/fmpz_poly.h>

#include <flint/fq.h>
#include <flint/fq_poly.h>

-- fq_poly_factor_t ------------------------------------------------------------

data FqPolyFactor = FqPolyFactor {-# UNPACK #-} !(ForeignPtr CFqPolyFactor)
data CFqPolyFactor = CFqPolyFactor (Ptr CFqPoly) (Ptr CLong) CLong CLong

instance Storable CFqPolyFactor where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fq_poly_factor_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fq_poly_factor_t}
  peek ptr = do
    poly  <- #{peek fq_poly_factor_struct, poly } ptr
    exp   <- #{peek fq_poly_factor_struct, exp } ptr
    num   <- #{peek fq_poly_factor_struct, num } ptr
    alloc <- #{peek fq_poly_factor_struct, alloc } ptr
    return $ CFqPolyFactor poly exp num alloc
  poke = undefined

newFqPolyFactor ctx@(FqCtx fctx) = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> do
    withFqCtx ctx $ \ctx -> do
      fq_poly_factor_init x ctx
    addForeignPtrFinalizerEnv p_fq_poly_factor_clear x fctx
  return $ FqPolyFactor x

{-# INLINE withFqPolyFactor #-}
withFqPolyFactor (FqPolyFactor x) f = do
  withForeignPtr x $ \px -> f px >>= return . (FqPolyFactor x,)

{-# INLINE withNewFqPolyFactor #-}
withNewFqPolyFactor ctx f = do
  x <- newFqPolyFactor ctx
  withFqPolyFactor x f
  
-- Memory Management -----------------------------------------------------------

-- | /fq_poly_factor_init/ /fac/ /ctx/ 
--
-- Initialises @fac@ for use. An @fq_poly_factor_t@ represents a polynomial
-- in factorised form as a product of polynomials with associated
-- exponents.
foreign import ccall "fq_poly_factor.h fq_poly_factor_init"
  fq_poly_factor_init :: Ptr CFqPolyFactor -> Ptr CFqCtx -> IO ()

-- | /fq_poly_factor_clear/ /fac/ /ctx/ 
--
-- Frees all memory associated with @fac@.
foreign import ccall "fq_poly_factor.h fq_poly_factor_clear"
  fq_poly_factor_clear :: Ptr CFqPolyFactor -> Ptr CFqCtx -> IO ()

foreign import ccall "fq_poly_factor.h &fq_poly_factor_clear"
  p_fq_poly_factor_clear :: FunPtr (Ptr CFqPolyFactor -> Ptr CFqCtx -> IO ())

-- | /fq_poly_factor_realloc/ /fac/ /alloc/ /ctx/ 
--
-- Reallocates the factor structure to provide space for precisely @alloc@
-- factors.
foreign import ccall "fq_poly_factor.h fq_poly_factor_realloc"
  fq_poly_factor_realloc :: Ptr CFqPolyFactor -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_factor_fit_length/ /fac/ /len/ /ctx/ 
--
-- Ensures that the factor structure has space for at least @len@ factors.
-- This function takes care of the case of repeated calls by always at
-- least doubling the number of factors the structure can hold.
foreign import ccall "fq_poly_factor.h fq_poly_factor_fit_length"
  fq_poly_factor_fit_length :: Ptr CFqPolyFactor -> CLong -> Ptr CFqCtx -> IO ()

-- Basic Operations ------------------------------------------------------------

-- | /fq_poly_factor_set/ /res/ /fac/ /ctx/ 
--
-- Sets @res@ to the same factorisation as @fac@.
foreign import ccall "fq_poly_factor.h fq_poly_factor_set"
  fq_poly_factor_set :: Ptr CFqPolyFactor -> Ptr CFqPolyFactor -> Ptr CFqCtx -> IO ()

-- | /fq_poly_factor_print_pretty/ /fac/ /var/ /ctx/ 
-- 
-- Pretty-prints the entries of @fac@ to standard output.
fq_poly_factor_print_pretty fac var ctx = do
  CFqPolyFactor poly exp num alloc <- peek fac
  forM_ [0..fromIntegral num-1] $ \j -> do
    fq_poly_print_pretty (poly `advancePtr` j) var ctx
    m <- peek (exp `advancePtr` j)
    putStrLn $ " ^ " ++ show m
    
-- | /fq_poly_factor_print/ /fac/ /ctx/ 
-- 
-- Prints the entries of @fac@ to standard output.
fq_poly_factor_print fac ctx = do
  CFqPolyFactor poly exp num alloc <- peek fac
  forM_ [0..fromIntegral num-1] $ \j -> do
    fq_poly_print (poly `advancePtr` j) ctx
    m <- peek (exp `advancePtr` j)
    putStrLn $ " ^ " ++ show m

-- | /fq_poly_factor_insert/ /fac/ /poly/ /exp/ /ctx/ 
--
-- Inserts the factor @poly@ with multiplicity @exp@ into the factorisation
-- @fac@.
-- 
-- If @fac@ already contains @poly@, then @exp@ simply gets added to the
-- exponent of the existing entry.
foreign import ccall "fq_poly_factor.h fq_poly_factor_insert"
  fq_poly_factor_insert :: Ptr CFqPolyFactor -> Ptr CFqPoly -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_factor_concat/ /res/ /fac/ /ctx/ 
--
-- Concatenates two factorisations.
-- 
-- This is equivalent to calling @fq_poly_factor_insert@ repeatedly with
-- the individual factors of @fac@.
-- 
-- Does not support aliasing between @res@ and @fac@.
foreign import ccall "fq_poly_factor.h fq_poly_factor_concat"
  fq_poly_factor_concat :: Ptr CFqPolyFactor -> Ptr CFqPolyFactor -> Ptr CFqCtx -> IO ()

-- | /fq_poly_factor_pow/ /fac/ /exp/ /ctx/ 
--
-- Raises @fac@ to the power @exp@.
foreign import ccall "fq_poly_factor.h fq_poly_factor_pow"
  fq_poly_factor_pow :: Ptr CFqPolyFactor -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_remove/ /f/ /p/ /ctx/ 
--
-- Removes the highest possible power of @p@ from @f@ and returns the
-- exponent.
foreign import ccall "fq_poly_factor.h fq_poly_remove"
  fq_poly_remove :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO CULong

-- Irreducibility Testing ------------------------------------------------------

-- | /fq_poly_is_irreducible/ /f/ /ctx/ 
--
-- Returns 1 if the polynomial @f@ is irreducible, otherwise returns 0.
foreign import ccall "fq_poly_factor.h fq_poly_is_irreducible"
  fq_poly_is_irreducible :: Ptr CFqPoly -> Ptr CFqCtx -> IO CInt

-- | /fq_poly_is_irreducible_ddf/ /f/ /ctx/ 
--
-- Returns 1 if the polynomial @f@ is irreducible, otherwise returns 0.
-- Uses fast distinct-degree factorisation.
foreign import ccall "fq_poly_factor.h fq_poly_is_irreducible_ddf"
  fq_poly_is_irreducible_ddf :: Ptr CFqPoly -> Ptr CFqCtx -> IO CInt

-- | /fq_poly_is_irreducible_ben_or/ /f/ /ctx/ 
--
-- Returns 1 if the polynomial @f@ is irreducible, otherwise returns 0.
-- Uses Ben-Or\'s irreducibility test.
foreign import ccall "fq_poly_factor.h fq_poly_is_irreducible_ben_or"
  fq_poly_is_irreducible_ben_or :: Ptr CFqPoly -> Ptr CFqCtx -> IO CInt

-- | /_fq_poly_is_squarefree/ /f/ /len/ /ctx/ 
--
-- Returns 1 if @(f, len)@ is squarefree, and 0 otherwise. As a special
-- case, the zero polynomial is not considered squarefree. There are no
-- restrictions on the length.
foreign import ccall "fq_poly_factor.h _fq_poly_is_squarefree"
  _fq_poly_is_squarefree :: Ptr (Ptr CFq) -> CLong -> Ptr CFqCtx -> IO CInt

-- | /fq_poly_is_squarefree/ /f/ /ctx/ 
--
-- Returns 1 if @f@ is squarefree, and 0 otherwise. As a special case, the
-- zero polynomial is not considered squarefree.
foreign import ccall "fq_poly_factor.h fq_poly_is_squarefree"
  fq_poly_is_squarefree :: Ptr CFqPoly -> Ptr CFqCtx -> IO CInt

-- Factorisation ---------------------------------------------------------------

-- | /fq_poly_factor_equal_deg_prob/ /factor/ /state/ /pol/ /d/ /ctx/ 
--
-- Probabilistic equal degree factorisation of @pol@ into irreducible
-- factors of degree @d@. If it passes, a factor is placed in factor and 1
-- is returned, otherwise 0 is returned and the value of factor is
-- undetermined.
-- 
-- Requires that @pol@ be monic, non-constant and squarefree.
foreign import ccall "fq_poly_factor.h fq_poly_factor_equal_deg_prob"
  fq_poly_factor_equal_deg_prob :: Ptr CFqPoly -> Ptr CFRandState -> Ptr CFqPoly -> CLong -> Ptr CFqCtx -> IO CInt

-- | /fq_poly_factor_equal_deg/ /factors/ /pol/ /d/ /ctx/ 
--
-- Assuming @pol@ is a product of irreducible factors all of degree @d@,
-- finds all those factors and places them in factors. Requires that @pol@
-- be monic, non-constant and squarefree.
foreign import ccall "fq_poly_factor.h fq_poly_factor_equal_deg"
  fq_poly_factor_equal_deg :: Ptr CFqPolyFactor -> Ptr CFqPoly -> CLong -> Ptr CFqCtx -> IO ()

-- | /fq_poly_factor_split_single/ /linfactor/ /input/ /ctx/ 
--
-- Assuming @input@ is a product of factors all of degree 1, finds a single
-- linear factor of @input@ and places it in @linfactor@. Requires that
-- @input@ be monic and non-constant.
foreign import ccall "fq_poly_factor.h fq_poly_factor_split_single"
  fq_poly_factor_split_single :: Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /fq_poly_factor_distinct_deg/ /res/ /poly/ /degs/ /ctx/ 
--
-- Factorises a monic non-constant squarefree polynomial @poly@ of degree
-- \(n\) into factors \(f[d]\) such that for \(1 \leq d \leq n\) \(f[d]\)
-- is the product of the monic irreducible factors of @poly@ of degree
-- \(d\). Factors are stored in @res@, associated powers of irreducible
-- polynomials are stored in @degs@ in the same order as factors.
-- 
-- Requires that @degs@ have enough space for irreducible polynomials\'
-- powers (maximum space required is @n * sizeof(slong)@).
foreign import ccall "fq_poly_factor.h fq_poly_factor_distinct_deg"
  fq_poly_factor_distinct_deg :: Ptr CFqPolyFactor -> Ptr CFqPoly -> Ptr (Ptr CLong) -> Ptr CFqCtx -> IO ()

-- | /fq_poly_factor_squarefree/ /res/ /f/ /ctx/ 
--
-- Sets @res@ to a squarefree factorization of @f@.
foreign import ccall "fq_poly_factor.h fq_poly_factor_squarefree"
  fq_poly_factor_squarefree :: Ptr CFqPolyFactor -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /fq_poly_factor/ /res/ /lead/ /f/ /ctx/ 
--
-- Factorises a non-constant polynomial @f@ into monic irreducible factors
-- choosing the best algorithm for given modulo and degree. The output
-- @lead@ is set to the leading coefficient of \(f\) upon return. Choice of
-- algorithm is based on heuristic measurements.
foreign import ccall "fq_poly_factor.h fq_poly_factor"
  fq_poly_factor :: Ptr CFqPolyFactor -> Ptr CFq -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /fq_poly_factor_cantor_zassenhaus/ /res/ /f/ /ctx/ 
--
-- Factorises a non-constant polynomial @f@ into monic irreducible factors
-- using the Cantor-Zassenhaus algorithm.
foreign import ccall "fq_poly_factor.h fq_poly_factor_cantor_zassenhaus"
  fq_poly_factor_cantor_zassenhaus :: Ptr CFqPolyFactor -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /fq_poly_factor_kaltofen_shoup/ /res/ /poly/ /ctx/ 
--
-- Factorises a non-constant polynomial @f@ into monic irreducible factors
-- using the fast version of Cantor-Zassenhaus algorithm proposed by
-- Kaltofen and Shoup (1998). More precisely this algorithm uses a “baby
-- step\/giant step” strategy for the distinct-degree factorization step.
foreign import ccall "fq_poly_factor.h fq_poly_factor_kaltofen_shoup"
  fq_poly_factor_kaltofen_shoup :: Ptr CFqPolyFactor -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /fq_poly_factor_berlekamp/ /factors/ /f/ /ctx/ 
--
-- Factorises a non-constant polynomial @f@ into monic irreducible factors
-- using the Berlekamp algorithm.
foreign import ccall "fq_poly_factor.h fq_poly_factor_berlekamp"
  fq_poly_factor_berlekamp :: Ptr CFqPolyFactor -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /fq_poly_factor_with_berlekamp/ /res/ /leading_coeff/ /f/ /ctx/ 
--
-- Factorises a general polynomial @f@ into monic irreducible factors and
-- sets @leading_coeff@ to the leading coefficient of @f@, or 0 if @f@ is
-- the zero polynomial.
-- 
-- This function first checks for small special cases, deflates @f@ if it
-- is of the form \(p(x^m)\) for some \(m > 1\), then performs a
-- square-free factorisation, and finally runs Berlekamp factorisation on
-- all the individual square-free factors.
foreign import ccall "fq_poly_factor.h fq_poly_factor_with_berlekamp"
  fq_poly_factor_with_berlekamp :: Ptr CFqPolyFactor -> Ptr CFq -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /fq_poly_factor_with_cantor_zassenhaus/ /res/ /leading_coeff/ /f/ /ctx/ 
--
-- Factorises a general polynomial @f@ into monic irreducible factors and
-- sets @leading_coeff@ to the leading coefficient of @f@, or 0 if @f@ is
-- the zero polynomial.
-- 
-- This function first checks for small special cases, deflates @f@ if it
-- is of the form \(p(x^m)\) for some \(m > 1\), then performs a
-- square-free factorisation, and finally runs Cantor-Zassenhaus on all the
-- individual square-free factors.
foreign import ccall "fq_poly_factor.h fq_poly_factor_with_cantor_zassenhaus"
  fq_poly_factor_with_cantor_zassenhaus :: Ptr CFqPolyFactor -> Ptr CFq -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /fq_poly_factor_with_kaltofen_shoup/ /res/ /leading_coeff/ /f/ /ctx/ 
--
-- Factorises a general polynomial @f@ into monic irreducible factors and
-- sets @leading_coeff@ to the leading coefficient of @f@, or 0 if @f@ is
-- the zero polynomial.
-- 
-- This function first checks for small special cases, deflates @f@ if it
-- is of the form \(p(x^m)\) for some \(m > 1\), then performs a
-- square-free factorisation, and finally runs Kaltofen-Shoup on all the
-- individual square-free factors.
foreign import ccall "fq_poly_factor.h fq_poly_factor_with_kaltofen_shoup"
  fq_poly_factor_with_kaltofen_shoup :: Ptr CFqPolyFactor -> Ptr CFq -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- | /fq_poly_iterated_frobenius_preinv/ /rop/ /n/ /v/ /vinv/ /ctx/ 
--
-- Sets @rop[i]@ to be \(x^{q^i}\bmod v\) for \(0 \le i < n\).
-- 
-- It is required that @vinv@ is the inverse of the reverse of @v@ mod
-- @x^lenv@.
foreign import ccall "fq_poly_factor.h fq_poly_iterated_frobenius_preinv"
  fq_poly_iterated_frobenius_preinv :: Ptr (Ptr CFqPoly) -> CLong -> Ptr CFqPoly -> Ptr CFqPoly -> Ptr CFqCtx -> IO ()

-- Root Finding ----------------------------------------------------------------

-- | /fq_poly_roots/ /r/ /f/ /with_multiplicity/ /ctx/ 
--
-- Fill \(r\) with factors of the form \(x - r_i\) where the \(r_i\) are
-- the distinct roots of a nonzero \(f\) in \(F_q\). If
-- \(with\_multiplicity\) is zero, the exponent \(e_i\) of the factor
-- \(x - r_i\) is \(1\). Otherwise, it is the largest \(e_i\) such that
-- \((x-r_i)^e_i\) divides \(f\). This function throws if \(f\) is zero,
-- but is otherwise always successful.
foreign import ccall "fq_poly_factor.h fq_poly_roots"
  fq_poly_roots :: Ptr CFqPolyFactor -> Ptr CFqPoly -> CInt -> Ptr CFqCtx -> IO ()

