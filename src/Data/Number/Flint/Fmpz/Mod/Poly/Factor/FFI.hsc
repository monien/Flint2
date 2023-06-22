{-# language
    CApiFFI
  , FlexibleInstances
  , ForeignFunctionInterface
  , MultiParamTypeClasses
  , TupleSections
  , TypeFamilies
  #-}

module Data.Number.Flint.Fmpz.Mod.Poly.Factor.FFI (
  -- * Factorisation of polynomials over integers mod n
    FmpzModPolyFactor (..)
  , CFmpzModPolyFactor (..)
  , newFmpzModPolyFactor
  , withFmpzModPolyFactor
  -- * Factorisation
  , fmpz_mod_poly_factor_init
  , fmpz_mod_poly_factor_clear
  , fmpz_mod_poly_factor_realloc
  , fmpz_mod_poly_factor_fit_length
  , fmpz_mod_poly_factor_set
  , fmpz_mod_poly_factor_print
  , fmpz_mod_poly_factor_print_pretty
  , fmpz_mod_poly_factor_insert
  , fmpz_mod_poly_factor_concat
  , fmpz_mod_poly_factor_pow
  , fmpz_mod_poly_is_irreducible
  , fmpz_mod_poly_is_irreducible_ddf
  , fmpz_mod_poly_is_irreducible_rabin
  , fmpz_mod_poly_is_irreducible_rabin_f
  , _fmpz_mod_poly_is_squarefree
  , _fmpz_mod_poly_is_squarefree_f
  , fmpz_mod_poly_is_squarefree
  , fmpz_mod_poly_is_squarefree_f
  , fmpz_mod_poly_factor_equal_deg_prob
  , fmpz_mod_poly_factor_equal_deg
  , fmpz_mod_poly_factor_distinct_deg
  , fmpz_mod_poly_factor_distinct_deg_threaded
  , fmpz_mod_poly_factor_squarefree
  , fmpz_mod_poly_factor
  , fmpz_mod_poly_factor_cantor_zassenhaus
  , fmpz_mod_poly_factor_kaltofen_shoup
  , fmpz_mod_poly_factor_berlekamp
  --, _fmpz_mod_poly_interval_poly_worker
  -- * Root Finding
  , fmpz_mod_poly_roots
  , fmpz_mod_poly_roots_factored
) where

-- Factorisation of polynomials over integers mod n ----------------------------

import Control.Monad

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr )
import Foreign.Storable
import Foreign.Marshal ( free )

import Data.Number.Flint.Flint
import Data.Number.Flint.ThreadPool
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Poly
import Data.Number.Flint.Fmpz.Mat
import Data.Number.Flint.Fmpz.Mod
import Data.Number.Flint.Fmpz.Mod.Poly

#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpz_mod_poly.h>
#include <flint/fmpz_mod_poly_factor.h>

-- fmpz_mod_poly_factor_t ------------------------------------------------------

data FmpzModPolyFactor =
  FmpzModPolyFactor {-# UNPACK #-} !(ForeignPtr CFmpzModPolyFactor)
data CFmpzModPolyFactor = CFmpzModPolyFactor (Ptr CFmpzModPoly) (Ptr CLong) CLong CLong  

instance Storable CFmpzModPolyFactor where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fmpz_mod_poly_factor_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fmpz_mod_poly_factor_t}
  peek ptr = return CFmpzModPolyFactor 
    `ap` #{peek fmpz_mod_poly_factor_struct, poly } ptr
    `ap` #{peek fmpz_mod_poly_factor_struct, exp  } ptr
    `ap` #{peek fmpz_mod_poly_factor_struct, num  } ptr
    `ap` #{peek fmpz_mod_poly_factor_struct, alloc} ptr
  poke = undefined

newFmpzModPolyFactor ctx@(FmpzModCtx mtx) = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> do
    withFmpzModCtx ctx $ \ctx -> do
      fmpz_mod_poly_factor_init x ctx
    addForeignPtrFinalizerEnv p_fmpz_mod_poly_factor_clear x mtx
  return $ FmpzModPolyFactor x

{-# INLINE withFmpzModPolyFactor #-}
withFmpzModPolyFactor (FmpzModPolyFactor x) f = do
  withForeignPtr x $ \px -> f px >>= return . (FmpzModPolyFactor x,)
  
-- Factorisation ---------------------------------------------------------------

-- | /fmpz_mod_poly_factor_init/ /fac/ /ctx/ 
--
-- Initialises @fac@ for use.
foreign import ccall "fmpz_mod_poly_factor.h fmpz_mod_poly_factor_init"
  fmpz_mod_poly_factor_init :: Ptr CFmpzModPolyFactor -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_factor_clear/ /fac/ /ctx/ 
--
-- Frees all memory associated with @fac@.
foreign import ccall "fmpz_mod_poly_factor.h fmpz_mod_poly_factor_clear"
  fmpz_mod_poly_factor_clear :: Ptr CFmpzModPolyFactor -> Ptr CFmpzModCtx -> IO ()

foreign import ccall "fmpz_mod_poly_factor.h &fmpz_mod_poly_factor_clear"
  p_fmpz_mod_poly_factor_clear :: FunPtr (Ptr CFmpzModPolyFactor -> Ptr CFmpzModCtx -> IO ())

-- | /fmpz_mod_poly_factor_realloc/ /fac/ /alloc/ /ctx/ 
--
-- Reallocates the factor structure to provide space for precisely @alloc@
-- factors.
foreign import ccall "fmpz_mod_poly_factor.h fmpz_mod_poly_factor_realloc"
  fmpz_mod_poly_factor_realloc :: Ptr CFmpzModPolyFactor -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_factor_fit_length/ /fac/ /len/ /ctx/ 
--
-- Ensures that the factor structure has space for at least @len@ factors.
-- This function takes care of the case of repeated calls by always at
-- least doubling the number of factors the structure can hold.
foreign import ccall "fmpz_mod_poly_factor.h fmpz_mod_poly_factor_fit_length"
  fmpz_mod_poly_factor_fit_length :: Ptr CFmpzModPolyFactor -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_factor_set/ /res/ /fac/ /ctx/ 
--
-- Sets @res@ to the same factorisation as @fac@.
foreign import ccall "fmpz_mod_poly_factor.h fmpz_mod_poly_factor_set"
  fmpz_mod_poly_factor_set :: Ptr CFmpzModPolyFactor -> Ptr CFmpzModPolyFactor -> Ptr CFmpzModCtx -> IO ()

foreign import ccall "fmpz_mod_poly_factor.h fmpz_mod_poly_factor_get_str"
  fmpz_mod_poly_factor_get_str :: Ptr CFmpzModPolyFactor -> Ptr CFmpzModCtx -> IO CString

foreign import ccall "fmpz_mod_poly_factor.h fmpz_mod_poly_factor_get_str_pretty"
  fmpz_mod_poly_factor_get_str_pretty :: Ptr CFmpzModPolyFactor -> CString -> Ptr CFmpzModCtx -> IO CString

-- | /fmpz_mod_poly_factor_print/ /fac/ /ctx/ 
--
-- Prints the entries of @fac@ to standard output.
fmpz_mod_poly_factor_print :: Ptr CFmpzModPolyFactor -> Ptr CFmpzModCtx -> IO ()
fmpz_mod_poly_factor_print fac ctx = do
  printCStr (flip fmpz_mod_poly_factor_get_str ctx) fac
  return ()

-- | /fmpz_mod_poly_factor_print_pretty/ /fac/ /var/ /ctx/ 
--
-- Prints the entries of @fac@ to standard output.
fmpz_mod_poly_factor_print_pretty :: Ptr CFmpzModPolyFactor -> CString -> Ptr CFmpzModCtx -> IO ()
fmpz_mod_poly_factor_print_pretty fac var ctx = do
  printCStr (\fac -> fmpz_mod_poly_factor_get_str_pretty fac var ctx) fac
  return ()

-- | /fmpz_mod_poly_factor_insert/ /fac/ /poly/ /exp/ /ctx/ 
--
-- Inserts the factor @poly@ with multiplicity @exp@ into the factorisation
-- @fac@.
-- 
-- If @fac@ already contains @poly@, then @exp@ simply gets added to the
-- exponent of the existing entry.
foreign import ccall "fmpz_mod_poly_factor.h fmpz_mod_poly_factor_insert"
  fmpz_mod_poly_factor_insert :: Ptr CFmpzModPolyFactor -> Ptr CFmpzModPoly -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_factor_concat/ /res/ /fac/ /ctx/ 
--
-- Concatenates two factorisations.
-- 
-- This is equivalent to calling @fmpz_mod_poly_factor_insert@ repeatedly
-- with the individual factors of @fac@.
-- 
-- Does not support aliasing between @res@ and @fac@.
foreign import ccall "fmpz_mod_poly_factor.h fmpz_mod_poly_factor_concat"
  fmpz_mod_poly_factor_concat :: Ptr CFmpzModPolyFactor -> Ptr CFmpzModPolyFactor -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_factor_pow/ /fac/ /exp/ /ctx/ 
--
-- Raises @fac@ to the power @exp@.
foreign import ccall "fmpz_mod_poly_factor.h fmpz_mod_poly_factor_pow"
  fmpz_mod_poly_factor_pow :: Ptr CFmpzModPolyFactor -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_is_irreducible/ /f/ /ctx/ 
--
-- Returns 1 if the polynomial @f@ is irreducible, otherwise returns 0.
foreign import ccall "fmpz_mod_poly_factor.h fmpz_mod_poly_is_irreducible"
  fmpz_mod_poly_is_irreducible :: Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO CInt

-- | /fmpz_mod_poly_is_irreducible_ddf/ /f/ /ctx/ 
--
-- Returns 1 if the polynomial @f@ is irreducible, otherwise returns 0.
-- Uses fast distinct-degree factorisation.
foreign import ccall "fmpz_mod_poly_factor.h fmpz_mod_poly_is_irreducible_ddf"
  fmpz_mod_poly_is_irreducible_ddf :: Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO CInt

-- | /fmpz_mod_poly_is_irreducible_rabin/ /f/ /ctx/ 
--
-- Returns 1 if the polynomial @f@ is irreducible, otherwise returns 0.
-- Uses Rabin irreducibility test.
foreign import ccall "fmpz_mod_poly_factor.h fmpz_mod_poly_is_irreducible_rabin"
  fmpz_mod_poly_is_irreducible_rabin :: Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO CInt

-- | /fmpz_mod_poly_is_irreducible_rabin_f/ /r/ /f/ /ctx/ 
--
-- Either sets \(r\) to \(1\) and returns 1 if the polynomial @f@ is
-- irreducible or \(0\) otherwise, or sets \(r\) to a nontrivial factor of
-- \(p\).
-- 
-- This algorithm correctly determines whether \(f\) is irreducible over
-- \(\mathbb{Z}/p\mathbb{Z}\), even for composite \(f\), or it finds a
-- factor of \(p\).
foreign import ccall "fmpz_mod_poly_factor.h fmpz_mod_poly_is_irreducible_rabin_f"
  fmpz_mod_poly_is_irreducible_rabin_f :: Ptr CFmpz -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO CInt

-- | /_fmpz_mod_poly_is_squarefree/ /f/ /len/ /ctx/ 
--
-- Returns 1 if @(f, len)@ is squarefree, and 0 otherwise. As a special
-- case, the zero polynomial is not considered squarefree. There are no
-- restrictions on the length.
foreign import ccall "fmpz_mod_poly_factor.h _fmpz_mod_poly_is_squarefree"
  _fmpz_mod_poly_is_squarefree :: Ptr CFmpz -> CLong -> Ptr CFmpzModCtx -> IO CInt

-- | /_fmpz_mod_poly_is_squarefree_f/ /fac/ /f/ /len/ /ctx/ 
--
-- If \(fac\) returns with the value \(1\) then the function operates as
-- per @_fmpz_mod_poly_is_squarefree@, otherwise \(f\) is set to a
-- nontrivial factor of \(p\).
foreign import ccall "fmpz_mod_poly_factor.h _fmpz_mod_poly_is_squarefree_f"
  _fmpz_mod_poly_is_squarefree_f :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpzModCtx -> IO CInt

-- | /fmpz_mod_poly_is_squarefree/ /f/ /ctx/ 
--
-- Returns 1 if @f@ is squarefree, and 0 otherwise. As a special case, the
-- zero polynomial is not considered squarefree.
foreign import ccall "fmpz_mod_poly_factor.h fmpz_mod_poly_is_squarefree"
  fmpz_mod_poly_is_squarefree :: Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO CInt

-- | /fmpz_mod_poly_is_squarefree_f/ /fac/ /f/ /ctx/ 
--
-- If \(fac\) returns with the value \(1\) then the function operates as
-- per @fmpz_mod_poly_is_squarefree@, otherwise \(f\) is set to a
-- nontrivial factor of \(p\).
foreign import ccall "fmpz_mod_poly_factor.h fmpz_mod_poly_is_squarefree_f"
  fmpz_mod_poly_is_squarefree_f :: Ptr CFmpz -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO CInt

-- | /fmpz_mod_poly_factor_equal_deg_prob/ /factor/ /state/ /pol/ /d/ /ctx/ 
--
-- Probabilistic equal degree factorisation of @pol@ into irreducible
-- factors of degree @d@. If it passes, a factor is placed in @factor@ and
-- 1 is returned, otherwise 0 is returned and the value of factor is
-- undetermined.
-- 
-- Requires that @pol@ be monic, non-constant and squarefree.
foreign import ccall "fmpz_mod_poly_factor.h fmpz_mod_poly_factor_equal_deg_prob"
  fmpz_mod_poly_factor_equal_deg_prob :: Ptr CFmpzModPoly -> Ptr CFRandState -> Ptr CFmpzModPoly -> CLong -> Ptr CFmpzModCtx -> IO CInt

-- | /fmpz_mod_poly_factor_equal_deg/ /factors/ /pol/ /d/ /ctx/ 
--
-- Assuming @pol@ is a product of irreducible factors all of degree @d@,
-- finds all those factors and places them in factors. Requires that @pol@
-- be monic, non-constant and squarefree.
foreign import ccall "fmpz_mod_poly_factor.h fmpz_mod_poly_factor_equal_deg"
  fmpz_mod_poly_factor_equal_deg :: Ptr CFmpzModPolyFactor -> Ptr CFmpzModPoly -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_factor_distinct_deg/ /res/ /poly/ /degs/ /ctx/ 
--
-- Factorises a monic non-constant squarefree polynomial @poly@ of degree
-- \(n\) into factors \(f[d]\) such that for \(1 \leq d \leq n\) \(f[d]\)
-- is the product of the monic irreducible factors of @poly@ of degree
-- \(d\). Factors \(f[d]\) are stored in @res@, and the degree \(d\) of the
-- irreducible factors is stored in @degs@ in the same order as the
-- factors.
-- 
-- Requires that @degs@ has enough space for \((n/2)+1 * sizeof(slong)\).
foreign import ccall "fmpz_mod_poly_factor.h fmpz_mod_poly_factor_distinct_deg"
  fmpz_mod_poly_factor_distinct_deg :: Ptr CFmpzModPolyFactor -> Ptr CFmpzModPoly -> Ptr (Ptr CLong) -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_factor_distinct_deg_threaded/ /res/ /poly/ /degs/ /ctx/ 
--
-- Multithreaded version of @fmpz_mod_poly_factor_distinct_deg@.
foreign import ccall "fmpz_mod_poly_factor.h fmpz_mod_poly_factor_distinct_deg_threaded"
  fmpz_mod_poly_factor_distinct_deg_threaded :: Ptr CFmpzModPolyFactor -> Ptr CFmpzModPoly -> Ptr (Ptr CLong) -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_factor_squarefree/ /res/ /f/ /ctx/ 
--
-- Sets @res@ to a squarefree factorization of @f@.
foreign import ccall "fmpz_mod_poly_factor.h fmpz_mod_poly_factor_squarefree"
  fmpz_mod_poly_factor_squarefree :: Ptr CFmpzModPolyFactor -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_factor/ /res/ /f/ /ctx/ 
--
-- Factorises a non-constant polynomial @f@ into monic irreducible factors
-- choosing the best algorithm for given modulo and degree. Choice is based
-- on heuristic measurements.
foreign import ccall "fmpz_mod_poly_factor.h fmpz_mod_poly_factor"
  fmpz_mod_poly_factor :: Ptr CFmpzModPolyFactor -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_factor_cantor_zassenhaus/ /res/ /f/ /ctx/ 
--
-- Factorises a non-constant polynomial @f@ into monic irreducible factors
-- using the Cantor-Zassenhaus algorithm.
foreign import ccall "fmpz_mod_poly_factor.h fmpz_mod_poly_factor_cantor_zassenhaus"
  fmpz_mod_poly_factor_cantor_zassenhaus :: Ptr CFmpzModPolyFactor -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_factor_kaltofen_shoup/ /res/ /poly/ /ctx/ 
--
-- Factorises a non-constant polynomial @poly@ into monic irreducible
-- factors using the fast version of Cantor-Zassenhaus algorithm proposed
-- by Kaltofen and Shoup (1998). More precisely this algorithm uses a baby
-- step\/giant step strategy for the distinct-degree factorization step. If
-- @flint_get_num_threads@ is greater than one
-- @fmpz_mod_poly_factor_distinct_deg_threaded@ is used.
foreign import ccall "fmpz_mod_poly_factor.h fmpz_mod_poly_factor_kaltofen_shoup"
  fmpz_mod_poly_factor_kaltofen_shoup :: Ptr CFmpzModPolyFactor -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_factor_berlekamp/ /factors/ /f/ /ctx/ 
--
-- Factorises a non-constant polynomial @f@ into monic irreducible factors
-- using the Berlekamp algorithm.
foreign import ccall "fmpz_mod_poly_factor.h fmpz_mod_poly_factor_berlekamp"
  fmpz_mod_poly_factor_berlekamp :: Ptr CFmpzModPolyFactor -> Ptr CFmpzModPoly -> Ptr CFmpzModCtx -> IO ()

-- -- | /_fmpz_mod_poly_interval_poly_worker/ /arg_ptr/ 
-- --
-- -- Worker function to compute interval polynomials in distinct degree
-- -- factorisation. Input\/output is stored in
-- -- @fmpz_mod_poly_interval_poly_arg_t@.
-- foreign import ccall "fmpz_mod_poly_factor.h _fmpz_mod_poly_interval_poly_worker"
--   _fmpz_mod_poly_interval_poly_worker :: Ptr  -> IO ()

-- Root Finding ----------------------------------------------------------------

-- | /fmpz_mod_poly_roots/ /r/ /f/ /with_multiplicity/ /ctx/ 
--
-- Fill \(r\) with factors of the form \(x - r_i\) where the \(r_i\) are
-- the distinct roots of a nonzero \(f\) in \(Z/pZ\). It is expected and
-- not checked that the modulus of \(ctx\) is prime. If
-- \(with\_multiplicity\) is zero, the exponent \(e_i\) of the factor
-- \(x - r_i\) is \(1\). Otherwise, it is the largest \(e_i\) such that
-- \((x-r_i)^e_i\) divides \(f\). This function throws if \(f\) is zero,
-- but is otherwise always successful.
foreign import ccall "fmpz_mod_poly_factor.h fmpz_mod_poly_roots"
  fmpz_mod_poly_roots :: Ptr CFmpzModPolyFactor -> Ptr CFmpzModPoly -> CInt -> Ptr CFmpzModCtx -> IO ()

-- | /fmpz_mod_poly_roots_factored/ /r/ /f/ /with_multiplicity/ /n/ /ctx/ 
--
-- Fill \(r\) with factors of the form \(x - r_i\) where the \(r_i\) are
-- the distinct roots of a nonzero \(f\) in \(Z/nZ\). It is expected and
-- not checked that \(n\) is a prime factorization of the modulus of
-- \(ctx\). If \(with\_multiplicity\) is zero, the exponent \(e_i\) of the
-- factor \(x - r_i\) is \(1\). Otherwise, it is the largest \(e_i\) such
-- that \((x-r_i)^e_i\) divides \(f\). The roots are first found modulo the
-- primes in \(n\), then lifted to the corresponding prime powers, then
-- combined into roots of the original polynomial \(f\). A return of \(1\)
-- indicates the function was successful. A return of \(0\) indicates the
-- function was not able to find the roots, possibly because there are too
-- many of them. This function throws if \(f\) is zero.
foreign import ccall "fmpz_mod_poly_factor.h fmpz_mod_poly_roots_factored"
  fmpz_mod_poly_roots_factored :: Ptr CFmpzModPolyFactor -> Ptr CFmpzModPoly -> CInt -> Ptr CFmpzFactor -> Ptr CFmpzModCtx -> IO CInt

