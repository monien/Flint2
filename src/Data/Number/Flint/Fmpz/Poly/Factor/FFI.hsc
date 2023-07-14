module Data.Number.Flint.Fmpz.Poly.Factor.FFI (
  -- * Factorisation of polynomials over the integers
    FmpzPolyFactor (..)
  , CFmpzPolyFactor (..)
  , newFmpzPolyFactor
  , withFmpzPolyFactor
  -- * Types, macros and constants
  -- * Memory management
  , fmpz_poly_factor_init
  , fmpz_poly_factor_init2
  , fmpz_poly_factor_realloc
  , fmpz_poly_factor_fit_length
  , fmpz_poly_factor_clear
  -- * Manipulating factors
  , fmpz_poly_factor_set
  , fmpz_poly_factor_insert
  , fmpz_poly_factor_concat
  -- * Input and output
  , fmpz_poly_factor_print
  -- * Factoring algorithms
  , fmpz_poly_factor_squarefree
  , fmpz_poly_factor_zassenhaus_recombination
  , _fmpz_poly_factor_zassenhaus
  , fmpz_poly_factor_zassenhaus
  , _fmpz_poly_factor_quadratic
  , fmpz_poly_factor
) where 

-- factorisation of polynomials over the integers ------------------------------

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr )
import Foreign.Storable
import Foreign.Marshal ( free )

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Poly

#include <flint/flint.h>

#include <flint/fmpz.h>
#include <flint/fmpz_poly.h>
#include <flint/fmpz_poly_factor.h>

-- fmpz_poly_factor_t
----------------------------------------------------------
data FmpzPolyFactor =
  FmpzPolyFactor {-# UNPACK #-} !(ForeignPtr CFmpzPolyFactor)
data CFmpzPolyFactor = CFmpzPolyFactor CLong (Ptr CFmpzPoly) (Ptr CLong) CLong CLong 

instance Storable CFmpzPolyFactor where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fmpz_poly_factor_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fmpz_poly_factor_t}
  peek ptr = do
    c     <- #{peek fmpz_poly_factor_struct, c    } ptr
    p     <- #{peek fmpz_poly_factor_struct, p    } ptr
    exp   <- #{peek fmpz_poly_factor_struct, exp  } ptr
    num   <- #{peek fmpz_poly_factor_struct, num  } ptr
    alloc <- #{peek fmpz_poly_factor_struct, alloc} ptr
    return $ CFmpzPolyFactor c p exp num alloc
  poke = error "CFmpzPolyFactor.poke: Not defined"

newFmpzPolyFactor = do
  p <- mallocForeignPtr
  withForeignPtr p fmpz_poly_factor_init
  addForeignPtrFinalizer p_fmpz_poly_factor_clear p
  return $ FmpzPolyFactor p

{-# INLINE withFmpzPolyFactor #-}
withFmpzPolyFactor (FmpzPolyFactor p) f = do
  withForeignPtr p $ \fp -> f fp >>= return . (FmpzPolyFactor p,)

withNewFmpzPolyFactor f = do
  x <- newFmpzPolyFactor
  withFmpzPolyFactor x $ \x -> f x
  
-- Memory management -----------------------------------------------------------

-- | /fmpz_poly_factor_init/ /fac/ 
-- 
-- Initialises a new factor structure.
foreign import ccall "fmpz_poly_factor.h fmpz_poly_factor_init"
  fmpz_poly_factor_init :: Ptr CFmpzPolyFactor -> IO ()

-- | /fmpz_poly_factor_init2/ /fac/ /alloc/ 
-- 
-- Initialises a new factor structure, providing space for at least @alloc@
-- factors.
foreign import ccall "fmpz_poly_factor.h fmpz_poly_factor_init2"
  fmpz_poly_factor_init2 :: Ptr CFmpzPolyFactor -> CLong -> IO ()

-- | /fmpz_poly_factor_realloc/ /fac/ /alloc/ 
-- 
-- Reallocates the factor structure to provide space for precisely @alloc@
-- factors.
foreign import ccall "fmpz_poly_factor.h fmpz_poly_factor_realloc"
  fmpz_poly_factor_realloc :: Ptr CFmpzPolyFactor -> CLong -> IO ()

-- | /fmpz_poly_factor_fit_length/ /fac/ /len/ 
-- 
-- Ensures that the factor structure has space for at least @len@ factors.
-- This functions takes care of the case of repeated calls by always at
-- least doubling the number of factors the structure can hold.
foreign import ccall "fmpz_poly_factor.h fmpz_poly_factor_fit_length"
  fmpz_poly_factor_fit_length :: Ptr CFmpzPolyFactor -> CLong -> IO ()

-- | /fmpz_poly_factor_clear/ /fac/ 
-- 
-- Releases all memory occupied by the factor structure.
foreign import ccall "fmpz_poly_factor.h fmpz_poly_factor_clear"
  fmpz_poly_factor_clear :: Ptr CFmpzPolyFactor -> IO ()

foreign import ccall "fmpz_poly_factor.h &fmpz_poly_factor_clear"
  p_fmpz_poly_factor_clear :: FunPtr (Ptr CFmpzPolyFactor -> IO ())

-- Manipulating factors --------------------------------------------------------

-- | /fmpz_poly_factor_set/ /res/ /fac/ 
-- 
-- Sets @res@ to the same factorisation as @fac@.
foreign import ccall "fmpz_poly_factor.h fmpz_poly_factor_set"
  fmpz_poly_factor_set :: Ptr CFmpzPolyFactor -> Ptr CFmpzPolyFactor -> IO ()

-- | /fmpz_poly_factor_insert/ /fac/ /p/ /e/ 
-- 
-- Adds the primitive polynomial \(p^e\) to the factorisation @fac@.
-- 
-- Assumes that \(\deg(p) \geq 2\) and \(e \neq 0\).
foreign import ccall "fmpz_poly_factor.h fmpz_poly_factor_insert"
  fmpz_poly_factor_insert :: Ptr CFmpzPolyFactor -> Ptr CFmpzPoly -> CLong -> IO ()

-- | /fmpz_poly_factor_concat/ /res/ /fac/ 
-- 
-- Concatenates two factorisations.
-- 
-- This is equivalent to calling @fmpz_poly_factor_insert@ repeatedly with
-- the individual factors of @fac@.
-- 
-- Does not support aliasing between @res@ and @fac@.
foreign import ccall "fmpz_poly_factor.h fmpz_poly_factor_concat"
  fmpz_poly_factor_concat :: Ptr CFmpzPolyFactor -> Ptr CFmpzPolyFactor -> IO ()

-- Input and output ------------------------------------------------------------

-- | /fmpz_poly_factor_print/ /fac/ 
-- 
-- Prints the entries of @fac@ to standard output.
foreign import ccall "fmpz_poly_factor.h fmpz_poly_factor_print"
  fmpz_poly_factor_print :: Ptr CFmpzPolyFactor -> IO ()

-- Factoring algorithms --------------------------------------------------------

-- | /fmpz_poly_factor_squarefree/ /fac/ /F/ 
-- 
-- Takes as input a polynomial \(F\) and a freshly initialized factor
-- structure @fac@. Updates @fac@ to contain a factorization of \(F\) into
-- (not necessarily irreducible) factors that themselves have no repeated
-- factors. None of the returned factors will have the same exponent. That
-- is we return \(g_i\) and unique \(e_i\) such that
-- 
-- \[F = c \prod_{i} g_i^{e_i}\]
-- 
-- where \(c\) is the signed content of \(F\) and \(\gcd(g_i, g_i') = 1\).
foreign import ccall "fmpz_poly_factor.h fmpz_poly_factor_squarefree"
  fmpz_poly_factor_squarefree :: Ptr CFmpzPolyFactor -> Ptr CFmpzPoly -> IO ()

-- | /fmpz_poly_factor_zassenhaus_recombination/ /final_fac/ /lifted_fac/ /F/ /P/ /exp/ 
-- 
-- Takes as input a factor structure @lifted_fac@ containing a squarefree
-- factorization of the polynomial \(F \bmod p\). The algorithm does a
-- brute force search for irreducible factors of \(F\) over the integers,
-- and each factor is raised to the power @exp@.
-- 
-- The impact of the algorithm is to augment a factorization of @F^exp@ to
-- the factor structure @final_fac@.
foreign import ccall "fmpz_poly_factor.h fmpz_poly_factor_zassenhaus_recombination"
  fmpz_poly_factor_zassenhaus_recombination :: Ptr CFmpzPolyFactor -> Ptr CFmpzPolyFactor -> Ptr CFmpzPoly -> Ptr CFmpz -> CLong -> IO ()

-- | /_fmpz_poly_factor_zassenhaus/ /final_fac/ /exp/ /f/ /cutoff/ /use_van_hoeij/ 
-- 
-- This is the internal wrapper of Zassenhaus.
-- 
-- It will attempt to find a small prime such that \(f\) modulo \(p\) has a
-- minimal number of factors. If it cannot find a prime giving less than
-- @cutoff@ factors it aborts. Then it decides a \(p\)-adic precision to
-- lift the factors to, hensel lifts, and finally calls Zassenhaus
-- recombination.
-- 
-- Assumes that \(\operatorname{len}(f) \geq 2\).
-- 
-- Assumes that \(f\) is primitive.
-- 
-- Assumes that the constant coefficient of \(f\) is non-zero. Note that
-- this can be easily achieved by taking out factors of the form \(x^k\)
-- before calling this routine.
-- 
-- If the final flag is set, the function will use the van Hoeij
-- factorisation algorithm with gradual feeding and mod \(2^k\) data
-- truncation to find factors when the number of local factors is large.
foreign import ccall "fmpz_poly_factor.h _fmpz_poly_factor_zassenhaus"
  _fmpz_poly_factor_zassenhaus :: Ptr CFmpzPolyFactor -> CLong -> Ptr CFmpzPoly -> CLong -> CInt -> IO ()

-- | /fmpz_poly_factor_zassenhaus/ /final_fac/ /F/ 
-- 
-- A wrapper of the Zassenhaus factoring algorithm, which takes as input
-- any polynomial \(F\), and stores a factorization in @final_fac@.
-- 
-- The complexity will be exponential in the number of local factors we
-- find for the components of a squarefree factorization of \(F\).
foreign import ccall "fmpz_poly_factor.h fmpz_poly_factor_zassenhaus"
  fmpz_poly_factor_zassenhaus :: Ptr CFmpzPolyFactor -> Ptr CFmpzPoly -> IO ()

-- | /_fmpz_poly_factor_quadratic/ /fac/ /f/ /exp/ 
-- 
-- Inserts the factorisation of the quadratic (resp. cubic) polynomial /f/
-- into /fac/ with multiplicity /exp/. This function requires that the
-- content of /f/ has been removed, and does not update the content of
-- /fac/. The factorzation is calculated over \(\mathbb{R}\) or
-- \(\mathbb{Q}_2\) and then tested over \(\mathbb{Z}\).
foreign import ccall "fmpz_poly_factor.h _fmpz_poly_factor_quadratic"
  _fmpz_poly_factor_quadratic :: Ptr CFmpzPolyFactor -> Ptr CFmpzPoly -> CLong -> IO ()

-- | /fmpz_poly_factor/ /final_fac/ /F/ 
-- 
-- A wrapper of the Zassenhaus and van Hoeij factoring algorithms, which
-- takes as input any polynomial \(F\), and stores a factorization in
-- @final_fac@.
foreign import ccall "fmpz_poly_factor.h fmpz_poly_factor"
  fmpz_poly_factor :: Ptr CFmpzPolyFactor -> Ptr CFmpzPoly -> IO ()

