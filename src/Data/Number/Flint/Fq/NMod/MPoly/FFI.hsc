{-|
module      :  Data.Number.Flint.Fq.NMod.MPoly.FFI
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de
-}
module Data.Number.Flint.Fq.NMod.MPoly.FFI (
  -- * Multivariate polynomials over finite fields of word-sized characteristic
    FqNModMPoly (..)
  , CFqNModMPoly (..)
  , newFqNModMPoly
  , withFqNModMPoly
  -- * Context object
  , FqNModMPolyCtx (..)
  , CFqNModMPolyCtx (..)
  , newFqNModMPolyCtx
  , withFqNModMPolyCtx
  -- *
  , fq_nmod_mpoly_ctx_init
  , fq_nmod_mpoly_ctx_nvars
  , fq_nmod_mpoly_ctx_ord
  , fq_nmod_mpoly_ctx_clear
  -- * Memory management
  , fq_nmod_mpoly_init
  , fq_nmod_mpoly_init2
  , fq_nmod_mpoly_init3
  , fq_nmod_mpoly_fit_length
  , fq_nmod_mpoly_realloc
  , fq_nmod_mpoly_clear
  -- * Input\/Output
  , fq_nmod_mpoly_get_str_pretty
  , fq_nmod_mpoly_fprint_pretty
  , fq_nmod_mpoly_print_pretty
  , fq_nmod_mpoly_set_str_pretty
  -- * Basic manipulation
  , fq_nmod_mpoly_gen
  , fq_nmod_mpoly_is_gen
  , fq_nmod_mpoly_set
  , fq_nmod_mpoly_equal
  , fq_nmod_mpoly_swap
  -- * Constants
  , fq_nmod_mpoly_is_fq_nmod
  , fq_nmod_mpoly_get_fq_nmod
  , fq_nmod_mpoly_set_fq_nmod
  , fq_nmod_mpoly_set_ui
  , fq_nmod_mpoly_set_fq_nmod_gen
  , fq_nmod_mpoly_zero
  , fq_nmod_mpoly_one
  , fq_nmod_mpoly_equal_fq_nmod
  , fq_nmod_mpoly_is_zero
  , fq_nmod_mpoly_is_one
  -- * Degrees
  , fq_nmod_mpoly_degrees_fit_si
  , fq_nmod_mpoly_degrees_fmpz
  , fq_nmod_mpoly_degrees_si
  , fq_nmod_mpoly_degree_fmpz
  , fq_nmod_mpoly_degree_si
  , fq_nmod_mpoly_total_degree_fits_si
  , fq_nmod_mpoly_total_degree_fmpz
  , fq_nmod_mpoly_total_degree_si
  , fq_nmod_mpoly_used_vars
  -- * Coefficients
  , fq_nmod_mpoly_get_coeff_fq_nmod_monomial
  , fq_nmod_mpoly_set_coeff_fq_nmod_monomial
  , fq_nmod_mpoly_get_coeff_fq_nmod_fmpz
  , fq_nmod_mpoly_get_coeff_fq_nmod_ui
  , fq_nmod_mpoly_set_coeff_fq_nmod_fmpz
  , fq_nmod_mpoly_set_coeff_fq_nmod_ui
  , fq_nmod_mpoly_get_coeff_vars_ui
  -- * Comparison
  , fq_nmod_mpoly_cmp
  -- * Container operations
  , fq_nmod_mpoly_is_canonical
  , fq_nmod_mpoly_length
  , fq_nmod_mpoly_resize
  , fq_nmod_mpoly_get_term_coeff_fq_nmod
  --, fq_nmod_mpoly_set_term_coeff_ui
  , fq_nmod_mpoly_term_exp_fits_si
  , fq_nmod_mpoly_term_exp_fits_ui
  , fq_nmod_mpoly_get_term_exp_fmpz
  , fq_nmod_mpoly_get_term_exp_ui
  , fq_nmod_mpoly_get_term_exp_si
  , fq_nmod_mpoly_get_term_var_exp_ui
  , fq_nmod_mpoly_get_term_var_exp_si
  , fq_nmod_mpoly_set_term_exp_fmpz
  , fq_nmod_mpoly_set_term_exp_ui
  , fq_nmod_mpoly_get_term
  , fq_nmod_mpoly_get_term_monomial
  , fq_nmod_mpoly_push_term_fq_nmod_fmpz
  , fq_nmod_mpoly_push_term_fq_nmod_ui
  , fq_nmod_mpoly_sort_terms
  , fq_nmod_mpoly_combine_like_terms
  , fq_nmod_mpoly_reverse
  -- * Random generation
  , fq_nmod_mpoly_randtest_bound
  , fq_nmod_mpoly_randtest_bounds
  , fq_nmod_mpoly_randtest_bits
  -- * Addition\/Subtraction
  , fq_nmod_mpoly_add_fq_nmod
  , fq_nmod_mpoly_sub_fq_nmod
  , fq_nmod_mpoly_add
  , fq_nmod_mpoly_sub
  -- * Scalar operations
  , fq_nmod_mpoly_neg
  , fq_nmod_mpoly_scalar_mul_fq_nmod
  , fq_nmod_mpoly_make_monic
  -- * Differentiation
  , fq_nmod_mpoly_derivative
  -- * Evaluation
  , fq_nmod_mpoly_evaluate_all_fq_nmod
  , fq_nmod_mpoly_evaluate_one_fq_nmod
  , fq_nmod_mpoly_compose_fq_nmod_poly
  , fq_nmod_mpoly_compose_fq_nmod_mpoly
  , fq_nmod_mpoly_compose_fq_nmod_mpoly_gen
  -- * Multiplication
  , fq_nmod_mpoly_mul
  -- * Powering
  , fq_nmod_mpoly_pow_fmpz
  , fq_nmod_mpoly_pow_ui
  -- * Division
  , fq_nmod_mpoly_divides
  , fq_nmod_mpoly_div
  , fq_nmod_mpoly_divrem
  , fq_nmod_mpoly_divrem_ideal
  -- * Greatest Common Divisor
  , fq_nmod_mpoly_term_content
  , fq_nmod_mpoly_content_vars
  , fq_nmod_mpoly_gcd
  , fq_nmod_mpoly_gcd_cofactors
  , fq_nmod_mpoly_gcd_brown
  , fq_nmod_mpoly_gcd_hensel
  , fq_nmod_mpoly_gcd_zippel
  , fq_nmod_mpoly_resultant
  , fq_nmod_mpoly_discriminant
  -- * Square Root
  , fq_nmod_mpoly_sqrt
  , fq_nmod_mpoly_is_square
  , fq_nmod_mpoly_quadratic_root
  -- * Univariate Functions
  , fq_nmod_mpoly_univar_init
  , fq_nmod_mpoly_univar_clear
  , fq_nmod_mpoly_univar_swap
  , fq_nmod_mpoly_to_univar
  , fq_nmod_mpoly_from_univar
  , fq_nmod_mpoly_univar_degree_fits_si
  , fq_nmod_mpoly_univar_length
  , fq_nmod_mpoly_univar_get_term_exp_si
  , fq_nmod_mpoly_univar_get_term_coeff
  , fq_nmod_mpoly_univar_swap_term_coeff
) where

-- Multivariate polynomials over finite fields of word-size characteristic -----

import Foreign.C.String
import Foreign.C.Types
import qualified Foreign.Concurrent
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr )
import Foreign.Storable
import Foreign.Marshal ( free )

import Data.Number.Flint.Flint
import Data.Number.Flint.MPoly
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Mod.Poly
import Data.Number.Flint.NMod.Poly
import Data.Number.Flint.NMod.MPoly
import Data.Number.Flint.Fq
import Data.Number.Flint.Fq.Poly
import Data.Number.Flint.Fq.NMod
import Data.Number.Flint.Fq.NMod.Types

#include <flint/flint.h>
#include <flint/fq.h>
#include <flint/fq_nmod.h>
#include <flint/fq_nmod_poly.h>
#include <flint/fq_nmod_mpoly.h>

-- fq_nmod_mpoly_t -------------------------------------------------------------

instance Storable CFqNModMPoly where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fq_nmod_mpoly_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fq_nmod_mpoly_t}
  peek = undefined
  poke = undefined

newFqNModMPoly ctx@(FqNModMPolyCtx ftx) = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> do
    withFqNModMPolyCtx ctx $ \ctx -> do
      fq_nmod_mpoly_init x ctx
    addForeignPtrFinalizerEnv p_fq_nmod_mpoly_clear x ftx
  return $ FqNModMPoly x

{-# INLINE withFqNModMPoly #-}
withFqNModMPoly (FqNModMPoly x) f = do
  withForeignPtr x $ \px -> f px >>= return . (FqNModMPoly x,)

-- fq_nmod_mpoly_univar_t ------------------------------------------------------

data FqNModMPolyUnivar = FqNModMPolyUnivar {-# UNPACK #-} !(ForeignPtr CFqNModMPolyUnivar)
data CFqNModMPolyUnivar = CFqNModMPolyUnivar 

instance Storable CFqNModMPolyUnivar where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fq_nmod_mpoly_univar_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fq_nmod_mpoly_univar_t}
  peek = error "CFqNModMPolyUnivar.peek: Not defined"
  poke = error "CFqNModMPolyUnivar.poke: Not defined"

-- | Create a new `FqNModMPolyUnivar`
newFqNModMPolyUnivar ctx@(FqNModMPolyCtx pctx) = do
  p <- mallocForeignPtr
  withForeignPtr p $ \p ->
    withFqNModMPolyCtx ctx $ \ctx -> do 
      fq_nmod_mpoly_univar_init p ctx
      addForeignPtrFinalizerEnv p_fq_nmod_mpoly_univar_clear p pctx
  return $ FqNModMPolyUnivar p

{-# INLINE withFqNModMPolyUnivar #-}
withFqNModMPolyUnivar (FqNModMPolyUnivar p) f = do
  withForeignPtr p $ \fp -> (FqNModMPolyUnivar p,) <$> f fp
  
-- fq_nmod_mpoly_ctx_t ---------------------------------------------------------


data FqNModMPolyCtx = FqNModMPolyCtx {-# UNPACK #-} !(ForeignPtr CFqNModMPolyCtx)
data CFqNModMPolyCtx

instance Storable CFqNModMPolyCtx where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fq_nmod_mpoly_ctx_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fq_nmod_mpoly_ctx_t}
  peek = error "CFqNModMPolyCtx.peek: Not defined"
  poke = error "CFqNModMPolyCtx.poke: Not defined"

-- | Create a new `FqNModMPolyCtx`
newFqNModMPolyCtx nvars ord fqctx = do
  p <- mallocForeignPtr
  withForeignPtr p $ \p ->
    withFqNModCtx fqctx $ \fqctx -> do
      fq_nmod_mpoly_ctx_init p nvars ord fqctx
  addForeignPtrFinalizer p_fq_nmod_mpoly_ctx_clear p
  return $ FqNModMPolyCtx p

-- | Use a `FqNModMPolyCtx`
{-# INLINE withFqNModMPolyCtx #-}
withFqNModMPolyCtx (FqNModMPolyCtx p) f = do
  withForeignPtr p $ \fp -> f fp >>= return . (FqNModMPolyCtx p,)

-- Context object --------------------------------------------------------------

-- | /fq_nmod_mpoly_ctx_init/ /ctx/ /nvars/ /ord/ /fqctx/ 
--
-- Initialise a context object for a polynomial ring with the given number
-- of variables and the given ordering. It will have coefficients in the
-- finite field /fqctx/. The possibilities for the ordering are @ORD_LEX@,
-- @ORD_DEGLEX@ and @ORD_DEGREVLEX@.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_ctx_init"
  fq_nmod_mpoly_ctx_init :: Ptr CFqNModMPolyCtx -> CLong -> Ptr COrdering -> Ptr CFqNModCtx -> IO ()

-- | /fq_nmod_mpoly_ctx_nvars/ /ctx/ 
--
-- Return the number of variables used to initialize the context.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_ctx_nvars"
  fq_nmod_mpoly_ctx_nvars :: Ptr CFqNModMPolyCtx -> IO CLong

-- | /fq_nmod_mpoly_ctx_ord/ /ctx/ 
--
-- Return the ordering used to initialize the context.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_ctx_ord"
  fq_nmod_mpoly_ctx_ord :: Ptr CFqNModMPolyCtx -> IO (Ptr COrdering)

-- | /fq_nmod_mpoly_ctx_clear/ /ctx/ 
--
-- Release any space allocated by an /ctx/.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_ctx_clear"
  fq_nmod_mpoly_ctx_clear :: Ptr CFqNModMPolyCtx -> IO ()

foreign import ccall "fq_nmod_mpoly.h &fq_nmod_mpoly_ctx_clear"
  p_fq_nmod_mpoly_ctx_clear :: FunPtr (Ptr CFqNModMPolyCtx -> IO ())

-- Memory management -----------------------------------------------------------

-- | /fq_nmod_mpoly_init/ /A/ /ctx/ 
--
-- Initialise /A/ for use with the given an initialised context object. Its
-- value is set to zero.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_init"
  fq_nmod_mpoly_init :: Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_init2/ /A/ /alloc/ /ctx/ 
--
-- Initialise /A/ for use with the given an initialised context object. Its
-- value is set to zero. It is allocated with space for /alloc/ terms and
-- at least @MPOLY_MIN_BITS@ bits for the exponents.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_init2"
  fq_nmod_mpoly_init2 :: Ptr CFqNModMPoly -> CLong -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_init3/ /A/ /alloc/ /bits/ /ctx/ 
--
-- Initialise /A/ for use with the given an initialised context object. Its
-- value is set to zero. It is allocated with space for /alloc/ terms and
-- /bits/ bits for the exponents.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_init3"
  fq_nmod_mpoly_init3 :: Ptr CFqNModMPoly -> CLong -> CFBitCnt -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_fit_length/ /A/ /len/ /ctx/ 
--
-- Ensure that /A/ has space for at least /len/ terms.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_fit_length"
  fq_nmod_mpoly_fit_length :: Ptr CFqNModMPoly -> CLong -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_realloc/ /A/ /alloc/ /ctx/ 
--
-- Reallocate /A/ to have space for /alloc/ terms. Assumes the current
-- length of the polynomial is not greater than /alloc/.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_realloc"
  fq_nmod_mpoly_realloc :: Ptr CFqNModMPoly -> CLong -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_clear/ /A/ /ctx/ 
--
-- Release any space allocated for /A/.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_clear"
  fq_nmod_mpoly_clear :: Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO ()

foreign import ccall "fq_nmod_mpoly.h &fq_nmod_mpoly_clear"
  p_fq_nmod_mpoly_clear :: FunPtr (Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO ())

-- Input\/Output ---------------------------------------------------------------

-- | /fq_nmod_mpoly_get_str_pretty/ /A/ /x/ /ctx/ 
--
-- Return a string, which the user is responsible for cleaning up,
-- representing /A/, given an array of variable strings /x/.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_get_str_pretty"
  fq_nmod_mpoly_get_str_pretty :: Ptr CFqNModMPoly -> Ptr CString -> Ptr CFqNModMPolyCtx -> IO CString

-- | /fq_nmod_mpoly_fprint_pretty/ /file/ /A/ /x/ /ctx/ 
--
-- Print a string representing /A/ to /file/.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_fprint_pretty"
  fq_nmod_mpoly_fprint_pretty :: Ptr CFile -> Ptr CFqNModMPoly -> Ptr CString -> Ptr CFqNModMPolyCtx -> IO CInt

-- | /fq_nmod_mpoly_print_pretty/ /A/ /x/ /ctx/ 
--
-- Print a string representing /A/ to @stdout@.
fq_nmod_mpoly_print_pretty :: Ptr CFqNModMPoly -> Ptr CString -> Ptr CFqNModMPolyCtx -> IO CInt
fq_nmod_mpoly_print_pretty a x ctx =
  printCStr (\a -> fq_nmod_mpoly_get_str_pretty a x ctx) a

-- | /fq_nmod_mpoly_set_str_pretty/ /A/ /str/ /x/ /ctx/ 
--
-- Set /A/ to the polynomial in the null-terminates string /str/ given an
-- array /x/ of variable strings. If parsing /str/ fails, /A/ is set to
-- zero, and \(-1\) is returned. Otherwise, \(0\) is returned. The
-- operations @+@, @-@, @*@, and @\/@ are permitted along with integers and
-- the variables in /x/. The character @^@ must be immediately followed by
-- the (integer) exponent. If any division is not exact, parsing fails.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_set_str_pretty"
  fq_nmod_mpoly_set_str_pretty :: Ptr CFqNModMPoly -> CString -> Ptr CString -> Ptr CFqNModMPolyCtx -> IO CInt

-- Basic manipulation ----------------------------------------------------------

-- | /fq_nmod_mpoly_gen/ /A/ /var/ /ctx/ 
--
-- Set /A/ to the variable of index /var/, where \(var = 0\) corresponds to
-- the variable with the most significance with respect to the ordering.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_gen"
  fq_nmod_mpoly_gen :: Ptr CFqNModMPoly -> CLong -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_is_gen/ /A/ /var/ /ctx/ 
--
-- If \(var \ge 0\), return \(1\) if /A/ is equal to the \(var\)-th
-- generator, otherwise return \(0\). If \(var < 0\), return \(1\) if the
-- polynomial is equal to any generator, otherwise return \(0\).
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_is_gen"
  fq_nmod_mpoly_is_gen :: Ptr CFqNModMPoly -> CLong -> Ptr CFqNModMPolyCtx -> IO CInt

-- | /fq_nmod_mpoly_set/ /A/ /B/ /ctx/ 
--
-- Set /A/ to /B/.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_set"
  fq_nmod_mpoly_set :: Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_equal/ /A/ /B/ /ctx/ 
--
-- Return \(1\) if /A/ is equal to /B/, else return \(0\).
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_equal"
  fq_nmod_mpoly_equal :: Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO CInt

-- | /fq_nmod_mpoly_swap/ /A/ /B/ /ctx/ 
--
-- Efficiently swap /A/ and /B/.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_swap"
  fq_nmod_mpoly_swap :: Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO ()

-- Constants -------------------------------------------------------------------

-- | /fq_nmod_mpoly_is_fq_nmod/ /A/ /ctx/ 
--
-- Return \(1\) if /A/ is a constant, else return \(0\).
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_is_fq_nmod"
  fq_nmod_mpoly_is_fq_nmod :: Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO CInt

-- | /fq_nmod_mpoly_get_fq_nmod/ /c/ /A/ /ctx/ 
--
-- Assuming that /A/ is a constant, set /c/ to this constant. This function
-- throws if /A/ is not a constant.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_get_fq_nmod"
  fq_nmod_mpoly_get_fq_nmod :: Ptr CFqNMod -> Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_set_fq_nmod/ /A/ /c/ /ctx/ 
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_set_fq_nmod"
  fq_nmod_mpoly_set_fq_nmod :: Ptr CFqNModMPoly -> Ptr CFqNMod -> Ptr CFqNModMPolyCtx -> IO ()
-- | /fq_nmod_mpoly_set_ui/ /A/ /c/ /ctx/ 
--
-- Set /A/ to the constant /c/.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_set_ui"
  fq_nmod_mpoly_set_ui :: Ptr CFqNModMPoly -> CULong -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_set_fq_nmod_gen/ /A/ /ctx/ 
--
-- Set /A/ to the constant given by @fq_nmod_gen@.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_set_fq_nmod_gen"
  fq_nmod_mpoly_set_fq_nmod_gen :: Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_zero/ /A/ /ctx/ 
--
-- Set /A/ to the constant \(0\).
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_zero"
  fq_nmod_mpoly_zero :: Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_one/ /A/ /ctx/ 
--
-- Set /A/ to the constant \(1\).
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_one"
  fq_nmod_mpoly_one :: Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_equal_fq_nmod/ /A/ /c/ /ctx/ 
--
-- Return \(1\) if /A/ is equal to the constant /c/, else return \(0\).
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_equal_fq_nmod"
  fq_nmod_mpoly_equal_fq_nmod :: Ptr CFqNModMPoly -> Ptr CFqNMod -> Ptr CFqNModMPolyCtx -> IO CInt

-- | /fq_nmod_mpoly_is_zero/ /A/ /ctx/ 
--
-- Return \(1\) if /A/ is the constant \(0\), else return \(0\).
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_is_zero"
  fq_nmod_mpoly_is_zero :: Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO CInt

-- | /fq_nmod_mpoly_is_one/ /A/ /ctx/ 
--
-- Return \(1\) if /A/ is the constant \(1\), else return \(0\).
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_is_one"
  fq_nmod_mpoly_is_one :: Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO CInt

-- Degrees ---------------------------------------------------------------------

-- | /fq_nmod_mpoly_degrees_fit_si/ /A/ /ctx/ 
--
-- Return \(1\) if the degrees of /A/ with respect to each variable fit
-- into an @slong@, otherwise return \(0\).
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_degrees_fit_si"
  fq_nmod_mpoly_degrees_fit_si :: Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO CInt

-- | /fq_nmod_mpoly_degrees_fmpz/ /degs/ /A/ /ctx/ 
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_degrees_fmpz"
  fq_nmod_mpoly_degrees_fmpz :: Ptr (Ptr CFmpz) -> Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO ()
-- | /fq_nmod_mpoly_degrees_si/ /degs/ /A/ /ctx/ 
--
-- Set /degs/ to the degrees of /A/ with respect to each variable. If /A/
-- is zero, all degrees are set to \(-1\).
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_degrees_si"
  fq_nmod_mpoly_degrees_si :: Ptr CLong -> Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_degree_fmpz/ /deg/ /A/ /var/ /ctx/ 
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_degree_fmpz"
  fq_nmod_mpoly_degree_fmpz :: Ptr CFmpz -> Ptr CFqNModMPoly -> CLong -> Ptr CFqNModMPolyCtx -> IO ()
-- | /fq_nmod_mpoly_degree_si/ /A/ /var/ /ctx/ 
--
-- Either return or set /deg/ to the degree of /A/ with respect to the
-- variable of index /var/. If /A/ is zero, the degree is defined to be
-- \(-1\).
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_degree_si"
  fq_nmod_mpoly_degree_si :: Ptr CFqNModMPoly -> CLong -> Ptr CFqNModMPolyCtx -> IO CLong

-- | /fq_nmod_mpoly_total_degree_fits_si/ /A/ /ctx/ 
--
-- Return \(1\) if the total degree of /A/ fits into an @slong@, otherwise
-- return \(0\).
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_total_degree_fits_si"
  fq_nmod_mpoly_total_degree_fits_si :: Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO CInt

-- | /fq_nmod_mpoly_total_degree_fmpz/ /tdeg/ /A/ /ctx/ 
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_total_degree_fmpz"
  fq_nmod_mpoly_total_degree_fmpz :: Ptr CFmpz -> Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO ()
-- | /fq_nmod_mpoly_total_degree_si/ /A/ /ctx/ 
--
-- Either return or set /tdeg/ to the total degree of /A/. If /A/ is zero,
-- the total degree is defined to be \(-1\).
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_total_degree_si"
  fq_nmod_mpoly_total_degree_si :: Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO CLong

-- | /fq_nmod_mpoly_used_vars/ /used/ /A/ /ctx/ 
--
-- For each variable index \(i\), set @used[i]@ to nonzero if the variable
-- of index \(i\) appears in /A/ and to zero otherwise.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_used_vars"
  fq_nmod_mpoly_used_vars :: Ptr CInt -> Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO ()

-- Coefficients ----------------------------------------------------------------

-- | /fq_nmod_mpoly_get_coeff_fq_nmod_monomial/ /c/ /A/ /M/ /ctx/ 
--
-- Assuming that /M/ is a monomial, set /c/ to the coefficient of the
-- corresponding monomial in /A/. This function throws if /M/ is not a
-- monomial.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_get_coeff_fq_nmod_monomial"
  fq_nmod_mpoly_get_coeff_fq_nmod_monomial :: Ptr CFqNMod -> Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_set_coeff_fq_nmod_monomial/ /A/ /c/ /M/ /ctx/ 
--
-- Assuming that /M/ is a monomial, set the coefficient of the
-- corresponding monomial in /A/ to /c/. This function throws if /M/ is not
-- a monomial.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_set_coeff_fq_nmod_monomial"
  fq_nmod_mpoly_set_coeff_fq_nmod_monomial :: Ptr CFqNModMPoly -> Ptr CFqNMod -> Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_get_coeff_fq_nmod_fmpz/ /c/ /A/ /exp/ /ctx/ 
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_get_coeff_fq_nmod_fmpz"
  fq_nmod_mpoly_get_coeff_fq_nmod_fmpz :: Ptr CFqNMod -> Ptr CFqNModMPoly -> Ptr (Ptr CFmpz) -> Ptr CFqNModMPolyCtx -> IO ()
-- | /fq_nmod_mpoly_get_coeff_fq_nmod_ui/ /c/ /A/ /exp/ /ctx/ 
--
-- Set /c/ to the coefficient of the monomial with exponent vector /exp/.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_get_coeff_fq_nmod_ui"
  fq_nmod_mpoly_get_coeff_fq_nmod_ui :: Ptr CFqNMod -> Ptr CFqNModMPoly -> Ptr CULong -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_set_coeff_fq_nmod_fmpz/ /A/ /c/ /exp/ /ctx/ 
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_set_coeff_fq_nmod_fmpz"
  fq_nmod_mpoly_set_coeff_fq_nmod_fmpz :: Ptr CFqNModMPoly -> Ptr CFqNMod -> Ptr (Ptr CFmpz) -> Ptr CFqNModMPolyCtx -> IO ()
-- | /fq_nmod_mpoly_set_coeff_fq_nmod_ui/ /A/ /c/ /exp/ /ctx/ 
--
-- Set the coefficient of the monomial with exponent /exp/ to /c/.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_set_coeff_fq_nmod_ui"
  fq_nmod_mpoly_set_coeff_fq_nmod_ui :: Ptr CFqNModMPoly -> Ptr CFqNMod -> Ptr CULong -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_get_coeff_vars_ui/ /C/ /A/ /vars/ /exps/ /length/ /ctx/ 
--
-- Set /C/ to the coefficient of /A/ with respect to the variables in
-- /vars/ with powers in the corresponding array /exps/. Both /vars/ and
-- /exps/ point to array of length /length/. It is assumed that
-- \(0 < length \le nvars(A)\) and that the variables in /vars/ are
-- distinct.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_get_coeff_vars_ui"
  fq_nmod_mpoly_get_coeff_vars_ui :: Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CLong -> Ptr CULong -> CLong -> Ptr CFqNModMPolyCtx -> IO ()

-- Comparison ------------------------------------------------------------------

-- | /fq_nmod_mpoly_cmp/ /A/ /B/ /ctx/ 
--
-- Return \(1\) (resp. \(-1\), or \(0\)) if /A/ is after (resp. before,
-- same as) /B/ in some arbitrary but fixed total ordering of the
-- polynomials. This ordering agrees with the usual ordering of monomials
-- when /A/ and /B/ are both monomials.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_cmp"
  fq_nmod_mpoly_cmp :: Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO CInt

-- Container operations --------------------------------------------------------

-- | /fq_nmod_mpoly_is_canonical/ /A/ /ctx/ 
--
-- Return \(1\) if /A/ is in canonical form. Otherwise, return \(0\). To be
-- in canonical form, all of the terms must have nonzero coefficients, and
-- the terms must be sorted from greatest to least.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_is_canonical"
  fq_nmod_mpoly_is_canonical :: Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO CInt

-- | /fq_nmod_mpoly_length/ /A/ /ctx/ 
--
-- Return the number of terms in /A/. If the polynomial is in canonical
-- form, this will be the number of nonzero coefficients.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_length"
  fq_nmod_mpoly_length :: Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO CLong

-- | /fq_nmod_mpoly_resize/ /A/ /new_length/ /ctx/ 
--
-- Set the length of /A/ to @new_length@. Terms are either deleted from the
-- end, or new zero terms are appended.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_resize"
  fq_nmod_mpoly_resize :: Ptr CFqNModMPoly -> CLong -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_get_term_coeff_fq_nmod/ /c/ /A/ /i/ /ctx/ 
--
-- Set /c/ to the coefficient of the term of index /i/.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_get_term_coeff_fq_nmod"
  fq_nmod_mpoly_get_term_coeff_fq_nmod :: Ptr CFqNMod -> Ptr CFqNModMPoly -> CLong -> Ptr CFqNModMPolyCtx -> IO ()

-- -- | /fq_nmod_mpoly_set_term_coeff_ui/ /A/ /i/ /c/ /ctx/ 
-- --
-- -- Set the coefficient of the term of index /i/ to /c/.
-- foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_set_term_coeff_ui"
--   fq_nmod_mpoly_set_term_coeff_ui :: Ptr CFqNModMPoly -> CLong -> CULong -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_term_exp_fits_si/ /A/ /i/ /ctx/ 
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_term_exp_fits_si"
  fq_nmod_mpoly_term_exp_fits_si :: Ptr CFqNModMPoly -> CLong -> Ptr CFqNModMPolyCtx -> IO CInt
-- | /fq_nmod_mpoly_term_exp_fits_ui/ /A/ /i/ /ctx/ 
--
-- Return \(1\) if all entries of the exponent vector of the term of index
-- \(i\) fit into an @slong@ (resp. a @ulong@). Otherwise, return \(0\).
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_term_exp_fits_ui"
  fq_nmod_mpoly_term_exp_fits_ui :: Ptr CFqNModMPoly -> CLong -> Ptr CFqNModMPolyCtx -> IO CInt

-- | /fq_nmod_mpoly_get_term_exp_fmpz/ /exp/ /A/ /i/ /ctx/ 
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_get_term_exp_fmpz"
  fq_nmod_mpoly_get_term_exp_fmpz :: Ptr (Ptr CFmpz) -> Ptr CFqNModMPoly -> CLong -> Ptr CFqNModMPolyCtx -> IO ()
-- | /fq_nmod_mpoly_get_term_exp_ui/ /exp/ /A/ /i/ /ctx/ 
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_get_term_exp_ui"
  fq_nmod_mpoly_get_term_exp_ui :: Ptr CULong -> Ptr CFqNModMPoly -> CLong -> Ptr CFqNModMPolyCtx -> IO ()
-- | /fq_nmod_mpoly_get_term_exp_si/ /exp/ /A/ /i/ /ctx/ 
--
-- Set /exp/ to the exponent vector of the term of index /i/. The @_ui@
-- (resp. @_si@) version throws if any entry does not fit into a @ulong@
-- (resp. @slong@).
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_get_term_exp_si"
  fq_nmod_mpoly_get_term_exp_si :: Ptr CLong -> Ptr CFqNModMPoly -> CLong -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_get_term_var_exp_ui/ /A/ /i/ /var/ /ctx/ 
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_get_term_var_exp_ui"
  fq_nmod_mpoly_get_term_var_exp_ui :: Ptr CFqNModMPoly -> CLong -> CLong -> Ptr CFqNModMPolyCtx -> IO CULong
-- | /fq_nmod_mpoly_get_term_var_exp_si/ /A/ /i/ /var/ /ctx/ 
--
-- Return the exponent of the variable /var/ of the term of index /i/. This
-- function throws if the exponent does not fit into a @ulong@ (resp.
-- @slong@).
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_get_term_var_exp_si"
  fq_nmod_mpoly_get_term_var_exp_si :: Ptr CFqNModMPoly -> CLong -> CLong -> Ptr CFqNModMPolyCtx -> IO CLong

-- | /fq_nmod_mpoly_set_term_exp_fmpz/ /A/ /i/ /exp/ /ctx/ 
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_set_term_exp_fmpz"
  fq_nmod_mpoly_set_term_exp_fmpz :: Ptr CFqNModMPoly -> CLong -> Ptr (Ptr CFmpz) -> Ptr CFqNModMPolyCtx -> IO ()
-- | /fq_nmod_mpoly_set_term_exp_ui/ /A/ /i/ /exp/ /ctx/ 
--
-- Set the exponent of the term of index /i/ to /exp/.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_set_term_exp_ui"
  fq_nmod_mpoly_set_term_exp_ui :: Ptr CFqNModMPoly -> CLong -> Ptr CULong -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_get_term/ /M/ /A/ /i/ /ctx/ 
--
-- Set /M/ to the term of index /i/ in /A/.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_get_term"
  fq_nmod_mpoly_get_term :: Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> CLong -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_get_term_monomial/ /M/ /A/ /i/ /ctx/ 
--
-- Set /M/ to the monomial of the term of index /i/ in /A/. The coefficient
-- of /M/ will be one.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_get_term_monomial"
  fq_nmod_mpoly_get_term_monomial :: Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> CLong -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_push_term_fq_nmod_fmpz/ /A/ /c/ /exp/ /ctx/ 
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_push_term_fq_nmod_fmpz"
  fq_nmod_mpoly_push_term_fq_nmod_fmpz :: Ptr CFqNModMPoly -> Ptr CFqNMod -> Ptr (Ptr CFmpz) -> Ptr CFqNModMPolyCtx -> IO ()
-- | /fq_nmod_mpoly_push_term_fq_nmod_ui/ /A/ /c/ /exp/ /ctx/ 
--
-- Append a term to /A/ with coefficient /c/ and exponent vector /exp/.
-- This function runs in constant average time.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_push_term_fq_nmod_ui"
  fq_nmod_mpoly_push_term_fq_nmod_ui :: Ptr CFqNModMPoly -> Ptr CFqNMod -> Ptr CULong -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_sort_terms/ /A/ /ctx/ 
--
-- Sort the terms of /A/ into the canonical ordering dictated by the
-- ordering in /ctx/. This function simply reorders the terms: It does not
-- combine like terms, nor does it delete terms with coefficient zero. This
-- function runs in linear time in the bit size of /A/.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_sort_terms"
  fq_nmod_mpoly_sort_terms :: Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_combine_like_terms/ /A/ /ctx/ 
--
-- Combine adjacent like terms in /A/ and delete terms with coefficient
-- zero. If the terms of /A/ were sorted to begin with, the result will be
-- in canonical form. This function runs in linear time in the bit size of
-- /A/.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_combine_like_terms"
  fq_nmod_mpoly_combine_like_terms :: Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_reverse/ /A/ /B/ /ctx/ 
--
-- Set /A/ to the reversal of /B/.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_reverse"
  fq_nmod_mpoly_reverse :: Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO ()

-- Random generation -----------------------------------------------------------

-- | /fq_nmod_mpoly_randtest_bound/ /A/ /state/ /length/ /exp_bound/ /ctx/ 
--
-- Generate a random polynomial with length up to /length/ and exponents in
-- the range @[0, exp_bound - 1]@. The exponents of each variable are
-- generated by calls to @n_randint(state, exp_bound)@.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_randtest_bound"
  fq_nmod_mpoly_randtest_bound :: Ptr CFqNModMPoly -> Ptr CFRandState -> CLong -> CULong -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_randtest_bounds/ /A/ /state/ /length/ /exp_bounds/ /ctx/ 
--
-- Generate a random polynomial with length up to /length/ and exponents in
-- the range @[0, exp_bounds[i] - 1]@. The exponents of the variable of
-- index /i/ are generated by calls to @n_randint(state, exp_bounds[i])@.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_randtest_bounds"
  fq_nmod_mpoly_randtest_bounds :: Ptr CFqNModMPoly -> Ptr CFRandState -> CLong -> CULong -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_randtest_bits/ /A/ /state/ /length/ /exp_bits/ /ctx/ 
--
-- Generate a random polynomial with length up to /length/ and exponents
-- whose packed form does not exceed the given bit count.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_randtest_bits"
  fq_nmod_mpoly_randtest_bits :: Ptr CFqNModMPoly -> Ptr CFRandState -> CLong -> CMpLimb -> Ptr CFqNModMPolyCtx -> IO ()

-- Addition\/Subtraction -------------------------------------------------------

-- | /fq_nmod_mpoly_add_fq_nmod/ /A/ /B/ /C/ /ctx/ 
--
-- Set /A/ to \(B + c\).
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_add_fq_nmod"
  fq_nmod_mpoly_add_fq_nmod :: Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CFqNMod -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_sub_fq_nmod/ /A/ /B/ /C/ /ctx/ 
--
-- Set /A/ to \(B - c\).
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_sub_fq_nmod"
  fq_nmod_mpoly_sub_fq_nmod :: Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CFqNMod -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_add/ /A/ /B/ /C/ /ctx/ 
--
-- Set /A/ to \(B + C\).
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_add"
  fq_nmod_mpoly_add :: Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_sub/ /A/ /B/ /C/ /ctx/ 
--
-- Set /A/ to \(B - C\).
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_sub"
  fq_nmod_mpoly_sub :: Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO ()

-- Scalar operations -----------------------------------------------------------

-- | /fq_nmod_mpoly_neg/ /A/ /B/ /ctx/ 
--
-- Set /A/ to \(-B\).
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_neg"
  fq_nmod_mpoly_neg :: Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_scalar_mul_fq_nmod/ /A/ /B/ /c/ /ctx/ 
--
-- Set /A/ to \(B \times c\).
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_scalar_mul_fq_nmod"
  fq_nmod_mpoly_scalar_mul_fq_nmod :: Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CFqNMod -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_make_monic/ /A/ /B/ /ctx/ 
--
-- Set /A/ to /B/ divided by the leading coefficient of /B/. This throws if
-- /B/ is zero.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_make_monic"
  fq_nmod_mpoly_make_monic :: Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO ()

-- Differentiation -------------------------------------------------------------

-- | /fq_nmod_mpoly_derivative/ /A/ /B/ /var/ /ctx/ 
--
-- Set /A/ to the derivative of /B/ with respect to the variable of index
-- /var/.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_derivative"
  fq_nmod_mpoly_derivative :: Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> CLong -> Ptr CFqNModMPolyCtx -> IO ()

-- Evaluation ------------------------------------------------------------------

-- | /fq_nmod_mpoly_evaluate_all_fq_nmod/ /ev/ /A/ /vals/ /ctx/ 
--
-- Set /ev/ the evaluation of /A/ where the variables are replaced by the
-- corresponding elements of the array /vals/.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_evaluate_all_fq_nmod"
  fq_nmod_mpoly_evaluate_all_fq_nmod :: Ptr CFqNMod -> Ptr CFqNModMPoly -> Ptr (Ptr (Ptr CFqNMod)) -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_evaluate_one_fq_nmod/ /A/ /B/ /var/ /val/ /ctx/ 
--
-- Set /A/ to the evaluation of /B/ where the variable of index /var/ is
-- replaced by /val/.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_evaluate_one_fq_nmod"
  fq_nmod_mpoly_evaluate_one_fq_nmod :: Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> CLong -> Ptr CFqNMod -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_compose_fq_nmod_poly/ /A/ /B/ /C/ /ctx/ 
--
-- Set /A/ to the evaluation of /B/ where the variables are replaced by the
-- corresponding elements of the array /C/. The context object of /B/ is
-- /ctxB/. Return \(1\) for success and \(0\) for failure.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_compose_fq_nmod_poly"
  fq_nmod_mpoly_compose_fq_nmod_poly :: Ptr CFqNModPoly -> Ptr CFqNModMPoly -> Ptr (Ptr (Ptr CFqNModPoly)) -> Ptr CFqNModMPolyCtx -> IO CInt

-- | /fq_nmod_mpoly_compose_fq_nmod_mpoly/ /A/ /B/ /C/ /ctxB/ /ctxAC/ 
--
-- Set /A/ to the evaluation of /B/ where the variables are replaced by the
-- corresponding elements of the array /C/. Both /A/ and the elements of
-- /C/ have context object /ctxAC/, while /B/ has context object /ctxB/.
-- Neither /A/ nor /B/ is allowed to alias any other polynomial. Return
-- \(1\) for success and \(0\) for failure.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_compose_fq_nmod_mpoly"
  fq_nmod_mpoly_compose_fq_nmod_mpoly :: Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr (Ptr (Ptr CFqNModMPoly)) -> Ptr CFqNModMPolyCtx -> Ptr CFqNModMPolyCtx -> IO CInt

-- | /fq_nmod_mpoly_compose_fq_nmod_mpoly_gen/ /A/ /B/ /c/ /ctxB/ /ctxAC/ 
--
-- Set /A/ to the evaluation of /B/ where the variable of index /i/ in
-- /ctxB/ is replaced by the variable of index @c[i]@ in /ctxAC/. The
-- length of the array /C/ is the number of variables in /ctxB/. If any
-- @c[i]@ is negative, the corresponding variable of /B/ is replaced by
-- zero. Otherwise, it is expected that @c[i]@ is less than the number of
-- variables in /ctxAC/.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_compose_fq_nmod_mpoly_gen"
  fq_nmod_mpoly_compose_fq_nmod_mpoly_gen :: Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CLong -> Ptr CFqNModMPolyCtx -> Ptr CFqNModMPolyCtx -> IO ()

-- Multiplication --------------------------------------------------------------

-- | /fq_nmod_mpoly_mul/ /A/ /B/ /C/ /ctx/ 
--
-- Set /A/ to /B/ times /C/.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_mul"
  fq_nmod_mpoly_mul :: Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CNModMPoly -> Ptr CFqNModMPolyCtx -> IO ()

-- Powering --------------------------------------------------------------------

-- | /fq_nmod_mpoly_pow_fmpz/ /A/ /B/ /k/ /ctx/ 
--
-- Set /A/ to \(B\) raised to the /k/-th power. Return \(1\) for success
-- and \(0\) for failure.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_pow_fmpz"
  fq_nmod_mpoly_pow_fmpz :: Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CFmpz -> Ptr CFqNModMPolyCtx -> IO CInt

-- | /fq_nmod_mpoly_pow_ui/ /A/ /B/ /k/ /ctx/ 
--
-- Set /A/ to \(B\) raised to the /k/-th power. Return \(1\) for success
-- and \(0\) for failure.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_pow_ui"
  fq_nmod_mpoly_pow_ui :: Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> CULong -> Ptr CFqNModMPolyCtx -> IO CInt

-- Division --------------------------------------------------------------------

-- | /fq_nmod_mpoly_divides/ /Q/ /A/ /B/ /ctx/ 
--
-- If /A/ is divisible by /B/, set /Q/ to the exact quotient and return
-- \(1\). Otherwise, set /Q/ to zero and return \(0\).
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_divides"
  fq_nmod_mpoly_divides :: Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO CInt

-- | /fq_nmod_mpoly_div/ /Q/ /A/ /B/ /ctx/ 
--
-- Set /Q/ to the quotient of /A/ by /B/, discarding the remainder.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_div"
  fq_nmod_mpoly_div :: Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_divrem/ /Q/ /R/ /A/ /B/ /ctx/ 
--
-- Set /Q/ and /R/ to the quotient and remainder of /A/ divided by /B/.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_divrem"
  fq_nmod_mpoly_divrem :: Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_divrem_ideal/ /Q/ /R/ /A/ /B/ /len/ /ctx/ 
--
-- This function is as per @fq_nmod_mpoly_divrem@ except that it takes an
-- array of divisor polynomials /B/ and it returns an array of quotient
-- polynomials /Q/. The number of divisor (and hence quotient) polynomials,
-- is given by /len/.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_divrem_ideal"
  fq_nmod_mpoly_divrem_ideal :: Ptr (Ptr (Ptr CFqNModMPoly)) -> Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr (Ptr (Ptr CFqNModMPoly)) -> CLong -> Ptr CFqNModMPolyCtx -> IO ()

-- Greatest Common Divisor -----------------------------------------------------

-- | /fq_nmod_mpoly_term_content/ /M/ /A/ /ctx/ 
--
-- Set /M/ to the GCD of the terms of /A/. If /A/ is zero, /M/ will be
-- zero. Otherwise, /M/ will be a monomial with coefficient one.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_term_content"
  fq_nmod_mpoly_term_content :: Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_content_vars/ /g/ /A/ /vars/ /vars_length/ /ctx/ 
--
-- Set /g/ to the GCD of the coefficients of /A/ when viewed as a
-- polynomial in the variables /vars/. Return \(1\) for success and \(0\)
-- for failure. Upon success, /g/ will be independent of the variables
-- /vars/.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_content_vars"
  fq_nmod_mpoly_content_vars :: Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CLong -> CLong -> Ptr CFqNModMPolyCtx -> IO CInt

-- | /fq_nmod_mpoly_gcd/ /G/ /A/ /B/ /ctx/ 
--
-- Try to set /G/ to the monic GCD of /A/ and /B/. The GCD of zero and zero
-- is defined to be zero. If the return is \(1\) the function was
-- successful. Otherwise the return is \(0\) and /G/ is left untouched.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_gcd"
  fq_nmod_mpoly_gcd :: Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO CInt

-- | /fq_nmod_mpoly_gcd_cofactors/ /G/ /Abar/ /Bbar/ /A/ /B/ /ctx/ 
--
-- Do the operation of @fq_nmod_mpoly_gcd@ and also compute \(Abar = A/G\)
-- and \(Bbar = B/G\) if successful.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_gcd_cofactors"
  fq_nmod_mpoly_gcd_cofactors :: Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO CInt

-- | /fq_nmod_mpoly_gcd_brown/ /G/ /A/ /B/ /ctx/ 
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_gcd_brown"
  fq_nmod_mpoly_gcd_brown :: Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO CInt
-- | /fq_nmod_mpoly_gcd_hensel/ /G/ /A/ /B/ /ctx/ 
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_gcd_hensel"
  fq_nmod_mpoly_gcd_hensel :: Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO CInt
-- | /fq_nmod_mpoly_gcd_zippel/ /G/ /A/ /B/ /ctx/ 
--
-- Try to set /G/ to the GCD of /A/ and /B/ using various algorithms.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_gcd_zippel"
  fq_nmod_mpoly_gcd_zippel :: Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO CInt

-- | /fq_nmod_mpoly_resultant/ /R/ /A/ /B/ /var/ /ctx/ 
--
-- Try to set /R/ to the resultant of /A/ and /B/ with respect to the
-- variable of index /var/.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_resultant"
  fq_nmod_mpoly_resultant :: Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> CLong -> Ptr CFqNModMPolyCtx -> IO CInt

-- | /fq_nmod_mpoly_discriminant/ /D/ /A/ /var/ /ctx/ 
--
-- Try to set /D/ to the discriminant of /A/ with respect to the variable
-- of index /var/.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_discriminant"
  fq_nmod_mpoly_discriminant :: Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> CLong -> Ptr CFqNModMPolyCtx -> IO CInt

-- Square Root -----------------------------------------------------------------

-- | /fq_nmod_mpoly_sqrt/ /Q/ /A/ /ctx/ 
--
-- If \(Q^2=A\) has a solution, set \(Q\) to a solution and return \(1\),
-- otherwise return \(0\) and set \(Q\) to zero.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_sqrt"
  fq_nmod_mpoly_sqrt :: Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO CInt

-- | /fq_nmod_mpoly_is_square/ /A/ /ctx/ 
--
-- Return \(1\) if /A/ is a perfect square, otherwise return \(0\).
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_is_square"
  fq_nmod_mpoly_is_square :: Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO CInt

-- | /fq_nmod_mpoly_quadratic_root/ /Q/ /A/ /B/ /ctx/ 
--
-- If \(Q^2+AQ=B\) has a solution, set \(Q\) to a solution and return
-- \(1\), otherwise return \(0\).
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_quadratic_root"
  fq_nmod_mpoly_quadratic_root :: Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CFqNModMPoly -> Ptr CFqNModMPolyCtx -> IO CInt

-- Univariate Functions --------------------------------------------------------

-- | /fq_nmod_mpoly_univar_init/ /A/ /ctx/ 
--
-- Initialize /A/.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_univar_init"
  fq_nmod_mpoly_univar_init :: Ptr CFqNModMPolyUnivar -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_univar_clear/ /A/ /ctx/ 
--
-- Clear /A/.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_univar_clear"
  fq_nmod_mpoly_univar_clear :: Ptr CFqNModMPolyUnivar -> Ptr CFqNModMPolyCtx -> IO ()

foreign import ccall "fq_nmod_mpoly.h &fq_nmod_mpoly_univar_clear"
  p_fq_nmod_mpoly_univar_clear :: FunPtr (Ptr CFqNModMPolyUnivar -> Ptr CFqNModMPolyCtx -> IO ())

-- | /fq_nmod_mpoly_univar_swap/ /A/ /B/ /ctx/ 
--
-- Swap /A/ and \(B\).
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_univar_swap"
  fq_nmod_mpoly_univar_swap :: Ptr CFqNModMPolyUnivar -> Ptr CFqNModMPolyUnivar -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_to_univar/ /A/ /B/ /var/ /ctx/ 
--
-- Set /A/ to a univariate form of /B/ by pulling out the variable of index
-- /var/. The coefficients of /A/ will still belong to the content /ctx/
-- but will not depend on the variable of index /var/.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_to_univar"
  fq_nmod_mpoly_to_univar :: Ptr CFqNModMPolyUnivar -> Ptr CFqNModMPoly -> CLong -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_from_univar/ /A/ /B/ /var/ /ctx/ 
--
-- Set /A/ to the normal form of /B/ by putting in the variable of index
-- /var/. This function is undefined if the coefficients of /B/ depend on
-- the variable of index /var/.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_from_univar"
  fq_nmod_mpoly_from_univar :: Ptr CFqNModMPoly -> Ptr CFqNModMPolyUnivar -> CLong -> Ptr CFqNModMPolyCtx -> IO ()

-- | /fq_nmod_mpoly_univar_degree_fits_si/ /A/ /ctx/ 
--
-- Return \(1\) if the degree of /A/ with respect to the main variable fits
-- an @slong@. Otherwise, return \(0\).
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_univar_degree_fits_si"
  fq_nmod_mpoly_univar_degree_fits_si :: Ptr CFqNModMPolyUnivar -> Ptr CFqNModMPolyCtx -> IO CInt

-- | /fq_nmod_mpoly_univar_length/ /A/ /ctx/ 
--
-- Return the number of terms in /A/ with respect to the main variable.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_univar_length"
  fq_nmod_mpoly_univar_length :: Ptr CFqNModMPolyUnivar -> Ptr CFqNModMPolyCtx -> IO CLong

-- | /fq_nmod_mpoly_univar_get_term_exp_si/ /A/ /i/ /ctx/ 
--
-- Return the exponent of the term of index /i/ of /A/.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_univar_get_term_exp_si"
  fq_nmod_mpoly_univar_get_term_exp_si :: Ptr CFqNModMPolyUnivar -> CLong -> Ptr CFqNModMPolyCtx -> IO CLong

-- | /fq_nmod_mpoly_univar_get_term_coeff/ /c/ /A/ /i/ /ctx/ 
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_univar_get_term_coeff"
  fq_nmod_mpoly_univar_get_term_coeff :: Ptr CFqNModMPoly -> Ptr CFqNModMPolyUnivar -> CLong -> Ptr CFqNModMPolyCtx -> IO ()
-- | /fq_nmod_mpoly_univar_swap_term_coeff/ /c/ /A/ /i/ /ctx/ 
--
-- Set (resp. swap) /c/ to (resp. with) the coefficient of the term of
-- index /i/ of /A/.
foreign import ccall "fq_nmod_mpoly.h fq_nmod_mpoly_univar_swap_term_coeff"
  fq_nmod_mpoly_univar_swap_term_coeff :: Ptr CFqNModMPoly -> Ptr CFqNModMPolyUnivar -> CLong -> Ptr CFqNModMPolyCtx -> IO ()

