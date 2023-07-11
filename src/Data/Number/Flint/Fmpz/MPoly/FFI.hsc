module Data.Number.Flint.Fmpz.MPoly.FFI (
  -- * Multivariate polynomials over the integers
    FmpzMPoly (..)
  , CFmpzMPoly (..)
  , newFmpzMPoly
  , withFmpzMPoly
  -- * Context object
  , FmpzMPolyCtx (..)
  , CFmpzMPolyCtx (..)
  , newFmpzMPolyCtx
  , withFmpzMPolyCtx
  , fmpz_mpoly_ctx_init
  , fmpz_mpoly_ctx_nvars
  , fmpz_mpoly_ctx_ord
  , fmpz_mpoly_ctx_clear
  -- * Memory management
  , fmpz_mpoly_init
  , fmpz_mpoly_init2
  , fmpz_mpoly_init3
  , fmpz_mpoly_fit_length
  , fmpz_mpoly_fit_bits
  , fmpz_mpoly_realloc
  , fmpz_mpoly_clear
  -- * Input\/Output
  , fmpz_mpoly_get_str_pretty
  , fmpz_mpoly_fprint_pretty
  , fmpz_mpoly_print_pretty
  , fmpz_mpoly_set_str_pretty
  -- * Basic manipulation
  , fmpz_mpoly_gen
  , fmpz_mpoly_is_gen
  , fmpz_mpoly_set
  , fmpz_mpoly_equal
  , fmpz_mpoly_swap
  , _fmpz_mpoly_fits_small
  , fmpz_mpoly_max_bits
  -- * Constants
  , fmpz_mpoly_is_fmpz
  , fmpz_mpoly_get_fmpz
  , fmpz_mpoly_set_fmpz
  , fmpz_mpoly_zero
  , fmpz_mpoly_one
  , fmpz_mpoly_equal_fmpz
  , fmpz_mpoly_is_zero
  , fmpz_mpoly_is_one
  -- * Degrees
  , fmpz_mpoly_degrees_fit_si
  , fmpz_mpoly_degrees_fmpz
  , fmpz_mpoly_degree_fmpz
  , fmpz_mpoly_total_degree_fits_si
  , fmpz_mpoly_total_degree_fmpz
  , fmpz_mpoly_used_vars
  -- * Coefficients
  , fmpz_mpoly_get_coeff_fmpz_monomial
  , fmpz_mpoly_set_coeff_fmpz_monomial
  , fmpz_mpoly_get_coeff_fmpz_fmpz
  , fmpz_mpoly_set_coeff_fmpz_fmpz
  , fmpz_mpoly_get_coeff_vars_ui
  -- * Comparison
  , fmpz_mpoly_cmp
  -- * Conversion
  , fmpz_mpoly_is_fmpz_poly
  , fmpz_mpoly_get_fmpz_poly
  , fmpz_mpoly_set_fmpz_poly
  -- * Container operations
  , fmpz_mpoly_term_coeff_ref
  , fmpz_mpoly_is_canonical
  , fmpz_mpoly_length
  , fmpz_mpoly_resize
  , fmpz_mpoly_get_term_coeff_fmpz
  , fmpz_mpoly_set_term_coeff_fmpz
  , fmpz_mpoly_term_exp_fits_si
  , fmpz_mpoly_get_term_exp_fmpz
  , fmpz_mpoly_get_term_var_exp_ui
  , fmpz_mpoly_set_term_exp_fmpz
  , fmpz_mpoly_get_term
  , fmpz_mpoly_get_term_monomial
  , fmpz_mpoly_push_term_fmpz_fmpz
  , fmpz_mpoly_sort_terms
  , fmpz_mpoly_combine_like_terms
  , fmpz_mpoly_reverse
  -- * Random generation
  , fmpz_mpoly_randtest_bound
  , fmpz_mpoly_randtest_bounds
  , fmpz_mpoly_randtest_bits
  -- * Addition\/Subtraction
  , fmpz_mpoly_add_fmpz
  , fmpz_mpoly_sub_fmpz
  , fmpz_mpoly_add
  , fmpz_mpoly_sub
  -- * Scalar operations
  , fmpz_mpoly_neg
  , fmpz_mpoly_scalar_mul_fmpz
  , fmpz_mpoly_scalar_fmma
  , fmpz_mpoly_scalar_divexact_fmpz
  , fmpz_mpoly_scalar_divides_fmpz
  -- * Differentiation\/Integration
  , fmpz_mpoly_derivative
  , fmpz_mpoly_integral
  -- * Evaluation
  , fmpz_mpoly_evaluate_all_fmpz
  , fmpz_mpoly_evaluate_one_fmpz
  , fmpz_mpoly_compose_fmpz_poly
  , fmpz_mpoly_compose_fmpz_mpoly_geobucket
  , fmpz_mpoly_compose_fmpz_mpoly_gen
  -- * Multiplication
  , fmpz_mpoly_mul
  , fmpz_mpoly_mul_johnson
  , fmpz_mpoly_mul_array
  , fmpz_mpoly_mul_dense
  -- * Powering
  , fmpz_mpoly_pow_fmpz
  , fmpz_mpoly_pow_ui
  -- * Division
  , fmpz_mpoly_divides
  , fmpz_mpoly_divrem
  , fmpz_mpoly_quasidivrem
  , fmpz_mpoly_div
  , fmpz_mpoly_quasidiv
  , fmpz_mpoly_divrem_ideal
  , fmpz_mpoly_quasidivrem_ideal
  -- * Greatest Common Divisor
  , fmpz_mpoly_term_content
  , fmpz_mpoly_content_vars
  , fmpz_mpoly_gcd
  , fmpz_mpoly_gcd_cofactors
  , fmpz_mpoly_gcd_brown
  , fmpz_mpoly_resultant
  , fmpz_mpoly_discriminant
  , fmpz_mpoly_primitive_part
  -- * Square Root
  , fmpz_mpoly_sqrt_heap
  , fmpz_mpoly_sqrt
  , fmpz_mpoly_is_square
  -- * Univariate Functions
  , fmpz_mpoly_univar_init
  , fmpz_mpoly_univar_clear
  , fmpz_mpoly_univar_swap
  , fmpz_mpoly_to_univar
  , fmpz_mpoly_from_univar
  , fmpz_mpoly_univar_degree_fits_si
  , fmpz_mpoly_univar_length
  , fmpz_mpoly_univar_get_term_exp_si
  , fmpz_mpoly_univar_get_term_coeff
  -- * Internal Functions
  , fmpz_mpoly_inflate
  , fmpz_mpoly_deflate
  , fmpz_mpoly_deflation
  , fmpz_mpoly_pow_fps
  , _fmpz_mpoly_divides_array
  , fmpz_mpoly_divides_array
  , _fmpz_mpoly_divides_monagan_pearce
  , fmpz_mpoly_divides_monagan_pearce
  , fmpz_mpoly_divides_heap_threaded
  , _fmpz_mpoly_div_monagan_pearce
  , fmpz_mpoly_div_monagan_pearce
  , _fmpz_mpoly_divrem_monagan_pearce
  , fmpz_mpoly_divrem_monagan_pearce
  , _fmpz_mpoly_divrem_array
  , fmpz_mpoly_divrem_array
  , fmpz_mpoly_quasidivrem_heap
  , _fmpz_mpoly_divrem_ideal_monagan_pearce
  , fmpz_mpoly_divrem_ideal_monagan_pearce
  -- * Vectors
  , fmpz_mpoly_vec_init
  , fmpz_mpoly_vec_clear
  , fmpz_mpoly_vec_print
  , fmpz_mpoly_vec_swap
  , fmpz_mpoly_vec_fit_length
  , fmpz_mpoly_vec_set
  , fmpz_mpoly_vec_append
  , fmpz_mpoly_vec_insert_unique
  , fmpz_mpoly_vec_set_length
  , fmpz_mpoly_vec_randtest_not_zero
  , fmpz_mpoly_vec_set_primitive_unique
  -- * Ideals and Gröbner bases
  , fmpz_mpoly_spoly
  , fmpz_mpoly_reduction_primitive_part
  , fmpz_mpoly_vec_is_groebner
  , fmpz_mpoly_vec_is_autoreduced
  , fmpz_mpoly_vec_autoreduction
  , fmpz_mpoly_vec_autoreduction_groebner
  -- , fmpz_mpoly_select_pop_pair
  , fmpz_mpoly_buchberger_naive
  , fmpz_mpoly_buchberger_naive_with_limits
  -- * Special polynomials
  , fmpz_mpoly_symmetric_gens
  , fmpz_mpoly_symmetric
) where

-- Multivariate polynomials over the integers ----------------------------------

import Control.Monad

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, nullPtr, plusPtr )
import Foreign.Storable
import Foreign.Marshal ( free )
import Foreign.Marshal.Array ( advancePtr )

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Poly
import Data.Number.Flint.Fmpq
import Data.Number.Flint.MPoly

#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpq.h>
#include <flint/fmpz_mpoly.h>

-- fmpz_mpoly_t ----------------------------------------------------------------

data FmpzMPoly = FmpzMPoly {-# UNPACK #-} !(ForeignPtr CFmpzMPoly)
data CFmpzMPoly = CFmpzMPoly 

instance Storable CFmpzMPoly where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fmpz_mpoly_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fmpz_mpoly_t}
  peek = error "CFmpzMPoly.peek: Not defined"
  poke = error "CFmpzMPoly.poke: Not defined"

-- | Create a new `FmpzMPoly`
newFmpzMPoly ctx@(FmpzMPolyCtx pctx) = do
  p <- mallocForeignPtr
  withForeignPtr p $ \p ->
    withFmpzMPolyCtx ctx $ \ctx -> do 
      fmpz_mpoly_init p ctx
      addForeignPtrFinalizerEnv p_fmpz_mpoly_clear p pctx 
  return $ FmpzMPoly p

{-# INLINE withFmpzMPoly #-}
withFmpzMPoly (FmpzMPoly p) f = do
  withForeignPtr p $ \fp -> (FmpzMPoly p,) <$> f fp

-- fmpz_mpoly_univar_t ---------------------------------------------------------

data FmpzMPolyUnivar = FmpzMPolyUnivar {-# UNPACK #-} !(ForeignPtr CFmpzMPolyUnivar)
data CFmpzMPolyUnivar = CFmpzMPolyUnivar 

instance Storable CFmpzMPolyUnivar where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fmpz_mpoly_univar_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fmpz_mpoly_univar_t}
  peek = error "CFmpzMPolyUnivar.peek: Not defined"
  poke = error "CFmpzMPolyUnivar.poke: Not defined"

-- | Create a new `FmpzMPolyUnivar`
newFmpzMPolyUnivar ctx@(FmpzMPolyCtx pctx) = do
  p <- mallocForeignPtr
  withForeignPtr p $ \p ->
    withFmpzMPolyCtx ctx $ \ctx -> do 
      fmpz_mpoly_univar_init p ctx
      addForeignPtrFinalizerEnv p_fmpz_mpoly_univar_clear p pctx
  return $ FmpzMPolyUnivar p

{-# INLINE withFmpzMPolyUnivar #-}
withFmpzMPolyUnivar (FmpzMPolyUnivar p) f = do
  withForeignPtr p $ \fp -> (FmpzMPolyUnivar p,) <$> f fp
  
-- fmpz_mpoly_ctx_t ------------------------------------------------------------

data FmpzMPolyCtx = FmpzMPolyCtx {-# UNPACK #-} !(ForeignPtr CFmpzMPolyCtx)
data CFmpzMPolyCtx

instance Storable CFmpzMPolyCtx where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fmpz_mpoly_ctx_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fmpz_mpoly_ctx_t}
  peek = error "CFmpzMPolyCtx.peek: Not defined"
  poke = error "CFmpzMPolyCtx.poke: Not defined"

-- | Create a new `FmpzMPolyCtx`
newFmpzMPolyCtx nvars ord = do
  p <- mallocForeignPtr
  withForeignPtr p $ \p ->
    fmpz_mpoly_ctx_init p nvars ord
  addForeignPtrFinalizer p_fmpz_mpoly_ctx_clear p
  return $ FmpzMPolyCtx p

-- | Use a `FmpzMPolyCtx`
{-# INLINE withFmpzMPolyCtx #-}
withFmpzMPolyCtx (FmpzMPolyCtx p) f = do
  withForeignPtr p $ \fp -> f fp >>= return . (FmpzMPolyCtx p,)

-- fmpz_mpoly_vec_t ------------------------------------------------------------

data FmpzMPolyVec = FmpzMPolyVec {-# UNPACK #-} !(ForeignPtr CFmpzMPolyVec)
data CFmpzMPolyVec = CFmpzMPolyVec (Ptr CFmpzMPoly) CLong CLong

-- pair_t ----------------------------------------------------------------------

data CPair = CPair CLong CLong
data CPairs = CPairs (Ptr CPair) CLong CLong

--------------------------------------------------------------------------------

-- | /fmpz_mpoly_ctx_init/ /ctx/ /nvars/ /ord/ 
-- 
-- Initialise a context object for a polynomial ring with the given number
-- of variables and the given ordering. The possibilities for the ordering
-- are @ORD_LEX@, @ORD_DEGLEX@ and @ORD_DEGREVLEX@.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_ctx_init"
  fmpz_mpoly_ctx_init :: Ptr CFmpzMPolyCtx -> CLong -> COrdering -> IO ()

-- | /fmpz_mpoly_ctx_nvars/ /ctx/ 
-- 
-- Return the number of variables used to initialize the context.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_ctx_nvars"
  fmpz_mpoly_ctx_nvars :: Ptr CFmpzMPolyCtx -> IO CLong

-- | /fmpz_mpoly_ctx_ord/ /ctx/ 
-- 
-- Return the ordering used to initialize the context.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_ctx_ord"
  fmpz_mpoly_ctx_ord :: Ptr CFmpzMPolyCtx -> IO COrdering

-- | /fmpz_mpoly_ctx_clear/ /ctx/ 
-- 
-- Release up any space allocated by /ctx/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_ctx_clear"
  fmpz_mpoly_ctx_clear :: Ptr CFmpzMPolyCtx -> IO ()

foreign import ccall "fmpz_mpoly.h &fmpz_mpoly_ctx_clear"
  p_fmpz_mpoly_ctx_clear :: FunPtr (Ptr CFmpzMPolyCtx -> IO ())

-- Memory management -----------------------------------------------------------

-- | /fmpz_mpoly_init/ /A/ /ctx/ 
-- 
-- Initialise /A/ for use with the given and initialised context object.
-- Its value is set to zero.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_init"
  fmpz_mpoly_init :: Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_init2/ /A/ /alloc/ /ctx/ 
-- 
-- Initialise /A/ for use with the given and initialised context object.
-- Its value is set to zero. It is allocated with space for /alloc/ terms
-- and at least @MPOLY_MIN_BITS@ bits for the exponents.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_init2"
  fmpz_mpoly_init2 :: Ptr CFmpzMPoly -> CLong -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_init3/ /A/ /alloc/ /bits/ /ctx/ 
-- 
-- Initialise /A/ for use with the given and initialised context object.
-- Its value is set to zero. It is allocated with space for /alloc/ terms
-- and /bits/ bits for the exponents.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_init3"
  fmpz_mpoly_init3 :: Ptr CFmpzMPoly -> CLong -> CFBitCnt -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_fit_length/ /A/ /len/ /ctx/ 
-- 
-- Ensure that /A/ has space for at least /len/ terms.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_fit_length"
  fmpz_mpoly_fit_length :: Ptr CFmpzMPoly -> CLong -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_fit_bits/ /A/ /bits/ /ctx/ 
-- 
-- Ensure that the exponent fields of /A/ have at least /bits/ bits.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_fit_bits"
  fmpz_mpoly_fit_bits :: Ptr CFmpzMPoly -> CFBitCnt -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_realloc/ /A/ /alloc/ /ctx/ 
-- 
-- Reallocate /A/ to have space for /alloc/ terms. Assumes the current
-- length of the polynomial is not greater than /alloc/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_realloc"
  fmpz_mpoly_realloc :: Ptr CFmpzMPoly -> CLong -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_clear/ /A/ /ctx/ 
-- 
-- Release any space allocated for /A/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_clear"
  fmpz_mpoly_clear :: Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO ()

foreign import ccall "fmpz_mpoly.h &fmpz_mpoly_clear"
  p_fmpz_mpoly_clear :: FunPtr (Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO ())

-- Input\/Output ---------------------------------------------------------------

-- | /fmpz_mpoly_get_str_pretty/ /A/ /x/ /ctx/ 
-- 
-- Return a string, which the user is responsible for cleaning up,
-- representing /A/, given an array of variable strings /x/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_get_str_pretty"
  fmpz_mpoly_get_str_pretty :: Ptr CFmpzMPoly -> Ptr (Ptr CChar) -> Ptr CFmpzMPolyCtx -> IO CString

-- | /fmpz_mpoly_fprint_pretty/ /file/ /A/ /x/ /ctx/ 
-- 
-- Print a string representing /A/ to /file/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_fprint_pretty"
  fmpz_mpoly_fprint_pretty :: Ptr CFile -> Ptr CFmpzMPoly -> Ptr (Ptr CChar) -> Ptr CFmpzMPolyCtx -> IO CInt

-- | /fmpz_mpoly_print_pretty/ /A/ /x/ /ctx/ 
-- 
-- Print a string representing /A/ to @stdout@.
-- foreign import ccall "fmpz_mpoly.h fmpz_mpoly_print_pretty"
--   fmpz_mpoly_print_pretty :: Ptr CFmpzMPoly -> Ptr (Ptr CChar) -> Ptr CFmpzMPolyCtx -> IO CInt
fmpz_mpoly_print_pretty :: Ptr CFmpzMPoly ->
                           Ptr (Ptr CChar) ->
                           Ptr CFmpzMPolyCtx -> IO CInt
fmpz_mpoly_print_pretty a x ctx =
  printCStr (\a -> fmpz_mpoly_get_str_pretty a x ctx) a

-- | /fmpz_mpoly_set_str_pretty/ /A/ /str/ /x/ /ctx/ 
-- 
-- Set /A/ to the polynomial in the null-terminates string /str/ given an
-- array /x/ of variable strings. If parsing /str/ fails, /A/ is set to
-- zero, and \(-1\) is returned. Otherwise, \(0\) is returned. The
-- operations @+@, @-@, @*@, and @\/@ are permitted along with integers and
-- the variables in /x/. The character @^@ must be immediately followed by
-- the (integer) exponent. If any division is not exact, parsing fails.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_set_str_pretty"
  fmpz_mpoly_set_str_pretty :: Ptr CFmpzMPoly -> CString -> Ptr (Ptr CChar) -> Ptr CFmpzMPolyCtx -> IO CInt

-- Basic manipulation ----------------------------------------------------------

-- | /fmpz_mpoly_gen/ /A/ /var/ /ctx/ 
-- 
-- Set /A/ to the variable of index /var/, where \(var = 0\) corresponds to
-- the variable with the most significance with respect to the ordering.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_gen"
  fmpz_mpoly_gen :: Ptr CFmpzMPoly -> CLong -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_is_gen/ /A/ /var/ /ctx/ 
-- 
-- If \(var \ge 0\), return \(1\) if /A/ is equal to the \(var\)-th
-- generator, otherwise return \(0\). If \(var < 0\), return \(1\) if the
-- polynomial is equal to any generator, otherwise return \(0\).
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_is_gen"
  fmpz_mpoly_is_gen :: Ptr CFmpzMPoly -> CLong -> Ptr CFmpzMPolyCtx -> IO CInt

-- | /fmpz_mpoly_set/ /A/ /B/ /ctx/ 
-- 
-- Set /A/ to /B/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_set"
  fmpz_mpoly_set :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_equal/ /A/ /B/ /ctx/ 
-- 
-- Return \(1\) if /A/ is equal to /B/, else return \(0\).
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_equal"
  fmpz_mpoly_equal :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO CInt

-- | /fmpz_mpoly_swap/ /poly1/ /poly2/ /ctx/ 
-- 
-- Efficiently swap /A/ and /B/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_swap"
  fmpz_mpoly_swap :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO ()

-- | /_fmpz_mpoly_fits_small/ /poly/ /len/ 
-- 
-- Return 1 if the array of coefficients of length /len/ consists entirely
-- of values that are small @fmpz@ values, i.e. of at most @FLINT_BITS - 2@
-- bits plus a sign bit.
foreign import ccall "fmpz_mpoly.h _fmpz_mpoly_fits_small"
  _fmpz_mpoly_fits_small :: Ptr CFmpz -> CLong -> IO CInt

-- | /fmpz_mpoly_max_bits/ /A/ 
-- 
-- Computes the maximum number of bits \(b\) required to represent the
-- absolute values of the coefficients of /A/. If all of the coefficients
-- are positive, \(b\) is returned, otherwise \(-b\) is returned.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_max_bits"
  fmpz_mpoly_max_bits :: Ptr CFmpzMPoly -> IO CLong

-- Constants -------------------------------------------------------------------

-- | /fmpz_mpoly_is_fmpz/ /A/ /ctx/ 
-- 
-- Return \(1\) if /A/ is a constant, else return \(0\).
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_is_fmpz"
  fmpz_mpoly_is_fmpz :: Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO CInt

-- | /fmpz_mpoly_get_fmpz/ /c/ /A/ /ctx/ 
-- 
-- Assuming that /A/ is a constant, set /c/ to this constant. This function
-- throws if /A/ is not a constant.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_get_fmpz"
  fmpz_mpoly_get_fmpz :: Ptr CFmpz -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_set_fmpz/ /A/ /c/ /ctx/ 
-- 
-- Set /A/ to the constant /c/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_set_fmpz"
  fmpz_mpoly_set_fmpz :: Ptr CFmpzMPoly -> Ptr CFmpz -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_zero/ /A/ /ctx/ 
-- 
-- Set /A/ to the constant \(0\).
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_zero"
  fmpz_mpoly_zero :: Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_one/ /A/ /ctx/ 
-- 
-- Set /A/ to the constant \(1\).
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_one"
  fmpz_mpoly_one :: Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_equal_fmpz/ /A/ /c/ /ctx/ 
-- 
-- Return \(1\) if /A/ is equal to the constant /c/, else return \(0\).
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_equal_fmpz"
  fmpz_mpoly_equal_fmpz :: Ptr CFmpzMPoly -> Ptr CFmpz -> Ptr CFmpzMPolyCtx -> IO CInt

-- | /fmpz_mpoly_is_zero/ /A/ /ctx/ 
-- 
-- Return \(1\) if /A/ is the constant \(0\), else return \(0\).
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_is_zero"
  fmpz_mpoly_is_zero :: Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO CInt

-- | /fmpz_mpoly_is_one/ /A/ /ctx/ 
-- 
-- Return \(1\) if /A/ is the constant \(1\), else return \(0\).
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_is_one"
  fmpz_mpoly_is_one :: Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO CInt

-- Degrees ---------------------------------------------------------------------

-- | /fmpz_mpoly_degrees_fit_si/ /A/ /ctx/ 
-- 
-- Return \(1\) if the degrees of /A/ with respect to each variable fit
-- into an @slong@, otherwise return \(0\).
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_degrees_fit_si"
  fmpz_mpoly_degrees_fit_si :: Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO CInt

-- | /fmpz_mpoly_degrees_fmpz/ /degs/ /A/ /ctx/ 
-- 
-- Set /degs/ to the degrees of /A/ with respect to each variable. If /A/
-- is zero, all degrees are set to \(-1\).
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_degrees_fmpz"
  fmpz_mpoly_degrees_fmpz :: Ptr (Ptr CFmpz) -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_degree_fmpz/ /deg/ /A/ /var/ /ctx/ 
-- 
-- Either return or set /deg/ to the degree of /A/ with respect to the
-- variable of index /var/. If /A/ is zero, the degree is defined to be
-- \(-1\).
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_degree_fmpz"
  fmpz_mpoly_degree_fmpz :: Ptr CFmpz -> Ptr CFmpzMPoly -> CLong -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_total_degree_fits_si/ /A/ /ctx/ 
-- 
-- Return \(1\) if the total degree of /A/ fits into an @slong@, otherwise
-- return \(0\).
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_total_degree_fits_si"
  fmpz_mpoly_total_degree_fits_si :: Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO CInt

-- | /fmpz_mpoly_total_degree_fmpz/ /tdeg/ /A/ /ctx/ 
-- 
-- Either return or set /tdeg/ to the total degree of /A/. If /A/ is zero,
-- the total degree is defined to be \(-1\).
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_total_degree_fmpz"
  fmpz_mpoly_total_degree_fmpz :: Ptr CFmpz -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_used_vars/ /used/ /A/ /ctx/ 
-- 
-- For each variable index /i/, set @used[i]@ to nonzero if the variable of
-- index /i/ appears in /A/ and to zero otherwise.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_used_vars"
  fmpz_mpoly_used_vars :: Ptr CInt -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO ()

-- Coefficients ----------------------------------------------------------------

-- | /fmpz_mpoly_get_coeff_fmpz_monomial/ /c/ /A/ /M/ /ctx/ 
-- 
-- Assuming that /M/ is a monomial, set /c/ to the coefficient of the
-- corresponding monomial in /A/. This function throws if /M/ is not a
-- monomial.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_get_coeff_fmpz_monomial"
  fmpz_mpoly_get_coeff_fmpz_monomial :: Ptr CFmpz -> Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_set_coeff_fmpz_monomial/ /poly/ /c/ /poly2/ /ctx/ 
-- 
-- Assuming that /M/ is a monomial, set the coefficient of the
-- corresponding monomial in /A/ to /c/. This function throws if /M/ is not
-- a monomial.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_set_coeff_fmpz_monomial"
  fmpz_mpoly_set_coeff_fmpz_monomial :: Ptr CFmpzMPoly -> Ptr CFmpz -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_get_coeff_fmpz_fmpz/ /c/ /A/ /exp/ /ctx/ 
-- 
-- Either return or set /c/ to the coefficient of the monomial with
-- exponent vector /exp/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_get_coeff_fmpz_fmpz"
  fmpz_mpoly_get_coeff_fmpz_fmpz :: Ptr CFmpz -> Ptr CFmpzMPoly -> Ptr (Ptr CFmpz) -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_set_coeff_fmpz_fmpz/ /A/ /c/ /exp/ /ctx/ 
-- 
-- Set the coefficient of the monomial with exponent vector /exp/ to /c/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_set_coeff_fmpz_fmpz"
  fmpz_mpoly_set_coeff_fmpz_fmpz :: Ptr CFmpzMPoly -> Ptr CFmpz -> Ptr (Ptr CFmpz) -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_get_coeff_vars_ui/ /C/ /A/ /vars/ /exps/ /length/ /ctx/ 
-- 
-- Set /C/ to the coefficient of /A/ with respect to the variables in
-- /vars/ with powers in the corresponding array /exps/. Both /vars/ and
-- /exps/ point to array of length /length/. It is assumed that
-- \(0 < length \le nvars(A)\) and that the variables in /vars/ are
-- distinct.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_get_coeff_vars_ui"
  fmpz_mpoly_get_coeff_vars_ui :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CLong -> Ptr CULong -> CLong -> Ptr CFmpzMPolyCtx -> IO ()

-- Comparison ------------------------------------------------------------------

-- | /fmpz_mpoly_cmp/ /A/ /B/ /ctx/ 
-- 
-- Return \(1\) (resp. \(-1\), or \(0\)) if /A/ is after (resp. before,
-- same as) /B/ in some arbitrary but fixed total ordering of the
-- polynomials. This ordering agrees with the usual ordering of monomials
-- when /A/ and /B/ are both monomials.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_cmp"
  fmpz_mpoly_cmp :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO CInt

-- Conversion ------------------------------------------------------------------

-- | /fmpz_mpoly_is_fmpz_poly/ /A/ /var/ /ctx/ 
-- 
-- Return whether /A/ is a univariate polynomial in the variable with index
-- /var/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_is_fmpz_poly"
  fmpz_mpoly_is_fmpz_poly :: Ptr CFmpzMPoly -> CLong -> Ptr CFmpzMPolyCtx -> IO CInt

-- | /fmpz_mpoly_get_fmpz_poly/ /A/ /B/ /var/ /ctx/ 
-- 
-- If /B/ is a univariate polynomial in the variable with index /var/, set
-- /A/ to this polynomial and return 1; otherwise return 0.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_get_fmpz_poly"
  fmpz_mpoly_get_fmpz_poly :: Ptr CFmpzPoly -> Ptr CFmpzMPoly -> CLong -> Ptr CFmpzMPolyCtx -> IO CInt

-- | /fmpz_mpoly_set_fmpz_poly/ /A/ /B/ /var/ /ctx/ 
-- 
-- Set /A/ to the univariate polynomial /B/ in the variable with index
-- /var/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_set_fmpz_poly"
  fmpz_mpoly_set_fmpz_poly :: Ptr CFmpzMPoly -> Ptr CFmpzPoly -> CLong -> Ptr CFmpzMPolyCtx -> IO ()

-- Container operations --------------------------------------------------------




-- | /fmpz_mpoly_term_coeff_ref/ /A/ /i/ /ctx/ 
-- 
-- Return a reference to the coefficient of index /i/ of /A/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_term_coeff_ref"
  fmpz_mpoly_term_coeff_ref :: Ptr CFmpzMPoly -> CLong -> Ptr CFmpzMPolyCtx -> IO (Ptr CFmpz)

-- | /fmpz_mpoly_is_canonical/ /A/ /ctx/ 
-- 
-- Return \(1\) if /A/ is in canonical form. Otherwise, return \(0\). To be
-- in canonical form, all of the terms must have nonzero coefficient, and
-- the terms must be sorted from greatest to least.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_is_canonical"
  fmpz_mpoly_is_canonical :: Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO CInt

-- | /fmpz_mpoly_length/ /A/ /ctx/ 
-- 
-- Return the number of terms in /A/. If the polynomial is in canonical
-- form, this will be the number of nonzero coefficients.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_length"
  fmpz_mpoly_length :: Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO CLong

-- | /fmpz_mpoly_resize/ /A/ /new_length/ /ctx/ 
-- 
-- Set the length of /A/ to \(new\_length\). Terms are either deleted from
-- the end, or new zero terms are appended.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_resize"
  fmpz_mpoly_resize :: Ptr CFmpzMPoly -> CLong -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_get_term_coeff_fmpz/ /c/ /A/ /i/ /ctx/ 
-- 
-- Either return or set /c/ to the coefficient of the term of index /i/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_get_term_coeff_fmpz"
  fmpz_mpoly_get_term_coeff_fmpz :: Ptr CFmpz -> Ptr CFmpzMPoly -> CLong -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_set_term_coeff_fmpz/ /A/ /i/ /c/ /ctx/ 
-- 
-- Set the coefficient of the term of index /i/ to /c/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_set_term_coeff_fmpz"
  fmpz_mpoly_set_term_coeff_fmpz :: Ptr CFmpzMPoly -> CLong -> Ptr CFmpz -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_term_exp_fits_si/ /poly/ /i/ /ctx/ 
-- 
-- Return \(1\) if all entries of the exponent vector of the term of index
-- /i/ fit into an @slong@ (resp. a @ulong@). Otherwise, return \(0\).
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_term_exp_fits_si"
  fmpz_mpoly_term_exp_fits_si :: Ptr CFmpzMPoly -> CLong -> Ptr CFmpzMPolyCtx -> IO CInt

-- | /fmpz_mpoly_get_term_exp_fmpz/ /exp/ /A/ /i/ /ctx/ 
-- 
-- Set /exp/ to the exponent vector of the term of index /i/. The @_ui@
-- (resp. @_si@) version throws if any entry does not fit into a @ulong@
-- (resp. @slong@).
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_get_term_exp_fmpz"
  fmpz_mpoly_get_term_exp_fmpz :: Ptr (Ptr CFmpz) -> Ptr CFmpzMPoly -> CLong -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_get_term_var_exp_ui/ /A/ /i/ /var/ /ctx/ 
-- 
-- Return the exponent of the variable \(var\) of the term of index /i/.
-- This function throws if the exponent does not fit into a @ulong@ (resp.
-- @slong@).
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_get_term_var_exp_ui"
  fmpz_mpoly_get_term_var_exp_ui :: Ptr CFmpzMPoly -> CLong -> CLong -> Ptr CFmpzMPolyCtx -> IO CULong

-- | /fmpz_mpoly_set_term_exp_fmpz/ /A/ /i/ /exp/ /ctx/ 
-- 
-- Set the exponent vector of the term of index /i/ to /exp/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_set_term_exp_fmpz"
  fmpz_mpoly_set_term_exp_fmpz :: Ptr CFmpzMPoly -> CLong -> Ptr (Ptr CFmpz) -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_get_term/ /M/ /A/ /i/ /ctx/ 
-- 
-- Set \(M\) to the term of index /i/ in /A/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_get_term"
  fmpz_mpoly_get_term :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> CLong -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_get_term_monomial/ /M/ /A/ /i/ /ctx/ 
-- 
-- Set \(M\) to the monomial of the term of index /i/ in /A/. The
-- coefficient of \(M\) will be one.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_get_term_monomial"
  fmpz_mpoly_get_term_monomial :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> CLong -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_push_term_fmpz_fmpz/ /A/ /c/ /exp/ /ctx/ 
-- 
-- Append a term to /A/ with coefficient /c/ and exponent vector /exp/.
-- This function runs in constant average time.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_push_term_fmpz_fmpz"
  fmpz_mpoly_push_term_fmpz_fmpz :: Ptr CFmpzMPoly -> Ptr CFmpz -> Ptr (Ptr CFmpz) -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_sort_terms/ /A/ /ctx/ 
-- 
-- Sort the terms of /A/ into the canonical ordering dictated by the
-- ordering in /ctx/. This function simply reorders the terms: It does not
-- combine like terms, nor does it delete terms with coefficient zero. This
-- function runs in linear time in the size of /A/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_sort_terms"
  fmpz_mpoly_sort_terms :: Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_combine_like_terms/ /A/ /ctx/ 
-- 
-- Combine adjacent like terms in /A/ and delete terms with coefficient
-- zero. If the terms of /A/ were sorted to begin with, the result will be
-- in canonical form. This function runs in linear time in the size of /A/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_combine_like_terms"
  fmpz_mpoly_combine_like_terms :: Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_reverse/ /A/ /B/ /ctx/ 
-- 
-- Set /A/ to the reversal of /B/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_reverse"
  fmpz_mpoly_reverse :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO ()

-- Random generation -----------------------------------------------------------

-- | /fmpz_mpoly_randtest_bound/ /A/ /state/ /length/ /coeff_bits/ /exp_bound/ /ctx/ 
-- 
-- Generate a random polynomial with length up to /length/ and exponents in
-- the range @[0, exp_bound - 1]@. The exponents of each variable are
-- generated by calls to @n_randint(state, exp_bound)@.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_randtest_bound"
  fmpz_mpoly_randtest_bound :: Ptr CFmpzMPoly -> Ptr CFRandState -> CLong -> CMpLimb -> CULong -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_randtest_bounds/ /A/ /state/ /length/ /coeff_bits/ /exp_bounds/ /ctx/ 
-- 
-- Generate a random polynomial with length up to /length/ and exponents in
-- the range @[0, exp_bounds[i] - 1]@. The exponents of the variable of
-- index /i/ are generated by calls to @n_randint(state, exp_bounds[i])@.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_randtest_bounds"
  fmpz_mpoly_randtest_bounds :: Ptr CFmpzMPoly -> Ptr CFRandState -> CLong -> CMpLimb -> Ptr CULong -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_randtest_bits/ /A/ /state/ /length/ /coeff_bits/ /exp_bits/ /ctx/ 
-- 
-- Generate a random polynomial with length up to the given length and
-- exponents whose packed form does not exceed the given bit count.
-- 
-- The parameter @coeff_bits@ to the three functions
-- @fmpz_mpoly_randtest_{bound|bounds|bits}@ is merely a suggestion for the
-- approximate bit count of the resulting signed coefficients. The function
-- @fmpz_mpoly_max_bits@ will give the exact bit count of the result.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_randtest_bits"
  fmpz_mpoly_randtest_bits :: Ptr CFmpzMPoly -> Ptr CFRandState -> CLong -> CMpLimb -> CMpLimb -> Ptr CFmpzMPolyCtx -> IO ()

-- Addition\/Subtraction -------------------------------------------------------

-- | /fmpz_mpoly_add_fmpz/ /A/ /B/ /c/ /ctx/ 
-- 
-- Set /A/ to \(B + c\). If /A/ and /B/ are aliased, this function will
-- probably run quickly.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_add_fmpz"
  fmpz_mpoly_add_fmpz :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpz -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_sub_fmpz/ /A/ /B/ /c/ /ctx/ 
-- 
-- Set /A/ to \(B - c\). If /A/ and /B/ are aliased, this function will
-- probably run quickly.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_sub_fmpz"
  fmpz_mpoly_sub_fmpz :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpz -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_add/ /A/ /B/ /C/ /ctx/ 
-- 
-- Set /A/ to \(B + C\). If /A/ and /B/ are aliased, this function might
-- run in time proportional to the size of \(C\).
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_add"
  fmpz_mpoly_add :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_sub/ /A/ /B/ /C/ /ctx/ 
-- 
-- Set /A/ to \(B - C\). If /A/ and /B/ are aliased, this function might
-- run in time proportional to the size of \(C\).
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_sub"
  fmpz_mpoly_sub :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO ()

-- Scalar operations -----------------------------------------------------------

-- | /fmpz_mpoly_neg/ /A/ /B/ /ctx/ 
-- 
-- Set /A/ to \(-B\).
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_neg"
  fmpz_mpoly_neg :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_scalar_mul_fmpz/ /A/ /B/ /c/ /ctx/ 
-- 
-- Set /A/ to \(B \times c\).
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_scalar_mul_fmpz"
  fmpz_mpoly_scalar_mul_fmpz :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpz -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_scalar_fmma/ /A/ /B/ /c/ /D/ /e/ /ctx/ 
-- 
-- Sets /A/ to \(B \times c + D \times e\).
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_scalar_fmma"
  fmpz_mpoly_scalar_fmma :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpz -> Ptr CFmpzMPoly -> Ptr CFmpz -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_scalar_divexact_fmpz/ /A/ /B/ /c/ /ctx/ 
-- 
-- Set /A/ to /B/ divided by /c/. The division is assumed to be exact.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_scalar_divexact_fmpz"
  fmpz_mpoly_scalar_divexact_fmpz :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpz -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_scalar_divides_fmpz/ /A/ /B/ /c/ /ctx/ 
-- 
-- If /B/ is divisible by /c/, set /A/ to the exact quotient and return
-- \(1\), otherwise set /A/ to zero and return \(0\).
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_scalar_divides_fmpz"
  fmpz_mpoly_scalar_divides_fmpz :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpz -> Ptr CFmpzMPolyCtx -> IO CInt

-- Differentiation\/Integration ------------------------------------------------

-- | /fmpz_mpoly_derivative/ /A/ /B/ /var/ /ctx/ 
-- 
-- Set /A/ to the derivative of /B/ with respect to the variable of index
-- \(var\).
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_derivative"
  fmpz_mpoly_derivative :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> CLong -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_integral/ /A/ /scale/ /B/ /var/ /ctx/ 
-- 
-- Set /A/ and /scale/ so that /A/ is an integral of \(scale \times B\)
-- with respect to the variable of index /var/, where /scale/ is positive
-- and as small as possible.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_integral"
  fmpz_mpoly_integral :: Ptr CFmpzMPoly -> Ptr CFmpz -> Ptr CFmpzMPoly -> CLong -> Ptr CFmpzMPolyCtx -> IO ()

-- Evaluation ------------------------------------------------------------------




-- | /fmpz_mpoly_evaluate_all_fmpz/ /ev/ /A/ /vals/ /ctx/ 
-- 
-- Set /ev/ to the evaluation of /A/ where the variables are replaced by
-- the corresponding elements of the array /vals/. Return \(1\) for success
-- and \(0\) for failure.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_evaluate_all_fmpz"
  fmpz_mpoly_evaluate_all_fmpz :: Ptr CFmpz -> Ptr CFmpzMPoly -> Ptr (Ptr CFmpz) -> Ptr CFmpzMPolyCtx -> IO CInt

-- | /fmpz_mpoly_evaluate_one_fmpz/ /A/ /B/ /var/ /val/ /ctx/ 
-- 
-- Set /A/ to the evaluation of /B/ where the variable of index /var/ is
-- replaced by @val@. Return \(1\) for success and \(0\) for failure.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_evaluate_one_fmpz"
  fmpz_mpoly_evaluate_one_fmpz :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> CLong -> Ptr CFmpz -> Ptr CFmpzMPolyCtx -> IO CInt

-- | /fmpz_mpoly_compose_fmpz_poly/ /A/ /B/ /C/ /ctxB/ 
-- 
-- Set /A/ to the evaluation of /B/ where the variables are replaced by the
-- corresponding elements of the array /C/. The context object of /B/ is
-- /ctxB/. Return \(1\) for success and \(0\) for failure.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_compose_fmpz_poly"
  fmpz_mpoly_compose_fmpz_poly :: Ptr CFmpzPoly -> Ptr CFmpzMPoly -> Ptr (Ptr CFmpzPoly) -> Ptr CFmpzMPolyCtx -> IO CInt

-- | /fmpz_mpoly_compose_fmpz_mpoly_geobucket/ /A/ /B/ /C/ /ctxB/ /ctxAC/ 
-- 
-- Set /A/ to the evaluation of /B/ where the variables are replaced by the
-- corresponding elements of the array /C/. Both /A/ and the elements of
-- /C/ have context object /ctxAC/, while /B/ has context object /ctxB/.
-- The length of the array /C/ is the number of variables in /ctxB/.
-- Neither /A/ nor /B/ is allowed to alias any other polynomial. Return
-- \(1\) for success and \(0\) for failure. The main method attempts to
-- perform the calculation using matrices and chooses heuristically between
-- the @geobucket@ and @horner@ methods if needed.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_compose_fmpz_mpoly_geobucket"
  fmpz_mpoly_compose_fmpz_mpoly_geobucket :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr (Ptr CFmpzMPoly) -> Ptr CFmpzMPolyCtx -> Ptr CFmpzMPolyCtx -> IO CInt

-- | /fmpz_mpoly_compose_fmpz_mpoly_gen/ /A/ /B/ /c/ /ctxB/ /ctxAC/ 
-- 
-- Set /A/ to the evaluation of /B/ where the variable of index /i/ in
-- /ctxB/ is replaced by the variable of index @c[i]@ in /ctxAC/. The
-- length of the array /C/ is the number of variables in /ctxB/. If any
-- @c[i]@ is negative, the corresponding variable of /B/ is replaced by
-- zero. Otherwise, it is expected that @c[i]@ is less than the number of
-- variables in /ctxAC/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_compose_fmpz_mpoly_gen"
  fmpz_mpoly_compose_fmpz_mpoly_gen :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CLong -> Ptr CFmpzMPolyCtx -> Ptr CFmpzMPolyCtx -> IO ()

-- Multiplication --------------------------------------------------------------

-- | /fmpz_mpoly_mul/ /A/ /B/ /C/ /ctx/ 
-- 
-- Set /A/ to \(B \times C\).
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_mul"
  fmpz_mpoly_mul :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_mul_johnson/ /A/ /B/ /C/ /ctx/ 
-- 
-- Set /A/ to \(B \times C\) using Johnson\'s heap-based method. The first
-- version always uses one thread.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_mul_johnson"
  fmpz_mpoly_mul_johnson :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_mul_array/ /A/ /B/ /C/ /ctx/ 
-- 
-- Try to set /A/ to \(B \times C\) using arrays. If the return is \(0\),
-- the operation was unsuccessful. Otherwise, it was successful and the
-- return is \(1\). The first version always uses one thread.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_mul_array"
  fmpz_mpoly_mul_array :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO CInt

-- | /fmpz_mpoly_mul_dense/ /A/ /B/ /C/ /ctx/ 
-- 
-- Try to set /A/ to \(B \times C\) using dense arithmetic. If the return
-- is \(0\), the operation was unsuccessful. Otherwise, it was successful
-- and the return is \(1\).
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_mul_dense"
  fmpz_mpoly_mul_dense :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO CInt

-- Powering --------------------------------------------------------------------




-- | /fmpz_mpoly_pow_fmpz/ /A/ /B/ /k/ /ctx/ 
-- 
-- Set /A/ to /B/ raised to the /k/-th power. Return \(1\) for success and
-- \(0\) for failure.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_pow_fmpz"
  fmpz_mpoly_pow_fmpz :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpz -> Ptr CFmpzMPolyCtx -> IO CInt

-- | /fmpz_mpoly_pow_ui/ /A/ /B/ /k/ /ctx/ 
-- 
-- Set /A/ to /B/ raised to the /k/-th power. Return \(1\) for success and
-- \(0\) for failure.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_pow_ui"
  fmpz_mpoly_pow_ui :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> CULong -> Ptr CFmpzMPolyCtx -> IO CInt

-- Division --------------------------------------------------------------------

-- | /fmpz_mpoly_divides/ /Q/ /A/ /B/ /ctx/ 
-- 
-- If /A/ is divisible by /B/, set /Q/ to the exact quotient and return
-- \(1\). Otherwise, set \(Q\) to zero and return \(0\).
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_divides"
  fmpz_mpoly_divides :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO CInt

-- | /fmpz_mpoly_divrem/ /Q/ /R/ /A/ /B/ /ctx/ 
-- 
-- Set \(Q\) and \(R\) to the quotient and remainder of /A/ divided by /B/.
-- The monomials in /R/ divisible by the leading monomial of /B/ will have
-- coefficients reduced modulo the absolute value of the leading
-- coefficient of /B/. Note that this function is not very useful if the
-- leading coefficient /B/ is not a unit.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_divrem"
  fmpz_mpoly_divrem :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_quasidivrem/ /scale/ /Q/ /R/ /A/ /B/ /ctx/ 
-- 
-- Set /scale/, /Q/ and /R/ so that /Q/ and /R/ are the quotient and
-- remainder of \(scale \times A\) divided by /B/. No monomials in /R/ will
-- be divisible by the leading monomial of /B/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_quasidivrem"
  fmpz_mpoly_quasidivrem :: Ptr CFmpz -> Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_div/ /Q/ /A/ /B/ /ctx/ 
-- 
-- Perform the operation of @fmpz_mpoly_divrem@ and discard /R/. Note that
-- this function is not very useful if the division is not exact and the
-- leading coefficient /B/ is not a unit.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_div"
  fmpz_mpoly_div :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_quasidiv/ /scale/ /Q/ /A/ /B/ /ctx/ 
-- 
-- Perform the operation of @fmpz_mpoly_quasidivrem@ and discard /R/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_quasidiv"
  fmpz_mpoly_quasidiv :: Ptr CFmpz -> Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_divrem_ideal/ /Q/ /R/ /A/ /B/ /len/ /ctx/ 
-- 
-- This function is as per @fmpz_mpoly_divrem@ except that it takes an
-- array of divisor polynomials /B/ and it returns an array of quotient
-- polynomials /Q/. The number of divisor (and hence quotient) polynomials
-- is given by /len/. Note that this function is not very useful if there
-- is no unit among the leading coefficients in the array /B/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_divrem_ideal"
  fmpz_mpoly_divrem_ideal :: Ptr (Ptr CFmpzMPoly) -> Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr (Ptr CFmpzMPoly) -> CLong -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_quasidivrem_ideal/ /scale/ /Q/ /R/ /A/ /B/ /len/ /ctx/ 
-- 
-- This function is as per @fmpz_mpoly_quasidivrem@ except that it takes an
-- array of divisor polynomials /B/ and it returns an array of quotient
-- polynomials /Q/. The number of divisor (and hence quotient) polynomials
-- is given by /len/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_quasidivrem_ideal"
  fmpz_mpoly_quasidivrem_ideal :: Ptr CFmpz -> Ptr (Ptr CFmpzMPoly) -> Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr (Ptr CFmpzMPoly) -> CLong -> Ptr CFmpzMPolyCtx -> IO ()

-- Greatest Common Divisor -----------------------------------------------------

-- | /fmpz_mpoly_term_content/ /M/ /A/ /ctx/ 
-- 
-- Set /M/ to the GCD of the terms of /A/. If /A/ is zero, /M/ will be
-- zero. Otherwise, /M/ will be a monomial with positive coefficient.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_term_content"
  fmpz_mpoly_term_content :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_content_vars/ /g/ /A/ /vars/ /vars_length/ /ctx/ 
-- 
-- Set /g/ to the GCD of the coefficients of /A/ when viewed as a
-- polynomial in the variables /vars/. Return \(1\) for success and \(0\)
-- for failure. Upon success, /g/ will be independent of the variables
-- /vars/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_content_vars"
  fmpz_mpoly_content_vars :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CLong -> CLong -> Ptr CFmpzMPolyCtx -> IO CInt

-- | /fmpz_mpoly_gcd/ /G/ /A/ /B/ /ctx/ 
-- 
-- Try to set /G/ to the GCD of /A/ and /B/ with positive leading
-- coefficient. The GCD of zero and zero is defined to be zero. If the
-- return is \(1\) the function was successful. Otherwise the return is
-- \(0\) and /G/ is left untouched.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_gcd"
  fmpz_mpoly_gcd :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO CInt

-- | /fmpz_mpoly_gcd_cofactors/ /G/ /Abar/ /Bbar/ /A/ /B/ /ctx/ 
-- 
-- Do the operation of @fmpz_mpoly_gcd@ and also compute \(Abar = A/G\) and
-- \(Bbar = B/G\) if successful.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_gcd_cofactors"
  fmpz_mpoly_gcd_cofactors :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO CInt

-- | /fmpz_mpoly_gcd_brown/ /G/ /A/ /B/ /ctx/ 
-- 
-- Try to set /G/ to the GCD of /A/ and /B/ using various algorithms.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_gcd_brown"
  fmpz_mpoly_gcd_brown :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO CInt

-- | /fmpz_mpoly_resultant/ /R/ /A/ /B/ /var/ /ctx/ 
-- 
-- Try to set /R/ to the resultant of /A/ and /B/ with respect to the
-- variable of index /var/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_resultant"
  fmpz_mpoly_resultant :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> CLong -> Ptr CFmpzMPolyCtx -> IO CInt

-- | /fmpz_mpoly_discriminant/ /D/ /A/ /var/ /ctx/ 
-- 
-- Try to set /D/ to the discriminant of /A/ with respect to the variable
-- of index /var/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_discriminant"
  fmpz_mpoly_discriminant :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> CLong -> Ptr CFmpzMPolyCtx -> IO CInt

-- | /fmpz_mpoly_primitive_part/ /res/ /f/ /ctx/ 
-- 
-- Sets /res/ to the primitive part of /f/, obtained by dividing out the
-- content of all coefficients and normalizing the leading coefficient to
-- be positive. The zero polynomial is unchanged.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_primitive_part"
  fmpz_mpoly_primitive_part :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO ()

-- Square Root -----------------------------------------------------------------

-- | /fmpz_mpoly_sqrt_heap/ /Q/ /A/ /ctx/ /check/ 
-- 
-- If /A/ is a perfect square return \(1\) and set /Q/ to the square root
-- with positive leading coefficient. Otherwise return \(0\) and set /Q/ to
-- the zero polynomial. If \(check = 0\) the polynomial is assumed to be a
-- perfect square. This can be significantly faster, but it will not detect
-- non-squares with any reliability, and in the event of being passed a
-- non-square the result is meaningless.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_sqrt_heap"
  fmpz_mpoly_sqrt_heap :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> CInt -> IO CInt

-- | /fmpz_mpoly_sqrt/ /q/ /A/ /ctx/ 
-- 
-- If /A/ is a perfect square return \(1\) and set /Q/ to the square root
-- with positive leading coefficient. Otherwise return \(0\) and set /Q/ to
-- zero.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_sqrt"
  fmpz_mpoly_sqrt :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO CInt

-- | /fmpz_mpoly_is_square/ /A/ /ctx/ 
-- 
-- Return \(1\) if /A/ is a perfect square, otherwise return \(0\).
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_is_square"
  fmpz_mpoly_is_square :: Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO CInt

-- Univariate Functions --------------------------------------------------------

-- | /fmpz_mpoly_univar_init/ /A/ /ctx/ 
-- 
-- Initialize /A/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_univar_init"
  fmpz_mpoly_univar_init :: Ptr CFmpzMPolyUnivar -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_univar_clear/ /A/ /ctx/ 
-- 
-- Clear /A/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_univar_clear"
  fmpz_mpoly_univar_clear :: Ptr CFmpzMPolyUnivar -> Ptr CFmpzMPolyCtx -> IO ()

foreign import ccall "fmpz_mpoly.h &fmpz_mpoly_univar_clear"
  p_fmpz_mpoly_univar_clear :: FunPtr (Ptr CFmpzMPolyUnivar -> Ptr CFmpzMPolyCtx -> IO ())

-- | /fmpz_mpoly_univar_swap/ /A/ /B/ /ctx/ 
-- 
-- Swap /A/ and /B/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_univar_swap"
  fmpz_mpoly_univar_swap :: Ptr CFmpzMPolyUnivar -> Ptr CFmpzMPolyUnivar -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_to_univar/ /A/ /B/ /var/ /ctx/ 
-- 
-- Set /A/ to a univariate form of /B/ by pulling out the variable of index
-- /var/. The coefficients of /A/ will still belong to the content /ctx/
-- but will not depend on the variable of index /var/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_to_univar"
  fmpz_mpoly_to_univar :: Ptr CFmpzMPolyUnivar -> Ptr CFmpzMPoly -> CLong -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_from_univar/ /A/ /B/ /var/ /ctx/ 
-- 
-- Set /A/ to the normal form of /B/ by putting in the variable of index
-- /var/. This function is undefined if the coefficients of /B/ depend on
-- the variable of index /var/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_from_univar"
  fmpz_mpoly_from_univar :: Ptr CFmpzMPoly -> Ptr CFmpzMPolyUnivar -> CLong -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_univar_degree_fits_si/ /A/ /ctx/ 
-- 
-- Return \(1\) if the degree of /A/ with respect to the main variable fits
-- an @slong@. Otherwise, return \(0\).
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_univar_degree_fits_si"
  fmpz_mpoly_univar_degree_fits_si :: Ptr CFmpzMPolyUnivar -> Ptr CFmpzMPolyCtx -> IO CInt

-- | /fmpz_mpoly_univar_length/ /A/ /ctx/ 
-- 
-- Return the number of terms in /A/ with respect to the main variable.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_univar_length"
  fmpz_mpoly_univar_length :: Ptr CFmpzMPolyUnivar -> Ptr CFmpzMPolyCtx -> IO CLong

-- | /fmpz_mpoly_univar_get_term_exp_si/ /A/ /i/ /ctx/ 
-- 
-- Return the exponent of the term of index /i/ of /A/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_univar_get_term_exp_si"
  fmpz_mpoly_univar_get_term_exp_si :: Ptr CFmpzMPolyUnivar -> CLong -> Ptr CFmpzMPolyCtx -> IO CLong

-- | /fmpz_mpoly_univar_get_term_coeff/ /c/ /A/ /i/ /ctx/ 
-- 
-- Set (resp. swap) /c/ to (resp. with) the coefficient of the term of
-- index /i/ of /A/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_univar_get_term_coeff"
  fmpz_mpoly_univar_get_term_coeff :: Ptr CFmpzMPoly -> Ptr CFmpzMPolyUnivar -> CLong -> Ptr CFmpzMPolyCtx -> IO ()

-- Internal Functions ----------------------------------------------------------

-- | /fmpz_mpoly_inflate/ /A/ /B/ /shift/ /stride/ /ctx/ 
-- 
-- Apply the function @e -> shift[v] + stride[v]*e@ to each exponent @e@
-- corresponding to the variable @v@. It is assumed that each shift and
-- stride is not negative.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_inflate"
  fmpz_mpoly_inflate :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_deflate/ /A/ /B/ /shift/ /stride/ /ctx/ 
-- 
-- Apply the function @e -> (e - shift[v])\/stride[v]@ to each exponent @e@
-- corresponding to the variable @v@. If any @stride[v]@ is zero, the
-- corresponding numerator @e - shift[v]@ is assumed to be zero, and the
-- quotient is defined as zero. This allows the function to undo the
-- operation performed by @fmpz_mpoly_inflate@ when possible.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_deflate"
  fmpz_mpoly_deflate :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_deflation/ /shift/ /stride/ /A/ /ctx/ 
-- 
-- For each variable \(v\) let \(S_v\) be the set of exponents appearing on
-- \(v\). Set @shift[v]@ to \(\operatorname{min}(S_v)\) and set @stride[v]@
-- to \(\operatorname{gcd}(S-\operatorname{min}(S_v))\). If /A/ is zero,
-- all shifts and strides are set to zero.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_deflation"
  fmpz_mpoly_deflation :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_pow_fps/ /A/ /B/ /k/ /ctx/ 
-- 
-- Set /A/ to /B/ raised to the /k/-th power, using the Monagan and Pearce
-- FPS algorithm. It is assumed that /B/ is not zero and \(k \geq 2\).
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_pow_fps"
  fmpz_mpoly_pow_fps :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> CULong -> Ptr CFmpzMPolyCtx -> IO ()

-- | /_fmpz_mpoly_divides_array/ /poly1/ /exp1/ /alloc/ /poly2/ /exp2/ /len2/ /poly3/ /exp3/ /len3/ /mults/ /num/ /bits/ 
-- 
-- Use dense array exact division to set @(poly1, exp1, alloc)@ to
-- @(poly2, exp3, len2)@ divided by @(poly3, exp3, len3)@ in @num@
-- variables, given a list of multipliers to tightly pack exponents and a
-- number of bits for the fields of the exponents of the result. The array
-- \"mults\" is a list of bases to be used in encoding the array indices
-- from the exponents. The function reallocates its output, hence the
-- double indirection, and returns the length of its output if the quotient
-- is exact, or zero if not. It is assumed that @poly2@ is not zero. No
-- aliasing is allowed.
foreign import ccall "fmpz_mpoly.h _fmpz_mpoly_divides_array"
  _fmpz_mpoly_divides_array :: Ptr (Ptr CFmpz) -> Ptr (Ptr CULong) -> Ptr CLong -> Ptr CFmpz -> Ptr CULong -> CLong -> Ptr CFmpz -> Ptr CULong -> CLong -> Ptr CLong -> CLong -> CLong -> IO CLong

-- | /fmpz_mpoly_divides_array/ /poly1/ /poly2/ /poly3/ /ctx/ 
-- 
-- Set @poly1@ to @poly2@ divided by @poly3@, using a big dense array to
-- accumulate coefficients, and return 1 if the quotient is exact.
-- Otherwise, return 0 if the quotient is not exact. If the array will be
-- larger than some internally set parameter, the function fails silently
-- and returns \(-1\) so that some other method may be called. This
-- function is most efficient on dense inputs. Note that the function
-- @fmpz_mpoly_div_monagan_pearce@ below may be much faster if the quotient
-- is known to be exact.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_divides_array"
  fmpz_mpoly_divides_array :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO CInt

-- | /_fmpz_mpoly_divides_monagan_pearce/ /poly1/ /exp1/ /alloc/ /poly2/ /exp2/ /len2/ /poly3/ /exp3/ /len3/ /bits/ /N/ 
-- 
-- Set @(poly1, exp1, alloc)@ to @(poly2, exp3, len2)@ divided by
-- @(poly3, exp3, len3)@ and return 1 if the quotient is exact. Otherwise
-- return 0. The function assumes exponent vectors that each fit in \(N\)
-- words, and are packed into fields of the given number of bits. Assumes
-- input polys are nonzero. Implements \"Polynomial division using dynamic
-- arrays, heaps and packed exponents\" by Michael Monagan and Roman
-- Pearce. No aliasing is allowed.
foreign import ccall "fmpz_mpoly.h _fmpz_mpoly_divides_monagan_pearce"
  _fmpz_mpoly_divides_monagan_pearce :: Ptr (Ptr CFmpz) -> Ptr (Ptr CULong) -> Ptr CLong -> Ptr CFmpz -> Ptr CULong -> CLong -> Ptr CFmpz -> Ptr CULong -> CLong -> CLong -> CLong -> IO CLong

foreign import ccall "fmpz_mpoly.h fmpz_mpoly_divides_monagan_pearce"
  fmpz_mpoly_divides_monagan_pearce :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO CInt

-- | /fmpz_mpoly_divides_heap_threaded/ /Q/ /A/ /B/ /ctx/ /thread_limit/ 
-- 
-- Set @poly1@ to @poly2@ divided by @poly3@ and return 1 if the quotient
-- is exact. Otherwise return 0. The function uses the algorithm of Michael
-- Monagan and Roman Pearce. Note that the function
-- @fmpz_mpoly_div_monagan_pearce@ below may be much faster if the quotient
-- is known to be exact.
-- 
-- The threaded version takes an upper limit on the number of threads to
-- use, while the first version always uses one thread.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_divides_heap_threaded"
  fmpz_mpoly_divides_heap_threaded :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> CLong -> IO CInt

-- | /_fmpz_mpoly_div_monagan_pearce/ /polyq/ /expq/ /allocq/ /poly2/ /exp2/ /len2/ /poly3/ /exp3/ /len3/ /bits/ /N/ 
-- 
-- Set @(polyq, expq, allocq)@ to the quotient of @(poly2, exp2, len2)@ by
-- @(poly3, exp3, len3)@ discarding remainder (with notional remainder
-- coefficients reduced modulo the leading coefficient of
-- @(poly3, exp3, len3)@), and return the length of the quotient. The
-- function reallocates its output, hence the double indirection. The
-- function assumes the exponent vectors all fit in \(N\) words. The
-- exponent vectors are assumed to have fields with the given number of
-- bits. Assumes input polynomials are nonzero. Implements \"Polynomial
-- division using dynamic arrays, heaps and packed exponents\" by Michael
-- Monagan and Roman Pearce. No aliasing is allowed.
foreign import ccall "fmpz_mpoly.h _fmpz_mpoly_div_monagan_pearce"
  _fmpz_mpoly_div_monagan_pearce :: Ptr (Ptr CFmpz) -> Ptr (Ptr CULong) -> Ptr CLong -> Ptr CFmpz -> Ptr CULong -> CLong -> Ptr CFmpz -> Ptr CULong -> CLong -> CLong -> CLong -> IO CLong

-- | /fmpz_mpoly_div_monagan_pearce/ /polyq/ /poly2/ /poly3/ /ctx/ 
-- 
-- Set @polyq@ to the quotient of @poly2@ by @poly3@, discarding the
-- remainder (with notional remainder coefficients reduced modulo the
-- leading coefficient of @poly3@). Implements \"Polynomial division using
-- dynamic arrays, heaps and packed exponents\" by Michael Monagan and
-- Roman Pearce. This function is exceptionally efficient if the division
-- is known to be exact.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_div_monagan_pearce"
  fmpz_mpoly_div_monagan_pearce :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO ()

-- | /_fmpz_mpoly_divrem_monagan_pearce/ /lenr/ /polyq/ /expq/ /allocq/ /polyr/ /expr/ /allocr/ /poly2/ /exp2/ /len2/ /poly3/ /exp3/ /len3/ /bits/ /N/ 
-- 
-- Set @(polyq, expq, allocq)@ and @(polyr, expr, allocr)@ to the quotient
-- and remainder of @(poly2, exp2, len2)@ by @(poly3, exp3, len3)@ (with
-- remainder coefficients reduced modulo the leading coefficient of
-- @(poly3, exp3, len3)@), and return the length of the quotient. The
-- function reallocates its outputs, hence the double indirection. The
-- function assumes the exponent vectors all fit in \(N\) words. The
-- exponent vectors are assumed to have fields with the given number of
-- bits. Assumes input polynomials are nonzero. Implements \"Polynomial
-- division using dynamic arrays, heaps and packed exponents\" by Michael
-- Monagan and Roman Pearce. No aliasing is allowed.
foreign import ccall "fmpz_mpoly.h _fmpz_mpoly_divrem_monagan_pearce"
  _fmpz_mpoly_divrem_monagan_pearce :: Ptr CLong -> Ptr (Ptr CFmpz) -> Ptr (Ptr CULong) -> Ptr CLong -> Ptr (Ptr CFmpz) -> Ptr (Ptr CULong) -> Ptr CLong -> Ptr CFmpz -> Ptr CULong -> CLong -> Ptr CFmpz -> Ptr CULong -> CLong -> CLong -> CLong -> IO CLong

-- | /fmpz_mpoly_divrem_monagan_pearce/ /q/ /r/ /poly2/ /poly3/ /ctx/ 
-- 
-- Set @polyq@ and @polyr@ to the quotient and remainder of @poly2@ divided
-- by @poly3@ (with remainder coefficients reduced modulo the leading
-- coefficient of @poly3@). Implements \"Polynomial division using dynamic
-- arrays, heaps and packed exponents\" by Michael Monagan and Roman
-- Pearce.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_divrem_monagan_pearce"
  fmpz_mpoly_divrem_monagan_pearce :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO ()

-- | /_fmpz_mpoly_divrem_array/ /lenr/ /polyq/ /expq/ /allocq/ /polyr/ /expr/ /allocr/ /poly2/ /exp2/ /len2/ /poly3/ /exp3/ /len3/ /mults/ /num/ /bits/ 
-- 
-- Use dense array division to set @(polyq, expq, allocq)@ and
-- @(polyr, expr, allocr)@ to the quotient and remainder of
-- @(poly2, exp2, len2)@ divided by @(poly3, exp3, len3)@ in @num@
-- variables, given a list of multipliers to tightly pack exponents and a
-- number of bits for the fields of the exponents of the result. The
-- function reallocates its outputs, hence the double indirection. The
-- array @mults@ is a list of bases to be used in encoding the array
-- indices from the exponents. The function returns the length of the
-- quotient. It is assumed that the input polynomials are not zero. No
-- aliasing is allowed.
foreign import ccall "fmpz_mpoly.h _fmpz_mpoly_divrem_array"
  _fmpz_mpoly_divrem_array :: Ptr CLong -> Ptr (Ptr CFmpz) -> Ptr (Ptr CULong) -> Ptr CLong -> Ptr (Ptr CFmpz) -> Ptr (Ptr CULong) -> Ptr CLong -> Ptr CFmpz -> Ptr CULong -> CLong -> Ptr CFmpz -> Ptr CULong -> CLong -> Ptr CLong -> CLong -> CLong -> IO CLong

-- | /fmpz_mpoly_divrem_array/ /q/ /r/ /poly2/ /poly3/ /ctx/ 
-- 
-- Set @polyq@ and @polyr@ to the quotient and remainder of @poly2@ divided
-- by @poly3@ (with remainder coefficients reduced modulo the leading
-- coefficient of @poly3@). The function is implemented using dense arrays,
-- and is efficient when the inputs are fairly dense. If the array will be
-- larger than some internally set parameter, the function silently returns
-- 0 so that another function can be called, otherwise it returns 1.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_divrem_array"
  fmpz_mpoly_divrem_array :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO CInt

-- | /fmpz_mpoly_quasidivrem_heap/ /scale/ /q/ /r/ /poly2/ /poly3/ /ctx/ 
-- 
-- Set @scale@, @q@ and @r@ so that @scale*poly2 = q*poly3 + r@ and no
-- monomial in @r@ is divisible by the leading monomial of @poly3@, where
-- @scale@ is positive and as small as possible. This function throws an
-- exception if @poly3@ is zero or if an exponent overflow occurs.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_quasidivrem_heap"
  fmpz_mpoly_quasidivrem_heap :: Ptr CFmpz -> Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO ()

-- | /_fmpz_mpoly_divrem_ideal_monagan_pearce/ /polyq/ /polyr/ /expr/ /allocr/ /poly2/ /exp2/ /len2/ /poly3/ /exp3/ /len/ /N/ /bits/ /ctx/ 
-- 
-- This function is as per @_fmpz_mpoly_divrem_monagan_pearce@ except that
-- it takes an array of divisor polynomials @poly3@ and an array of
-- repacked exponent arrays @exp3@, which may alias the exponent arrays of
-- @poly3@, and it returns an array of quotient polynomials @polyq@. The
-- number of divisor (and hence quotient) polynomials is given by @len@.
-- The function computes polynomials \(q_i\) such that
-- \(r = a - \sum_{i=0}^{\mbox{len - 1}} q_ib_i\), where the \(q_i\) are
-- the quotient polynomials and the \(b_i\) are the divisor polynomials.
foreign import ccall "fmpz_mpoly.h _fmpz_mpoly_divrem_ideal_monagan_pearce"
  _fmpz_mpoly_divrem_ideal_monagan_pearce :: Ptr (Ptr CFmpzMPoly) -> Ptr (Ptr CFmpz) -> Ptr (Ptr CULong) -> Ptr CLong -> Ptr CFmpz -> Ptr CULong -> CLong -> Ptr (Ptr CFmpzMPoly) -> Ptr (Ptr CULong) -> CLong -> CLong -> CLong -> Ptr CFmpzMPolyCtx -> IO CLong

-- | /fmpz_mpoly_divrem_ideal_monagan_pearce/ /q/ /r/ /poly2/ /poly3/ /len/ /ctx/ 
-- 
-- This function is as per @fmpz_mpoly_divrem_monagan_pearce@ except that
-- it takes an array of divisor polynomials @poly3@, and it returns an
-- array of quotient polynomials @q@. The number of divisor (and hence
-- quotient) polynomials is given by @len@. The function computes
-- polynomials \(q_i = q[i]\) such that @poly2@ is
-- \(r + \sum_{i=0}^{\mbox{len - 1}} q_ib_i\), where \(b_i =\) @poly3[i]@.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_divrem_ideal_monagan_pearce"
  fmpz_mpoly_divrem_ideal_monagan_pearce :: Ptr (Ptr CFmpzMPoly) -> Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr (Ptr CFmpzMPoly) -> CLong -> Ptr CFmpzMPolyCtx -> IO ()

-- Vectors ---------------------------------------------------------------------

-- | /fmpz_mpoly_vec_init/ /vec/ /len/ /ctx/ 
-- 
-- Initializes /vec/ to a vector of length /len/, setting all entries to
-- the zero polynomial.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_vec_init"
  fmpz_mpoly_vec_init :: Ptr CFmpzMPolyVec -> CLong -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_vec_clear/ /vec/ /ctx/ 
-- 
-- Clears /vec/, freeing its allocated memory.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_vec_clear"
  fmpz_mpoly_vec_clear :: Ptr CFmpzMPolyVec -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_vec_print/ /vec/ /ctx/ 
-- 
-- Prints /vec/ to standard output.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_vec_print"
  fmpz_mpoly_vec_print :: Ptr CFmpzMPolyVec -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_vec_swap/ /x/ /y/ /ctx/ 
-- 
-- Swaps /x/ and /y/ efficiently.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_vec_swap"
  fmpz_mpoly_vec_swap :: Ptr CFmpzMPolyVec -> Ptr CFmpzMPolyVec -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_vec_fit_length/ /vec/ /len/ /ctx/ 
-- 
-- Allocates room for /len/ entries in /vec/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_vec_fit_length"
  fmpz_mpoly_vec_fit_length :: Ptr CFmpzMPolyVec -> CLong -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_vec_set/ /dest/ /src/ /ctx/ 
-- 
-- Sets /dest/ to a copy of /src/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_vec_set"
  fmpz_mpoly_vec_set :: Ptr CFmpzMPolyVec -> Ptr CFmpzMPolyVec -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_vec_append/ /vec/ /f/ /ctx/ 
-- 
-- Appends /f/ to the end of /vec/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_vec_append"
  fmpz_mpoly_vec_append :: Ptr CFmpzMPolyVec -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_vec_insert_unique/ /vec/ /f/ /ctx/ 
-- 
-- Inserts /f/ without duplication into /vec/ and returns its index. If
-- this polynomial already exists, /vec/ is unchanged. If this polynomial
-- does not exist in /vec/, it is appended.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_vec_insert_unique"
  fmpz_mpoly_vec_insert_unique :: Ptr CFmpzMPolyVec -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO CLong

-- | /fmpz_mpoly_vec_set_length/ /vec/ /len/ /ctx/ 
-- 
-- Sets the length of /vec/ to /len/, truncating or zero-extending as
-- needed.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_vec_set_length"
  fmpz_mpoly_vec_set_length :: Ptr CFmpzMPolyVec -> CLong -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_vec_randtest_not_zero/ /vec/ /state/ /len/ /poly_len/ /bits/ /exp_bound/ /ctx/ 
-- 
-- Sets /vec/ to a random vector with exactly /len/ entries, all nonzero,
-- with random parameters defined by /poly_len/, /bits/ and /exp_bound/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_vec_randtest_not_zero"
  fmpz_mpoly_vec_randtest_not_zero :: Ptr CFmpzMPolyVec -> Ptr CFRandState -> CLong -> CLong -> CLong -> CULong -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_vec_set_primitive_unique/ /res/ /src/ /ctx/ 
-- 
-- Sets /res/ to a vector containing all polynomials in /src/ reduced to
-- their primitive parts, without duplication. The zero polynomial is
-- skipped if present. The output order is arbitrary.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_vec_set_primitive_unique"
  fmpz_mpoly_vec_set_primitive_unique :: Ptr CFmpzMPolyVec -> Ptr CFmpzMPolyVec -> Ptr CFmpzMPolyCtx -> IO ()

-- Ideals and Gröbner bases ----------------------------------------------------

-- The following methods deal with ideals in
-- \(\mathbb{Q}[X_1,\ldots,X_n]\). We use primitive integer polynomials as
-- normalised generators in place of monic rational polynomials.
--
-- | /fmpz_mpoly_spoly/ /res/ /f/ /g/ /ctx/ 
-- 
-- Sets /res/ to the /S/-polynomial of /f/ and /g/, scaled to an integer
-- polynomial by computing the LCM of the leading coefficients.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_spoly"
  fmpz_mpoly_spoly :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_reduction_primitive_part/ /res/ /f/ /vec/ /ctx/ 
-- 
-- Sets /res/ to the primitive part of the reduction (remainder of
-- multivariate quasidivision with remainder) with respect to the
-- polynomials /vec/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_reduction_primitive_part"
  fmpz_mpoly_reduction_primitive_part :: Ptr CFmpzMPoly -> Ptr CFmpzMPoly -> Ptr CFmpzMPolyVec -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_vec_is_groebner/ /G/ /F/ /ctx/ 
-- 
-- If /F/ is /NULL/, checks if /G/ is a Gröbner basis. If /F/ is not
-- /NULL/, checks if /G/ is a Gröbner basis for /F/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_vec_is_groebner"
  fmpz_mpoly_vec_is_groebner :: Ptr CFmpzMPolyVec -> Ptr CFmpzMPolyVec -> Ptr CFmpzMPolyCtx -> IO CInt

-- | /fmpz_mpoly_vec_is_autoreduced/ /F/ /ctx/ 
-- 
-- Checks whether the vector /F/ is autoreduced (or inter-reduced).
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_vec_is_autoreduced"
  fmpz_mpoly_vec_is_autoreduced :: Ptr CFmpzMPolyVec -> Ptr CFmpzMPolyCtx -> IO CInt

-- | /fmpz_mpoly_vec_autoreduction/ /H/ /F/ /ctx/ 
-- 
-- Sets /H/ to the autoreduction (inter-reduction) of /F/.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_vec_autoreduction"
  fmpz_mpoly_vec_autoreduction :: Ptr CFmpzMPolyVec -> Ptr CFmpzMPolyVec -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_vec_autoreduction_groebner/ /H/ /G/ /ctx/ 
-- 
-- Sets /H/ to the autoreduction (inter-reduction) of /G/. Assumes that /G/
-- is a Gröbner basis. This produces a reduced Gröbner basis, which is
-- unique (up to the sort order of the entries in the vector).
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_vec_autoreduction_groebner"
  fmpz_mpoly_vec_autoreduction_groebner :: Ptr CFmpzMPolyVec -> Ptr CFmpzMPolyVec -> Ptr CFmpzMPolyCtx -> IO ()

-- -- | /fmpz_mpoly_select_pop_pair/ /pairs/ /G/ /ctx/ 
-- -- 
-- -- Given a vector /pairs/ of indices \((i, j)\) into /G/, selects one pair
-- -- for elimination in Buchberger\'s algorithm. The pair is removed from
-- -- /pairs/ and returned.
-- foreign import ccall "fmpz_mpoly.h fmpz_mpoly_select_pop_pair"
--   fmpz_mpoly_select_pop_pair :: Ptr CPairs -> Ptr CFmpzMPolyVec -> Ptr CFmpzMPolyCtx -> IO (Ptr CPair)

-- | /fmpz_mpoly_buchberger_naive/ /G/ /F/ /ctx/ 
-- 
-- Sets /G/ to a Gröbner basis for /F/, computed using a naive
-- implementation of Buchberger\'s algorithm.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_buchberger_naive"
  fmpz_mpoly_buchberger_naive :: Ptr CFmpzMPolyVec -> Ptr CFmpzMPolyVec -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_buchberger_naive_with_limits/ /G/ /F/ /ideal_len_limit/ /poly_len_limit/ /poly_bits_limit/ /ctx/ 
-- 
-- As @fmpz_mpoly_buchberger_naive@, but halts if during the execution of
-- Buchberger\'s algorithm the length of the ideal basis set exceeds
-- /ideal_len_limit/, the length of any polynomial exceeds
-- /poly_len_limit/, or the size of the coefficients of any polynomial
-- exceeds /poly_bits_limit/. Returns 1 for success and 0 for failure. On
-- failure, /G/ is a valid basis for /F/ but it might not be a Gröbner
-- basis.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_buchberger_naive_with_limits"
  fmpz_mpoly_buchberger_naive_with_limits :: Ptr CFmpzMPolyVec -> Ptr CFmpzMPolyVec -> CLong -> CLong -> CLong -> Ptr CFmpzMPolyCtx -> IO CInt

-- Special polynomials ---------------------------------------------------------

foreign import ccall "fmpz_mpoly.h fmpz_mpoly_symmetric_gens"
  fmpz_mpoly_symmetric_gens :: Ptr CFmpzMPoly -> CULong -> Ptr CLong -> CLong -> Ptr CFmpzMPolyCtx -> IO ()

-- | /fmpz_mpoly_symmetric/ /res/ /k/ /ctx/ 
-- 
-- Sets /res/ to the elementary symmetric polynomial
-- \(e_k(X_1,\ldots,X_n)\).
-- 
-- The /gens/ version takes \(X_1,\ldots,X_n\) to be the subset of
-- generators given by /vars/ and /n/. The indices in /vars/ start from
-- zero. Currently, the indices in /vars/ must be distinct.
foreign import ccall "fmpz_mpoly.h fmpz_mpoly_symmetric"
  fmpz_mpoly_symmetric :: Ptr CFmpzMPoly -> CULong -> Ptr CFmpzMPolyCtx -> IO ()

